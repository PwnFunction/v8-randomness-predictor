#!/usr/bin/env python3
import os
import z3
import struct
import argparse
from tabulate import tabulate
from rich import print
from shutil import which
from rich.console import Console

# Some default values incase you want to test your code
SEQUENCE = [
    0.9311600617849973,
    0.3551442693830502,
    0.7923158995678377,
    0.787777942408997,
    0.376372264303491,
    # 0.23137147109312428
]

def double_to_long_long(val):
    """
    IEEE 754 double-precision binary floating-point format
    > https://en.wikipedia.org/wiki/Double-precision_floating-point_format
    > https://www.youtube.com/watch?v=p8u_k2LIZyo&t=257s

    Sign (1)    Exponent (11)    Mantissa (52)
    [#]         [###########]    [####################################################]
    """

    """
    Pack as `double` and re-interpret as unsigned `long long` (little endian)
    > https://stackoverflow.com/a/65377273
    """
    float_64 = struct.pack("d", val)
    u_long_long_64 = struct.unpack("<Q", float_64)[0]
    return u_long_long_64


"""
Solving for seed states in XorShift128+ used in V8
> https://v8.dev/blog/math-random
> https://apechkurov.medium.com/v8-deep-dives-random-thoughts-on-math-random-fb155075e9e5
> https://blog.securityevaluators.com/hacking-the-javascript-lottery-80cc437e3b7f

> Tested on Chrome(102.0.5005.61) or Nodejs(v18.2.0.) 
"""
class Cracker:
    """Class To Calculate the next 'Random' number"""

    def __init__(self, sequence):
        # Number of v8 generated values
        self.iteration = len(sequence)

        if self.iteration < 2:
            raise ValueError("Atleast Need 2 Values to compute")

        # List of states
        self.states = {}

        # Denotes if the problem is solvable
        self.sol_state = False

        """
        Random numbers generated from xorshift128+ is used to fill an internal entropy pool of size 64
        > https://github.com/v8/v8/blob/7a4a6cc6a85650ee91344d0dbd2c53a8fa8dce04/src/numbers/math-random.cc#L35

        Numbers are popped out in LIFO(Last-In First-Out) manner, hence the numbers presented from the entropy pool are reverese
        d.
        """
        self.sequence = sequence[::-1]    

        # z3 solver object
        self.solver = z3.Solver()

        """
        Create 64 bit states, BitVec (uint64_t)
        > static inline void XorShift128(uint64_t* state0, uint64_t* state1);
        > https://github.com/v8/v8/blob/a9f802859bc31e57037b7c293ce8008542ca03d8/src/base/utils/random-number-generator.h#L119
        """
        self.state0, self.state1 = z3.BitVecs("state0 state1", 64)

    def get_seeds(self):
        """
        Random numbers generated from xorshift128+ is used to fill an internal entropy pool of size 64
        > https://github.com/v8/v8/blob/7a4a6cc6a85650ee91344d0dbd2c53a8fa8dce04/src/numbers/math-random.cc#L35
        
        Numbers are popped out in LIFO(Last-In First-Out) manner, hence the numbers presented from the entropy pool are reveresed.
        """

        cmd = 'node -e "console.log(Math.random())"'
        if which("node") is not None:
            for _i in range(self.iteration):
                self.sequence.append(
                    float(os.popen(cmd).read())
                )
        self.sequence = SEQUENCE
        self.sequence = self.sequence[::-1]    
        return (len(self.sequence) != 0)

    def xorshift128plus(self):
        """
        XorShift128+
        > https://vigna.di.unimi.it/ftp/papers/xorshiftplus.pdf
        > https://github.com/v8/v8/blob/a9f802859bc31e57037b7c293ce8008542ca03d8/src/base/utils/random-number-generator.h#L119

        class V8_BASE_EXPORT RandomNumberGenerator final {
            ...
            static inline void XorShift128(uint64_t* state0, uint64_t* state1) {
                uint64_t s1 = *state0;
                uint64_t s0 = *state1;
                *state0 = s0;
                s1 ^= s1 << 23;
                s1 ^= s1 >> 17;
                s1 ^= s0;
                s1 ^= s0 >> 26;
                *state1 = s1;
            }
            ...
        }
        """

        s1 = self.state0
        s0 = self.state1
        self.state0 = s0
        s1 ^= s1 << 23
        s1 ^= z3.LShR(s1, 17)  # Logical shift instead of Arthmetric shift
        s1 ^= s0
        s1 ^= z3.LShR(s0, 26)
        self.state1 = s1

    def solve(self):
        solver = self.solver
        for i in range(self.iteration):
            self.xorshift128plus()

            u_long_long_64 = double_to_long_long(self.sequence[i] + 1)

            """
            # visualize sign, exponent & mantissa
            bits = bin(u_long_long_64)[2:]
            bits = '0' * (64-len(bits)) + bits
            print(f'{bits[0]} {bits[1:12]} {bits[12:]}')
            """
        
            # Get the lower 52 bits (mantissa)
            mantissa = u_long_long_64 & ((1 << 52) - 1)
        
            # Compare Mantissas
            solver.add(int(mantissa) == z3.LShR(self.state0, 12))
        
        
        if solver.check() == z3.sat:
            model = solver.model()
        
            for state in model.decls():
                self.states[state.__str__()] = model[state]
        
            state0 = self.states["state0"].as_long()
        
            """
            Extract mantissa
            - Add `1.0` (+ 0x3FF0000000000000) to 52 bits
            - Get the double and Subtract `1` to obtain the random number between [0, 1)
        
            > https://github.com/v8/v8/blob/a9f802859bc31e57037b7c293ce8008542ca03d8/src/base/utils/random-number-generator.h#L111
        
            static inline double ToDouble(uint64_t state0) {
                // Exponent for double values for [1.0 .. 2.0)
                static const uint64_t kExponentBits = uint64_t{0x3FF0000000000000};
                uint64_t random = (state0 >> 12) | kExponentBits;
                return base::bit_cast<double>(random) - 1;
            }
            """
            u_long_long_64 = (state0 >> 12) | 0x3FF0000000000000
            float_64 = struct.pack("<Q", u_long_long_64)
            next_sequence = struct.unpack("d", float_64)[0]
            next_sequence -= 1
            self.sequence = self.sequence[::-1]
            self.sequence.append(next_sequence)
            self.iteration = self.iteration + 1
            self.sequence = self.sequence[::-1]
            return next_sequence
        
        return None


def main():
    print(":man_technologist:", "[bold][green]Break that v8 Math.random()![/green]")
    _flag = False
    parser = argparse.ArgumentParser(description="[+] Break that v8 Math.random()!")
    parser.add_argument('-s', '--seeds', 
                        help="Comma separated list of number obtained from subsequent Math.random() functions")
    args = parser.parse_args()

    if args.seeds is None:
        global SEQUENCE
    
    else:
        SEQUENCE = []
        for x in args.seeds.split(','):
            if x != '':
                try:
                    SEQUENCE.append(float(x))
                except ValueError:
                    print(":x:", "Invalid Input!")
                    __import__('sys').exit()

    # Create a cracker object
    cracker = Cracker(SEQUENCE)

    print(":seedling:", f"[bold][yellow]  Using {cracker.iteration} seeds[/yellow]")
    for x in cracker.sequence:
        print(":point_right:", f"  {x}")

    soln = cracker.solve()
    if soln is not None:
        print(":rocket:", f"[bold magenta]  Next Random Number: [green]{soln}[/green] [b/old magenta]")
        print(":floppy_disk:", "[bold]  State Values:[/bold]")
        print(tabulate([["state", "value"], ["state0", cracker.states["state0"]], ["state1", cracker.states["state1"]]], headers="firstrow", tablefmt="pretty"))
    else:
        print(":x:", "[bold red]  No Solution Found![/bold red]")
    
if __name__ == '__main__':
    main()
