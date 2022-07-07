#!/usr/bin/python3
import z3
import struct
import sys


""" 
Solving for seed states in XorShift128+ used in V8
> https://v8.dev/blog/math-random
> https://apechkurov.medium.com/v8-deep-dives-random-thoughts-on-math-random-fb155075e9e5
> https://blog.securityevaluators.com/hacking-the-javascript-lottery-80cc437e3b7f

> Tested on Chrome(102.0.5005.61) or Nodejs(v18.2.0.) 
"""

"""
Plug in a handful random number sequences from node/chrome
> Array.from(Array(5), Math.random)

(Optional) In node, we can specify the seed
> node --random_seed=1337
"""
sequence = [
  0.9311600617849973,
  0.3551442693830502,
  0.7923158995678377,
  0.787777942408997,
  0.376372264303491,
  # 0.23137147109312428
]

"""
Random numbers generated from xorshift128+ is used to fill an internal entropy pool of size 64
> https://github.com/v8/v8/blob/7a4a6cc6a85650ee91344d0dbd2c53a8fa8dce04/src/numbers/math-random.cc#L35

Numbers are popped out in LIFO(Last-In First-Out) manner, hence the numbers presented from the entropy pool are reveresed.
"""
sequence = sequence[::-1]

solver = z3.Solver()

"""
Create 64 bit states, BitVec (uint64_t)
> static inline void XorShift128(uint64_t* state0, uint64_t* state1);
> https://github.com/v8/v8/blob/a9f802859bc31e57037b7c293ce8008542ca03d8/src/base/utils/random-number-generator.h#L119
"""
se_state0, se_state1 = z3.BitVecs("se_state0 se_state1", 64)

for i in range(len(sequence)):
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
    se_s1 = se_state0
    se_s0 = se_state1
    se_state0 = se_s0
    se_s1 ^= se_s1 << 23
    se_s1 ^= z3.LShR(se_s1, 17)  # Logical shift instead of Arthmetric shift
    se_s1 ^= se_s0
    se_s1 ^= z3.LShR(se_s0, 26)
    se_state1 = se_s1

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
    float_64 = struct.pack("d", sequence[i] + 1)
    u_long_long_64 = struct.unpack("<Q", float_64)[0]

    """
    # visualize sign, exponent & mantissa
    bits = bin(u_long_long_64)[2:]
    bits = '0' * (64-len(bits)) + bits
    print(f'{bits[0]} {bits[1:12]} {bits[12:]}')
    """

    # Get the lower 52 bits (mantissa)
    mantissa = u_long_long_64 & ((1 << 52) - 1)

    # Compare Mantissas
    solver.add(int(mantissa) == z3.LShR(se_state0, 12))


if solver.check() == z3.sat:
    model = solver.model()

    states = {}
    for state in model.decls():
        states[state.__str__()] = model[state]

    print(states)

    state0 = states["se_state0"].as_long()

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

    print(next_sequence)
