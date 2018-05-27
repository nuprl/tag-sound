v0.12
===

Notes on the performance of Tagged Racket v0.12.

TODO
- [ ] keep investigating morsecode, seems there is MORE to the gap


tetris
---

- Fully typed configuration is faster than others.
  Is this a bug? NO
- Cannot run fully-typed with my current TR.
  Why not? IDK SEEMS FIXED

The speedup is NOT a bug,
 I forgot that I'd implemented a "trust codomain of any Tagged Racket function".
Turns out to be extremely important for performance.


gregor
---

- Fully-typed is faster than others. Bug?
  - typed ~ 1000ms
  - slow ones (~ 1200ms each)
    okay the slowdown is really not that much so dont go crazy about this
    also, only have 2 gregor iterations
  ```
    0101000101111  -- cannot reproduce
    0101111010101  -- cannot reproduce
    0111101101011  -- cannot reproduce
    0111101111101  -- YES
    1101101011011  -- YES
    1111001011001  -- cannot reproduce
    0101101101101  -- cannot reproduce
    0111111011101  -- cannot reproduce
  ```
- IDEA: maybe its slower because of the adaptor,
        indirection because of that.
        but not a big deal don't worry about this

NO there is great reason for more types = faster, removes codomain checks.


morsecode
---

- Some configs are _much_ slower on TAG than 6.10.1
  ```
    config | 6.10.1 | tag
    -------|--------|-----
    0010   |    984 | 1062
    0011   |    688 | 1033
    0111   |    704 |  968
    1000   |    830 | 1694
    1001   |   1179 | 1704
    1010   |   1062 | 1902
    1011   |    745 | 1927
    1100   |    860 | 1766
    1101   |   1235 | 1711
    1110   |   1030 | 1889
    1111   |    714 | 1873
  ```
- Most of these have Levenshtein tagged.
  How much slower is untyped, with similar checks?
  - 150ms slower, with manual checks and using racket/contract for `or/c`
    not much!

- Some configs are much faster on TAG than 6.10.1
  ```
    config | 6.10.1 | tag
    -------|--------|----
    0100   |    830 | 747
    0101   |   1167 | 720
    0110   |   1015 | 951
  ```
  Nothing remarkable
