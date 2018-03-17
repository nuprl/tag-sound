Models for _The Spectrum of Soundness and Performance_
===

Series of simple PLT Redex models.

("Type tags" here are called "type constructors" in the paper.)


#### High-level outline

1. (no gradual typing)
   Introduce a dynamically-typed language (D) and a statically-typed counterpart (S)
2. (syntax for gradual typing)
   Add syntax for embedding D-terms within S-terms, and S-terms within D-terms
3. (simple mixing)
   Explain & compare _the natural embedding_ vs. _the erasure embedding_.
   Note the performance problem, and where the overhead comes from.
4. (trade for performance)
   Systematically increase performance by making run-time type checks "lazy",
    "flat", and finally tagged


### Outline

Most `*.rkt` files contains a PLT Redex model.

1. `dyn.rkt` dynamically typed language, term safety theorem
2. `sta.rkt` statically typed language, type safety theorem
3. `mixed.rkt` combined language "well-formed" rules
4. `erased.rkt` type-erased embedding
5. `natural.rkt` natural (type-directed) embedding
6. `conatural.rkt` co-natural embedding
7. `forgetful.rkt` forgetful final embedding
8. `tagged.rkt` monitor-free lazy-forgetful natural embedding

Other files:

- `redex-helpers.rkt` generic helper functions, mostly for testing


#### Diagram of dependencies

HOW TO READ, assuming `A` and `B` are module names:

- a line from `A` **down to** `B` means that `B` imports things from `A`
- if `A` is above `B`, then `A` comes "conceptually before" `B` in the outline,
  at least for my conception of things

```
     dyn   sta
      \     /
       \   /
       mixed
     /   | | \
 natural | |  erased
         | |
         | conatural
         | |
         | forgetful
         |
         tagged
```
