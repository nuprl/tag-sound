little-model
===

Series of simple PLT Redex models to describe the key ideas of type-tag soundness.


#### High-level outline

1. (no gradual typing)
   Introduce a dynamically-typed language (D) and a statically-typed counterpart (S)
2. (syntax for gradual typing)
   Add syntax for embedding D-terms within S-terms, and S-terms within D-terms
3. (simple mixing)
   Explain & compare _the natural embedding_ vs. _the erasure embedding_.
   Note the performance problem, and where the overhead comes from.
4. (trade for performance)
   Systematically increase performance by making run-time type checks lazy,
    "flat", and finally tagged


### Outline

Every `little-*.rkt` file contains a PLT Redex model.
Some models depend on others.

- `little-dyn.rkt` dynamically typed language, term safety theorem
- `little-sta.rkt` statically typed language, type safety theorem
- `little-mixed.rkt` combined language "well-formed" rules
- `little-erased.rkt` type-erased embedding
- `little-natural.rkt` natural (type-directed) embedding
- `little-lazy.rkt` lazy natural embedding
- `little-forgetful.rkt` lazy forgetful natural embedding
- `little-tagged.rkt` monitor-free lazy-forgetful natural embedding


#### Diagram of dependencies

If `A` and `B` are module names, here's how to read the diagram:

- a line from `A` **down to** `B` means that `B` imports things from `A`
- if `A` is above `B`, then `A` comes "conceptually before" `B` in the outline,
  at least for my conception of things

```

     little-dyn   little-sta
           \      /
            \    /
          little-mixed
          /      | | \
  little-natural | |  little-erased
                 | |
                 | little-lazy
                 | |
                 | little-forgetful
                 |
                 little-tagged
```
