micro-racket
===

Model of Typed Racket,
 showing difference between type soundness and tag soundness semantics.

Outline:
- one source language, looks like Typed Racket
- three semantics,
  * type sound
  * tag sound
  * unsound
proofs of type and tag soundness

TODO
- count runtime time checks ?
- be careful! don't mix typing with evaluation
- stop using "typed modules" list, make module names have (id typed?)
- allow mutually recursive defines

Summary
---

- `lang.rkt` language definition
- `util.rkt` debugging helpers
- `metafunctions.rkt` helpers
- `grammar.rkt` well-formed program, type, expression etc.
- `typecheck.rkt` static type checking
- `eval-typed.rkt` Typed Racket evaluation, with monitors. Type-sound.
- `eval-tagged.rkt` Tagged Racket evaluation. Tag-sound.
- `eval-untyped.rkt` type-erased evaluation. TST-sound.


Notes
---

All module paths are relative strings,
 to make it easy to build the model without building the paper.


