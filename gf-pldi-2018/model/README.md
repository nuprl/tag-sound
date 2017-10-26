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
- CURRENT STATUS
  * go back, clean up language, revise aux files AGAIN --- do this quickly
  * with revisions, 2 soundnesses are 2 ways of interpreting boundaries
  * actually possible (easy) to prove no type errors in tagged code --- because
    now the runtime knows what is tagged code instead of being hopelessly jumbled


Summary
---

- `lang.rkt` language definition
- `util.rkt` debugging helpers
- `metafunctions.rkt` helpers
- `grammar.rkt` well-formed program, type, expression etc.
- `typecheck.rkt` static type checking
- `eval-common.rkt` helpers for evaluation
- `eval-typed.rkt` Typed Racket evaluation, with monitors. Type-sound.
- `eval-tagged.rkt` Tagged Racket evaluation. Tag-sound.
- `eval-untyped.rkt` type-erased evaluation. TST-sound.
- `sound-typed.rkt` Typed Racket evaluation, with monitors. Type-sound.
- `sound-tagged.rkt` Tagged Racket evaluation. Tag-sound.
- `sound-untyped.rkt` type-erased evaluation. TST-sound.


Notes
---

All module paths are relative strings,
 to make it easy to build the model without building the paper.


