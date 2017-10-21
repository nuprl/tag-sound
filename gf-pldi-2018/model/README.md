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
- stop using `untyped-context`, stop using `L` tag,
  - make Et and Eu frames, a frame is 1 level of evaluation context
  - E ::= (Et | Eu) *
  - reduction matches E[Et[e]] E[Eu[e]]
- maybe have surface & core languages,
  because they really are different,
  source doesn't allow monitors


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


