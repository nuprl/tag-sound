model
===

Model of:
- Racket
- Tag-Sound Typed Racket (shallow)
- Typed Racket

Everything is in `model.rkt`

- - -

Update 2017-07-06
---

- not everything is in `model.rkt`
- basic "provably sound" model in `stlc.rkt`
- three other files, just starting out:
  - `typed-racket.rkt`
  - `shallow-racket.rkt`
  - `transient-racket.rkt`
- possible to combine the similar parts of those files?


- - -

Update 2017-07-20
---

STOP  ... need to say, what are key points for Matthias?
- [X] soundness statements
  - UNCLEAR typed raises more boundary errors
  - UNCLEAR typed catches first violation
  - UNCLEAR retic catches last violation
- [ ] interesting programs, litmus tests
- [X] plan for what's next / in-paper
  1. define dynamically typed language
    - gets stuck, add completions, no longer stuck
    - show progress + preservation at TST
  2. gradual typing I
    - add higher-order contracts to evaluator
    - add static typed "sublanguage", with eval rules (just for the proofs)
    - show type soundness at \tau, despite interaction with R
  3. gradual typing II
    - add static typed "sublanguage"
    - type-based rewriting, new dyn checks
    - type soundness at \floor{\tau} despite R
  4. comparison between gradual typings
    - different types
    - different blame
    - different performance in theory
    - 2 implementations, different in practice
  5. interop

Narrative:

- start with untyped language, with runtime, gets stuck
- add completions, dynamically typed safe
- add sister language T, static type system, monitors at boundaries
- type soundness (boundary error)

