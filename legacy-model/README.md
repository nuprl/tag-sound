model
===

Note from Matthias:

> Two thoughts on the theoretical underpinnings; please contemplate while away: 
>
> 1. The type system of our model for Transient GTLC must include ONE type that
> shows that Raw GTLC (rip types out) does NOT preserve a subject reduction
> theorem. That is, there are places where the typed-predicted value of an
> expression does NOT include the actual value (say, natural : type vs -5 :
> actual). That way we can claim that Transient is a first confirmed point
> between Sound and NOT Sound.
>
> 2. Ideally we should have something like this for Generalized GTLC vs
> Transient GTLC. I think in a sense Transient fails like Raw BUT catches all
> abuses IF an observation takes place.
>
> Literature: please read introduction to Cartwright’s Constructive Data Type
> Definitions. It discusses final vs initial algebraic semantics best. You may
> also wish to read Felleisen-Wand ’88 from that perspective (skip all details
> about continuations).
>
> Title: Soundness is Not Binary. Or: Between Soundness and Unsoundness and
> What It Means for Performance.



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

