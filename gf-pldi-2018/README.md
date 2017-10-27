paper
===

"Spectrum of soundness"

TODO
---

- type soundness isn't the only reason for type systems, see:
  - typescript
  - java
  - pluggable types
  - "any lnaguage without a proof (ocaml haskell TR)"
- why reason ... still not sure, have some ideas, call for user studies


Intro
---

@; Based on conversation with Matthias

Soundness costs time and money.
JFP shows for Typed Racket.
DLS shows for Reticulated.
POPL (Vitousek) shows there's a spectrum of soundness,
 from Typed Racket's
 to Reticulated's
 to who knows what else.
We implement a few sister languages to Racket,
 (variations of Typed Racket),
 and compare the guarantees and performance.

Later, integration with Typed Racket.
Also discussion of the hazards and pitfalls,
 tldr why you should use Typed Racket and work to improve its performance.


Intro II
---

0. Typed Racket
  - generalized soundness
  - zero types = racket
  - 100% types = normal typed language, with optimizations
1. the cost is high
  - cite Takikawa
  - comes from allocation, indirection, checking
2. one idea, improve Typed Racket
  - same guarantees, better implementation
  - soft contracts, space-efficient contracts, soft typing, general tuning
3. Vitousek etal have nuclear option
  - type-based rewriting
  - tag soundness
  - little-to-no-blame
  - fully typed ~ worst performance (basically, linear increase)
  - much better performance!!! cite Zeina
4. Research Question
  - what is performance, if we skip on type safety and blame?
  - constraint 1 : untyped = Racket
  - constraint 2 : typed = Typed Racket, with optimizations

NOTE: first introduce tag soundness (reasonable soundness)
      second, introduce "drop monitors" as principled implementation


Typed Racket
---

@; section 2

Typed Racket, described in SNAPL.
Soundness is similar to conventional:
  if `\vdash e : \tau` then either
  - `e -->* v` and `\vdash v : \tau`
  - `e -->\infty`
  - `e -->* BoundaryError b`
    where `b` is specific boundary from `R` into `T`
    (could be derived boundary, R-input to a T function)
  - `e -->* RuntimeError` (from T or R interacting with runtime functions)

EXPLAIN WITH COLORS,
 colors for the boundaries
 - lambda (keep color)
 - vector (keep color)
 - list (flip color)

Tagged Racket
---

Enforce tag-level soundness.
Every runtime check is either a tag-check or delayed.

Similar to TR soundness, but weaker.
Only does "top level" of types.
  if `\vdash e : TAG(\tau)` then either
  - `e -->* v` and `\vdash v : TAG(\tau)`
  - `e -->\infty`
  - `e -->* BoundaryError b`
    where `b` is specific boundary from `R` into `S`
    (could be derived boundary, R-input to a S function)
  - `e -->* RuntimeError` (from S or R interacting with runtime functions)

Implemented using monitors (chaperones, contracts).


Transient Racket
---

Tag-level soundness, no chaperones.
Use type-based rewriting.
No allocation at runtime, but lose blame.

  if `\vdash e : TAG(\tau)` then either
  - `e -->* v` and `\vdash v : TAG(\tau)`
  - `e -->\infty`
  - `e -->* BoundaryError b*`
    where `b*` is a SET of boundaries that might pinpoint the bad cast
    (can guarantee?)
  - `e -->* RuntimeError` (from S or R interacting with runtime functions)


Other Soundness
---

0. nothing
1. O(1) checks
2. flat types
3. all types

#### \kappa-based dynamic typing
- transient (as I'm thinking about it) is O(1) at every input to typed code
- but dynamic typing is lazier, checks every use, so `z + z` is 2 checks
- every variable reference is nowa tag check, okay
- easy to implement? anyway wait until later. Then maybe, Henglein to reduce

#### Retic confuses "my transient" and "\kappa-based"

Checks:
- input of +
- derefs

Should not need to check both ... if you check every deref & every application,
 no need to check inputs to + in typed code ... typed code can assume tag-safety,
 which is all that + needs.



Tradeoffs
---

Guard all channels ==> optimize

Label all values \/ Eager checks (for unlabeled) ==> blame


References
---

Vitouseks
Levity Polymorphism
Concrete Types
