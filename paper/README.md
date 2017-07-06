paper
===

"Spectrum of soundness"


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
