#lang gf-pldi-2018
@title[#:tag "sec:conclusion"]{Why Types?}

@; Future work:
@; - static/dynamic analysis to attribute run-time cost to boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - static analysis, to pick natural vs. co-natural for a boundary (for efficiency)
@; - JIT for tagged, other things to reduce tag checks

@; -----------------------------------------------------------------------------

There seems to be general agreement that type systems are useful,
 and general disagreement about what type systems are useful for.
Types get used for proving theorems, reasoning about semantics,
 static analysis, efficient compilation, and checked documentation.
Even C and Python programmers use types to specify their programs
 get something from their toolchain (faster code, IDE auto-completion).

In migratory type systems, changing the intended purpose of types can
 have significant performance implications.
Perhaps in addition to designing a type system to accomodate the idioms
 of dynamically-typed programs, a migratory typing system ought to tailor
 its type soundness.


@acks{
  @; redex-check
  @; NSF funding
  @; early feedback at PI meeting
}
