#lang gf-icfp-2018
@title[#:tag "sec:conclusion"]{Finding Balance}

@; TODO
@; - future work
@;   We leave as open the question of how to define a completion function that
@;    generates the minimum number of @${\vchk} expressions.@note{@citet[henglein-scp-1994]
@;     defines a rewriting system that is provably optimal, but possibly non-terminating.}
@; - what did we do in this paper? (where do I want to end up)
@;   * different semantics => simple & blame-free notions of typescript, TR, retic soundness
@;   * derive tag soundness, comes about by cutting costs

@; -----------------------------------------------------------------------------

The paper contributes two major results. First, the idea of viewing
 migratory typing as a multi-language problem demonstrates that a language
 with a migratory type system may satisfy at least five different
 type-soundness conditions, depending on which kind of ``foreign function
 interface'' we choose. Each soundness condition has different implications
 for how a developer can reason about the code, especially when it comes to
 diagnosing the cause of a run-time error.
@itemlist[

@; TODO this list should connect to the _embeddings_ and NOT the implementations

@item{Running a Typed Racket program as a Racket program (via erasure)
 gives a developer no clue as to what triggers an error; the type
 information in the code does @emph{not} reduce the search space. Indeed, a
 violation of the types in the source code may go unnoticed.}

@item{Running a Typed Racket program in @|LD-Racket| is guaranteed to reveal a
 violation of types @emph{eventually} if it affects the execution. The
 delayed checking schema may completely obscure the source of the error,
 however.}

@item{Running a Typed Racket program with the full contract checks uncovers
 a violation of type annotations as soon as there is a witness. @;{(As a
 matter of fact, Typed Racket's implementation can even point back to the
 violated type annotation.)}}

]

Second, our measurements are the first ``apples-to-apples'' comparison, and
they confirm that a locally defensive semantics reduces the cost of a
migratory run-time checking by at least an order of magnitude. We
conjecture that additional improvements on the checking scheme and the @|LD-Racket|
implementation may bring the performance within a reasonable overhead
factor for every mixed-typed configuration.

The question for researchers is thus what developers really want from a
migratory type system. More specifically, we need to ask how much
performance they are willing to sacrifice for how much soundness. We expect
that where there are five flavors of soundness, there might be many more,
and additional work may just find one that properly balances the need for
performance with the need for guarantees.

@acks{
  @; redex-check
  @; NSF funding
  @; early feedback at PI meeting
  @; pldi reviewers for skimming the paper and letting us know it wasn't shiny and new enough
}


@; Future work:
@; - static/dynamic analysis to attribute run-time cost to boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - static analysis, to pick natural vs. co-natural for a boundary (for efficiency)
@; - JIT for tagged, other things to reduce tag checks
