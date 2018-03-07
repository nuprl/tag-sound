#lang gf-icfp-2018
@title[#:tag "sec:conclusion"]{Finding Balance}

@; TODO
@; - future work
@;   We leave as open the question of how to define a completion function that
@;    generates the minimum number of @${\vchk} expressions.@note{@citet[h-scp-1994]
@;     defines a rewriting system that is provably optimal, but possibly non-terminating.}
@;   JIT to kill redundant checks
@;   Profiler to choose between LD and natural
@; - natural embedding, why runtime check and not typecheck?
@;     maybe possible in pure language, probably not in any language worth building an MT system for

@; Future work:
@; - static/dynamic analysis to attribute run-time cost to boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - semantic type soundness theorems, better classification

@; -----------------------------------------------------------------------------

The paper contributes two major results:
 @; species of migratory typing?
 (1) a common theoretical framework for the three forms of migratory typing
     that have developed over time, and
 (2) an implementation of @emph{locally-defensive} migratory typing
     (the kernel underlying the transient semantics@~cite[vss-popl-2017])
     for Racket.
The latter contribution enables an apples-to-apples comparison of the three
 forms as implementations for a realistic programming language.
We measure performance and find that the
 locally-defensive embedding drastically improves the average-case performance
 on benchmarks from @citet[tfgnvf-popl-2016].

Each embedding and its corresponding soundness condition has different implications
 for how a developer can reason about the code, especially when
 diagnosing the cause of a run-time error.
@; TODO what is the most important implications to discuss?
@itemlist[
@item{
 Running a Typed Racket program as a Racket program (via erasure)
  gives a developer no clue as to what triggers an error; the type
  information in the code does @emph{not} reduce the search space.
Indeed, a violation of the types in the source code may go unnoticed.
}
@item{
 Running a Typed Racket program in @|LD-Racket| is guaranteed to reveal a
  violation of types @emph{eventually} if it affects the execution.
 The delayed checking schema may completely obscure the source of the error,
  however.
}
@item{
 Running a Typed Racket program with the full contract checks uncovers
  a violation of type annotations as soon as there is a witness.
 @;{(As a matter of fact, Typed Racket's implementation can even point back to the
  violated type annotation.)}
}
]

The question for researchers is thus what developers really want from a
 migratory type system.
More specifically, we need to ask how much performance they are willing to
 sacrifice for how much soundness.
@; maybe they want MORE guarantees; we stop at soundness but what about parametricity?
@;  (we should say _something_ about parametricity for ICFP)

Developers are probably not going to accept the ``more types, slower performance''
 characteristic of the locally-defensive embedding, thus one important open
 question is how to reduce the cost of type-tag soundness.
One strategy is to design a more sophisticated completion function and
 evaluation property; the pair in @secref{sec:locally-defensive-embedding} is
 simple and includes some obviously redundant checks.
An occurrence typing system@~cite[tf-icfp-2010] seems a perfect fit for this job.
A second strategy is to design a JIT compiler that can recognize and avoid
 redundant constructor checks; the compiler by @citet[rat-oopsla-2017] might
 be a promising context to experiment.
Alternatively, combining @|LD-Racket| with the orthogonal work on Pycket@~cite[bauman-et-al-icfp-2015 bbst-oopsla-2017]
 may yield an implementation with good performance in all configurations.
A third strategy is to automatically switch to the natural embedding when it
 is likely to give better performance.

Finally, where there are three (five) flavors of soundness there might be many others.
Additional work may just find one --- or a combination --- that
 balance the need for performance with the need for guarantees.

@acks{
  Omitted for review.
  @; Hey, could Scribble generate invisible/anonymized LaTeX that takes up
  @;  equal space but doesn't put sensitive info in the source?


  @; redex-check
  @; NSF funding
  @; early feedback at PI meeting
  @; pldi reviewers for skimming the paper and letting us know it wasn't shiny and new enough
}

