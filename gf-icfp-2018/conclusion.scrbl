#lang gf-icfp-2018
@title[#:tag "sec:conclusion"]{Finding Balance}

@; Future work:
@; - static/dynamic analysis to attribute run-time cost to boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - semantic type soundness theorems, better classification

@; -----------------------------------------------------------------------------

@;What should types mean in a mixed-typed program?
@;In the natural embedding, base and inductive types have the same meaning as
@; in a statically-typed language.
@;Coinductive types have a different meaning, but semantically equivalent.
@;In the erasure embedding, types are meaningless.
@;In the locally-defensive embedding, types mean assertions --- having
@; lots of types probably avoids catastrophic failure, but adds overhead.


The paper contributes two major results:
 (1) a common theoretical framework for the three forms of migratory typing
     that have developed over time, and
 (2) an apples-to-apples performance evaluation based on Racket.

Each approach to migratory typing and its corresponding soundness condition has
 different implications for how a developer can reason about the code, especially when
 diagnosing the cause of a run-time error.
@itemlist[
@item{
 Running a Typed Racket program as a Racket program (via erasure)
  gives a developer no clue as to what triggers an error; the type
  information in the code does @emph{not} reduce the search space.
Indeed, a violation of the types in the source code may go unnoticed.
}
@item{
 Running a Typed Racket program under the locally-defensive semantics is guaranteed to reveal a
  violation of types @emph{eventually} if it affects the execution.
 The delayed checking schema may completely obscure the source of the error,
  however.
}
@item{
 Running a Typed Racket program with the type-sound semantics uncovers a violation
 of type annotations as soon as there is a witness and pinpoints the exact
 boundary that is responsible.
}
]@;
In terms of performance on mixed-typed programs, the ranking is reversed:
 erasure adds zero overhead, locally-defensive checks lead to moderate overhead,
 and the natural approach may render a working program unusably slow.
For fully-typed programs the natural embedding is on par with erasure
 and significantly faster than the locally-defensive semantics,
 but the thesis of migratory typing is that programs do not need to be fully-typed.

The question for researchers is thus what developers really want from a
 migratory type system.
More specifically, we need to ask how much performance they are willing to
 sacrifice for how much soundness.
Developers are probably not going to accept the fact that adding types always leads
 to slower performance in the locally-defensive embedding, thus one important open
 question is how to reduce the cost of its type-constructor checks.
One strategy is to design a more sophisticated completion function and
 evaluation property; the pair in @section-ref{sec:locally-defensive-embedding} is
 simple and includes some obviously redundant checks.
Occurrence typing@~cite[tf-icfp-2010] is well-suited for this task.
A second strategy is to design a JIT compiler that can recognize and avoid
 redundant constructor checks; the compiler by @citet[rat-oopsla-2017] might
 be a promising context in which to experiment.
Alternatively, combining the locally-defensive approach with the orthogonal work on Pycket@~cite[bauman-et-al-icfp-2015 bbst-oopsla-2017]
 may yield an implementation with good performance in all configurations.
A third strategy is to automatically switch to the natural embedding when it
 is likely to give better performance.

@acks{
  @; redex-check
  @; NSF funding
  @; early feedback at PI meeting
  @; pldi reviewers for skimming the paper and letting us know it wasn't shiny and new enough
}

