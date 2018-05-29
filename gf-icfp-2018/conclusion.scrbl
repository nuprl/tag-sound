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

The paper contributes two major results. First, it delivers a
 theoretical framework for investigating different ways of combining twin
 pairs of dynamically-typed and statically-typed languages. The framework
 generalizes the Matthews-Findler multi-language
 approach@~cite[mf-toplas-2007]. With this framework, we can finally work
 out a systematic comparison of the three current semantics of migratory
 typing @note{In addition to the comparison, it also suggests two alternative
 variants that fall between the natural and locally-defensive semantics.
 The appendix outlines these variants, and the supplement contains the technical details@~cite[gf-tr-2018].}
 @emph{and} capture the locally defensive semantics in such a way that it
 was easy to create the first alternative implementation. 

Second, this paper is the first to present an apples-to-apples performance
 evaluation of three implementations of these primary semantics of
 migratory typing. This evaluation weakly confirms conjectures in the
 literature, which is valuable, but most importantly it shows that none of
 these approaches dominates across the whole spectrum. Jointly the two
 contributions put the systematic and comparative study of a ``spectrum'' on
 a firm basis that allows well-founded conclusions. 

In practice, each approach has different implications for how a developer can
reason about the code, especially when diagnosing the cause of a run-time error:
@itemlist[
@item{
 Running a @TR_E program gives a developer no clue as to what in the source code triggers an error; i.e., the type
  information in the code does @emph{not} reduce the search space.
Indeed, a violation of the types in the source code may go completely unnoticed.
}
@item{
 Running a @TR_LD program is guaranteed to reveal a
  violation of types @emph{if it affects the execution}.
 The delayed checking schema is likely to obscure the source of the error,
 however. 
}
@item{
 Running a @TR_N program uncovers a violation
 of type annotations as soon as there is a witness and pinpoints the exact
 boundary that is violated by this witness.}
]@;

@; In light of the work by New and Licata, only the natural embedding
@;  can achieve type soundness in the traditional sense@~cite[fb-flops-2006 nl-fscd-2018].

In terms of performance, the picture is much more mixed than the literature
 would suggest. On mixed-typed programs, erasure adds zero overhead,
 locally-defensive checks lead to moderate overhead, and the natural
 approach may render a working program unusably slow.  For fully-typed
 programs the natural embedding often dominates erasure and is
 significantly faster than the locally-defensive semantics. Equipped with
 this comparison platform, we intend to explore additional ways of making
 some form of sound migratory typing sufficiently practical.

One strategy is to design a more sophisticated completion function and
 evaluation property than the one extracted from the literature; the pair in @section-ref{sec:locally-defensive-embedding} is
 simple and includes some obviously redundant checks.
Occurrence typing@~cite[tf-icfp-2010] seems well-suited for this task.
A second strategy is to design a JIT compiler that can recognize and avoid
 redundant constructor checks; the compiler by @citet[rat-oopsla-2017] might
 be a promising context in which to experiment.
Alternatively, combining the locally-defensive approach with the Pycket@~cite[bauman-et-al-icfp-2015 bbst-oopsla-2017] compiler for Racket
 may yield an implementation with good performance in all configurations.
A third strategy is to combine multiple semantics within a program, using
 the natural embedding for fully-typed components and an embedding with weaker
 guarantees for other components.

@acks{
  @; redex-check
  @; NSF funding
  @; early feedback at PI meeting
  @; pldi reviewers for skimming the paper and letting us know it wasn't shiny and new enough
  @; Artem P. for comments
  Felleisen would like to acknowledge insightful conversations with Ron Garcia and Eric Tanter about the meaning of types in a locally-defensive setting.
}

