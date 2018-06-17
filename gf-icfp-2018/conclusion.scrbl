#lang gf-icfp-2018
@title[#:tag "sec:conclusion"]{Finding Balance}

@; Future work:
@; - static/dynamic analysis to attribute run-time cost to boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - semantic type soundness theorems, better classification
@; - measure the cost of blame / error messages

@; -----------------------------------------------------------------------------

@;What should types mean in a mixed-typed program?
@;In the @|holong| embedding, base and inductive types have the same meaning as
@; in a statically-typed language.
@;Coinductive types have a different meaning, but semantically equivalent.
@;In the @|eolong| embedding, types are meaningless.
@;In the @|folong| embedding, types mean assertions---having
@; lots of types probably avoids catastrophic failure, but adds overhead.

This paper contributes two major results. First, it delivers a
 theoretical framework for investigating different ways of combining twin
 pairs of dynamically-typed and statically-typed languages. The framework
 generalizes the Matthews--Findler multi-language
 approach@~cite[mf-toplas-2009] and the theorems in @section-ref{sec:design}
 clearly show how soundness for a pair of languages requires a more careful
 treatment than soundness for a single language.
With the framework, we can finally work
 out a systematic comparison of prior work
 @emph{and} capture the @|folong| semantics of Reticulated@~cite[vss-popl-2017]
 in such a way that it
 is easy to create the first alternative implementation. 

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
 Running a @TR_E (@|eolong|) program gives a developer no clue as to what in the source code triggers an error; i.e., the type
  information in the code does @emph{not} reduce the search space.
Indeed, a violation of the types in the source code may go completely unnoticed.
}
@item{
 Running a @TR_LD (@|folong|) program is guaranteed to reveal a
  violation of types @emph{if it affects the execution of typed code}.
 The delayed checking schema is unlikely to pinpoint the source of the error,
 however.
}
@item{
 Running a @TR_N (@|holong|) program uncovers a violation
 of type annotations as soon as there is a witness and pinpoints the exact
 type boundary that is violated by this witness.}
]@;

@; In light of the work by New and Licata, only the @|holong| embedding
@;  can achieve type soundness in the traditional sense@~cite[fb-flops-2006 nl-fscd-2018].

In terms of performance, the picture is more nuanced than the literature
 would suggest. On mixed-typed programs: @|eolong| adds zero overhead,
 @|folong| checks add overhead on a pay-as-you-annotate basis,
 and the @|holong|
 approach may render a working program unusably slow.  For fully-typed
 programs, the @|holong| embedding often dominates @|eolong| and is
 significantly faster than the @|folong| semantics. Equipped with
 this comparison platform, we intend to explore additional ways of making
 some form of sound migratory typing sufficiently practical.

One strategy is to improve the @|folong| model with a more sophisticated completion function and
 evaluation property than the one extracted from the literature; the pair in @section-ref{sec:locally-defensive-embedding} is
 simple and includes some obviously redundant checks.
Occurrence typing@~cite[tf-icfp-2010] seems well-suited for this task.
A second strategy is to design a JIT compiler that can dynamically minimize
 the cost of run-time constructor checks; the HiggsCheck compiler@~cite[rat-oopsla-2017]
 might be a promising context in which to experiment.
Alternatively, combining the @|folong| approach with the Pycket@~cite[bauman-et-al-icfp-2015 bbst-oopsla-2017] JIT compiler for Racket
 may yield an implementation with good performance in all configurations.
A third strategy is to combine multiple semantics within a program, using
 the @|holong| embedding for fully-typed components and an embedding with weaker
 guarantees for other parts of the program.

@acks{
  This paper is supported by @hyperlink["https://www.nsf.gov/awardsearch/showAward?AWD_ID=1518844"]{NSF grant CCF-1518844}.
  @; redex-check
  @; early feedback at PI meeting
  @; pldi reviewers for skimming the paper and letting us know it wasn't shiny and new enough
  @;
  We thank Erik Ernst, Bryan LaChance, Benjamin S. Lerner, Fabian Muehlboeck, Max S. New, Artem Pelenitsyn, Ross Tate, and Jan Vitek.
  Felleisen acknowledges insightful conversations with Ron Garcia and Eric Tanter about the meaning of types in Reticulated Python.
}

