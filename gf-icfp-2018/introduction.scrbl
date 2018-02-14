#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO
@; - examples need labels, need to stand out a little more
@; - M: don't need to mention Pycket, just wait until conclusion
@;   ... maybe turn it around, use Pycket to describe Racket
@; - intro needs to be fucking concrete ... best to use actual code



Over the last two decades, programmers have transitioned from the world
 C++ and Java to the broad world of dynamically-typed languages: JavaScript,
 Perl, Python, Ruby (on Rails), and many others.
About one decade ago, programmers discovered the maintenance cost of using
 languages without type systems.
In response, academic researchers simultaneously proposed gradual typing@~cite[st-sfp-2006 svcb-snapl-2015]
 and migratory typing@~cite[thf-dls-2006 tfffgksst-snapl-2017].
The latter retrofits a static typing system onto an existing language.

In theory, a migratory typing system gives programmers an ideal pathway to
 equip a codebase with types.
To begin with, a developer can add types wherever needed, explicitly stating
 invariants that will help future readers to understand the code.
Better still, the software system keeps functioning, regression test suites
 remain applicable, and the added types may just reveal some long-hidden
 errors; in contrast, a whole-sale port to a (completely) statically
 typed language merely forces developers to go through the whole development
 process again---without necessarily improving the well-tested system.

Inspired by this vision, at least three companies have invested significant
 resouces implementing optional typing systems.
@;for JavaScript, PHP, and Python.
An optional typing system is simply a migratory typing system with no type soundness
 guarantee; the type annotations in these languages may be used for static
 analysis, but they are @emph{erased} during compilation and have no effect on
 program behavior.
For example, if @${\vdash} is the static typing judgment and @${\rrEEstar} is the
 reduction relation for an optionally typed language:
@nested[#:style 'inset
 @elem{(@emph{Soundness 1:})
       if @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrEEstar v} then @${v} might be any kind of value}
]@;
@; TODO "generally speaking"
This means that @${\rrEEstar} can simply be the semantics of the host language, and
 the designers of the migratory typing system can focus their efforts on
 the typing judgment and IDE tools that leverage type information.
Unfortunately, it also means that programmers cannot trust the types when
 reasoning about the correctness of mixed-typed programs.

@; TODO read https://github.com/Microsoft/TypeScript/issues/9825

By contrast, academic work on migratory typing has focused on systems that
 enforce type soundness with runtime checks.
The most mature of these systems is Typed Racket;
 it implements a strong form of type soundness based on Matthew's and Findler's
 @emph{natural} embedding of ML in Scheme.
To illustrate, let @${\rrNEstar} be a reduction relation for Typed Racket:
@nested[#:style 'inset
 @elem{(@emph{Soundness 2:})
       if @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrNEstar v} then @${v} is a pair of integers}
]@;
Typed Racket programmers can therefore use static types to compositionally
 verify the correctness of their programs.
If this seems too good to be true, never fear---it is.
Enforcing this strong form of soundness at runtime can slow a working
 program by over two orders of magnitude@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].

Until recently, these two extremes represented the state of the art:
 type-unsound and usable versus type-sound and disastrously slow.@note{This caricature
 is a bit simplistic given the work on Pycket@~cite[bbst-oopsla-2017]
 (see @secref{sec:related-work}).
 It is more accurate to say ``disastrously slow using conventional JIT technology''.}
@citet[vss-popl-2017] suggest a middle ground via Reticulated, a migratory
 typing system for Python.
Roughly speaking, a reduction relation @${\rrKEstar} corresponding to their
 transient enforces a shallow, constructor-level notion of soundness:
@nested[#:style 'inset
 @elem{(@emph{Soundness 3:})
       If @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrKEstar v} then @${v} is a pair.}
]@;
This form of soundness is non-compositional, but prevents the silent failures
 that can occur with optional typing@~cite[tfffgksst-snapl-2017].
Moreover, it appears to come at a more reasonable runtime cost.
@citet[vss-popl-2017] report a worst-case overhead of about 6x for fully-typed
 programs, and @citet[gm-pepm-2018] confirm that programs mixing typed and
 untyped code have similar performance.

A natural question is whether the performance of Reticulated can be reproduced
 for other migratory typing systems.
Prior work suggests that replacing Typed Racket's reduction relation
 with a suitable ``transient'' reduction relation should lead to an order-of-magnitude
 improvement@~cite[gm-pepm-2018], but it is unclear how to adapt the novel ideas
 from Reticulated to another language.
@citet[vss-popl-2017] define transient by its implementation
 (i.e., a compiler and reduction relation) and soundness theorem;
 they do not explain what properties a different implementation must satisfy
 to be properly ``transient'', or whether such properties exist.
Another question is whether there are other forms of soundness that lie along
 the three-point spectrum from type soundness to type-tag soundness to type unsoundness.
Our contributions address these questions:
@itemlist[
@item{
  We model the key ideas from optional typing, Typed Racket, and Reticulated
   as three multi-language embeddings@~cite[mf-toplas-2007]:
   the @emph{erasure} embedding, the @emph{natural} embedding,
   and the @emph{locally-defensive} embedding, respectively (@secref{sec:design}).
  The differences between the embeddings are captured by their reduction
   relations; each relation preserves a different soundness invariant.
}
@item{
  The locally-defensive embedding comes about by systematically
   addressing three sources of performance overhead in the natural embedding.
  Addressing the first two sources independently leads to two novel embeddings,
   the @emph{co-natural} and @emph{forgetful} embedding, with notions of
   soundness that lie between type soundness and type-tag soundness (@secref{sec:design}).
}
@item{
  Our implementation of the locally-defensive embedding for Racket demonstrates
   a worst-case performance overhead of 10x on mixed-typed programs (@secref{sec:evaluation}).
  This is a significant improvement over Typed Racket; however, Typed Racket
   has superior performance on fully-typed programs.
}
]@;
Our work thus presents the first rigorous comparison of two semantics for
 the same migratory typing system, and provides a theoretical framework to
 support future comparisons.

@Secref{sec:background} starts the paper with a presentation of the background,
 @secref{sec:implementation} explains the key aspects of scaling the model to
 an implementation in Racket, and @secref{sec:related-work} discusses the
 research context.
The conclusion (@secref{sec:conclusion}) outlines avenues for future work.
