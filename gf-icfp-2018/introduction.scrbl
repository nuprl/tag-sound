#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@;{Large, reliable programs cannot be coded from scratch; there has to be a plan
 for growth@~cite[growing-a-language].}

@; -----------------------------------------------------------------------------

For the past two decades, many programmers have built systems in dynamically
 typed programming languages.
Regardless of why they make this choice, they eventually discover that they
 wish their code base came with some types.
 To accommodate the @emph{migration} of
 a large code base from an untyped language to a typed one, researchers have
 created migratory typing systems@~cite[tfffgksst-snapl-2017]. In essence, a
 migratory typing system comes with the same expression and statement syntax as
 the underlying untyped language but allows the addition of type annotations.
 While all such systems use the annotations for static analysis@~cite[bg-oopsla-1993
 mw-icfp-1997 fafh-sac-2009 bmt-ecoop-2010 wnlov-popl-2010 chj-oopsla-2012 rtsf-sac-2013
 bat-ecoop-2014 mmi-dyla-2014 rsfbv-popl-2015 rzv-ecoop-2015 bdt-esop-2016 vss-popl-2017 tfffgksst-snapl-2017],
 it remains unclear what these type annotations @emph{mean} for the behavior of a mixed-typed program.

Over the years, three approaches have emerged for interpreting types in a
 mixed-typed setting.
 Each approach generalizes type soundness from one language to a pair of
 related languages.
@;
 The first approach is to @emph{enforce types eagerly} at the boundaries
 between statically and dynamically typed code, which leads to a generalized
 form of traditional type soundness@~cite[st-sfp-2006 tf-dls-2006].
 Eager enforcement of higher-order types prevents dynamically typed code
 from sending (type) invalid arguments to a typed function or returning
 invalid results into a typed context via callbacks. But, it may impose a significant run-time
 cost@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
@;
 A second approach is to @emph{erase the types} and rely on the soundness
 of the underlying dynamically typed language@~cite[bat-ecoop-2014].
 @; @note{Bracha's @emph{pluggable types} (@hyperlink["http://bracha.org/pluggableTypesPosition.pdf"]{@tt{bracha.org/pluggableTypesPosition.pdf}}) provides additional motivation.}
 While this lack of any dynamic enforcement is free of run-time
 overhead, it takes a ``garbage in, garbage out'' approach toward
 interactions between the statically typed and dynamically typed parts of a
 mixed-typed program.
@; 
 Finally, a third approach is to compromise between those two extremes and to
 @emph{check type constructors} in a way that protects typed code against
 first-order errors@~cite[vss-popl-2017].

The existence of three approaches raises two scientific question concerning
a proper comparison:
@itemlist[

@item{@emph{How do the logical implications of the three approaches compare}?

 Publications on implementations of migratory typing often prove a
 ``type soundness'' (or ``type safety'') theorem without formally discussing
 how soundness for the pair of languages differs
 from soundness for a single language@~cite[vss-popl-2017 rsfbv-popl-2015].
 @; @note{See also: this unpublished manuscript with a single-language soundness theorem @hyperlink["https://arxiv.org/abs/1708.08021/"]{@tt{arxiv.org/abs/1708.08021/}}}

 To answer this question precisely, this paper explains the three
 approaches in a systematic manner within one semantic framework. For the
 same source syntax and type system, it formulates the three approaches as three
 different semantics and articulates three theorems that
 precisely state which properties are preserved. It also demonstrates with
 source-language examples how these theorems differ and the consequences
 for developers.}

@item{@emph{How do the three approaches compare with respect to performance}? 

 Although the purpose of migratory typing is to accomodate the creation of
 mixed-typed languages, researchers in this area have only recently studied the performance
 of implementations systematically@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017 mt-oopsla-2017 bbst-oopsla-2017].
Previous attempts to compare approaches make claims about
 @emph{different programming languages} using (mostly) unrelated
 benchmarks@~cite[vss-popl-2017 mt-oopsla-2017 gm-pepm-2018].

 To answer this question properly, the paper measures
 the same benchmarks in three implementations of the same syntax and type system,
 based on the common theoretical framework.
 While our results confirm the published conjectures to some degree, we
 consider it imperative for the future of this area to put the research
 on solid ground.
}

]
