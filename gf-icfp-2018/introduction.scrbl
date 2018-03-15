#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO more citations? for adding types to dynamic
@; - hack
@; - imperial college, javascript
@; - bigloo boo cecil shen

@;{Large, reliable programs cannot be coded from scratch; there has to be a plan
 for growth@~cite[growing-a-language].}

@; -----------------------------------------------------------------------------

For the past two decades, many programmers have switched to untyped programming
 languages. Regardless of why they make this choice, they eventually discover
 that they wish their code base came with some types. To accommodate the migration of
 a large code base from an untyped language to a typed one, researchers have
 created migratory typing systems@~cite[tfffgksst-snapl-2017]. In essence, a
 migratory typing system comes with the same expression and statement syntax as
 the underlying untyped language but allows the addition of type annotations.
 While all such systems @emph{check} the type annotations@~cite[tf-dls-2006 bmt-ecoop-2010 wnlov-popl-2010 bat-ecoop-2014 rtsf-oops-2013 rsfbv-popl-2015 vss-popl-2017],
 it remains unclear what types @emph{should mean} in mixed-typed programs.

Over the years, three approaches have emerged for integrating a
 dynamically typed language with a statically typed twin. Each approach
 corresponds to a generalization of type soundness from one language to a
 pair of related languages.
@;
 The first approach is to enforce @emph{types eagerly} at the boundaries
 between statically and dynamically typed code, which leads to a generalized
 form of traditional type soundness@~cite[st-sfp-2006 tf-dls-2006
 tfffgksst-snapl-2017].  Eager enforcement prevents dynamically typed code
 from sending (type) invalid arguments to a typed function or returning
 invalid results into a typed context via callbacks. But, it may impose a huge run-time
 cost@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
@;
 A second approach is to @emph{erase the types} and rely on the soundness
 of the underlying dynamically typed language@~cite[b-ordl-2004
 bat-ecoop-2014]. While this lack of any dynamic enforcement is free of any
 overhead, it takes a ``garbage in, garbage out'' approach to runtime
 interactions between the statically typed and dynamically typed parts of a
 mixed-typed program.
@; 
 Finally, a third approach is to compromise between those two
 extremes and to check only the @emph{type constructors} as late as
 possible according to the type annotations@~cite[vss-popl-2017].
 Intuitively, this approach sacrifices some type safety in exchange for
 some performance. 

The existence of three approaches raises two scientific question concerning
a proper comparison:
@itemlist[

@item{@emph{How do the logical implications of the three approaches compare}?

 Publications on implementations of migratory typing often use the phrase
 ``type soundness'' to describe unconventional soundness claims
 about the pair of languages, without discussing how the new soundness differs
 from soundness for a single language.
 @; TODO add citations, Vitousek Richards Rastogi
 @; TODO add citations (if any) that claim TypeScript / Hack are sound

 To answer this question precisely, this paper explains the three
 approaches in a systematic manner with a novel semantic framework. For the
 same source languages and type system, it formulates the three approaches as three
 different semantics and, for each semantics, articulates a theorem that
 precisely states which properties are preserved. It also demonstrates with
 source-language examples how these theorems differ and the consequences
 for developers.}

@item{@emph{How do the three approaches compare with respect to performance}? 

 @; TODO find citations other than Vitousek that make fully-typed/untyped claims

 Although the purpose of migratory typing is to accomodate the creation of
 mixed-typed languages, the researchers in this area studied the performance
 of implementations only recently@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
 Only one pair of researchers made an attempt to compare two of the three
 approaches and promptly implied order-of-magnitude differences
 @emph{across completely different programming languages} using (mostly) unrelated
 benchmarks@~cite[gm-pepm-2018].
 @; Vitousek POPL 2017 makes apples-to-oranges claims, too

 To answer this question properly, this paper presents results of running
 the same benchmarks in three implementations of the same
 language corresponding to the three approaches. While our results confirm the
 published conjectures to some degree, we consider it imperative for the future
 of this research area to put the science on solid ground.
}

]
