#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO more citations? for adding types to dynamic
@; - hack
@; - imperial college, javascript
@; - bigloo boo cecil shen

Large, reliable programs cannot be coded from scratch; there has to be a plan
 for growth@~cite[growing-a-language].
One alluring plan for growth is to start with a dynamically-typed program and
 later add explicit and checked type annotations@~cite[s-popl-1981
 bg-oopsla-1993 wc-toplas-1997 st-sfp-2006 tf-dls-2006 wnlov-popl-2010
 bat-ecoop-2014 vss-popl-2017].
A migratory typing system@~cite[tfffgksst-snapl-2017] supports this plan by
 adding a statically-typed twin language to an existing, dynamically-typed
 language and integrating the pair of languages in a common runtime system.
@; TODO fix this whole paragraph, especially the final sentence

Over the years, three approaches have emerged for integrating a dynamically-typed
 language with its statically-typed twin; each approach
 corresponds to a different notion of soundness for the pair of languages.
One approach is to @emph{erase the types} and rely on the soundness of the
 dynamically-typed language@~cite[b-ordl-2004 bat-ecoop-2014].
These optional types may catch logical errors in typed code, but take a
 ``garbage in, garbage out'' approach to runtime interactions with the dynamically-typed
 parts of the codebase.
A second approach is to eagerly @emph{enforce the types} at the boundaries between
 static and dynamic code to provide a generalized form of type soundness
 for the statically-typed language@~cite[st-sfp-2006 tf-dls-2006 tfffgksst-snapl-2017].
These conventionally-sound types prevent dynamically-typed code from sending
 invalid arguments to a typed function or data structure, but may impose a
 huge run-time cost@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
A third approach is to lazily @emph{enforce the type constructors} by checking
 that every typed expression reduces to a superficially correct value@~cite[vss-popl-2017].
Intuitively, this approach sacrifices some type safety in exchange for some performance,
 but this tradeoff has not been measured systematically.

The existence of three approaches to the problem of soundness for a pair of
 languages raises two scientific questions, which we answer in this paper.
@itemlist[
@item{
  The first question is how the notions of soundness relate in a common
   theoretical framework.
  To this end, we equip one surface syntax and type system with three different
   semantics and three different notions of soundness, corresponding to the
   erasure, type-sound, and tag-sound approaches to migratory typing (section N).
  Furthermore, we use the common framework to systematically derive the tag-sound
   approach by eliminating known sources of performance overhead in the type-sound approach.
}
@item{
  The second question is how the three notions of soundness compare in a
   performance evaluation of three practical implementations for one programming
   language, as opposed to the ``apples-to-oranges'' comparisons present in the
   literature@~cite[gtnffvf-jfp-2017 vss-popl-2017 gm-pepm-2018].
  We answer this question by implementing the tag-sound approach for Typed
   Racket and comparing its performance to the erasure approach and the default
   type-sound approach (section L).
}
]@;
This paper begins with a survey of related work (section A),
 focuses on the models and their soundness theorems (section B),
 and then presents results of the performance evaluation (section C).
The conclusion outlines future work.

@;This work is the first common framework,
@; the first re-implementation of Reticulated,
@; and the first rigorous comparative evaluation of multiple semantics.
