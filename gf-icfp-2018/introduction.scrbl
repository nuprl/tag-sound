#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO more citations? for adding types to dynamic
@; - hack
@; - imperial college, javascript
@; - bigloo boo cecil shen
@; - 

Large, reliable programs cannot be coded from scratch; there has to be a plan
 for growth@~cite[growing-a-language].
One alluring plan for growth is to start with a dynamically-typed program and
 later add explicit and checked type annotations@~cite[s-popl-1981
 bg-oopsla-1993 wc-toplas-1997 st-sfp-2006 tf-dls-2006 wnlov-popl-2010
 bat-ecoop-2014 vss-popl-2017].
A migratory typing system@~cite[tfffgksst-snapl-2017] supports this plan by
 adding a statically-typed twin language to an existing, dynamically-typed
 language and monitoring the runtime interactions between the pair of languages.

Over the years, three approaches have emerged for monitoring the interactions
 between a dynamically typed language and its statically-typed twin; each
 approach corresponds to a different notion of soundness for the integration of
 the two languages.
One approach is to erase the types during compilation and let soundness for the
 pair be their lowest common denominator, namely, the soundness of the
 dynamically-typed language@~cite[b-ordl-2004 bat-ecoop-2014].
These @emph{optional} types may catch static type errors, but take a
 ``garbage in, garbage out'' approach to runtime interactions with the
 dynamically-typed parts of the codebase.
A second approach is to generalize the standard, compositional type soundness
 @; TODO cite?
 (for a single language) by interpreting types as higher-order contracts for
 dynamically-typed values@~cite[st-sfp-2006 tf-dls-2006].
Programmers may use these sound types to reason about interactions with dynamically-typed code.
The performance cost of the enforcement, however, may be prohibitively
 high@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
@; TODO would rather say "the contracts allow soundness, but may come at a huge cost"
A third approach is to enforce a non-compositional, type-tag notion of soundness
 by checking only value constructors at runtime@~cite[vss-popl-2017].
Intuitively, this approach sacrifices some type safety in exchange for some performance.
@; TODO but no data to base this comparison

The existence of three approaches to the problem of soundness for a pair of
 languages raises two scientific questions.
The first question is how to model the different notions of soundness in a
 common framework.
In particular, the only model for the third approach consists of a specific
 compiler and abstract machine@~cite[vss-popl-2017]; leaving it open whether
 another language can satisfy a similar soundness.
 @; TODO not quite ... the criteria is whats unclear, the theorem is just one thing
The second question is how these notions of soundness compare in an ``apples-to-apples''
 performance evaluation of three practical implementations for one programming
 language.
Our contributions address these questions:
@itemlist[
@item{
  we equip one model with three different semantics and three different
   notions of soundness, corresponding to the optional, type-sound, and
   tag-sound approaches (section N);
  @; TODO should we hammer "pairs of langs" here? or, "systematic derive"?
}
@item{
  we implement the tag-sound model for Typed Racket and present the first
   comparative evaluation of three semantics for the same migratory typing
   system (section L).
}
]@;
@;This paper begins with a survey of related work.
Derive tag sound, find two new points on the spectrum along the way.

@;This work is the first common framework,
@; the first re-implementation of Reticulated,
@; and the first rigorous comparative evaluation of multiple semantics.
