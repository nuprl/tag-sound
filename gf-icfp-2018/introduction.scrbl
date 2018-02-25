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
These conventially-sound types prevent dynamically-typed code from sending
 invalid arguments to a typed function or data structure, but may impose a
 huge run-time cost@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
A third approach is to lazily @emph{enforce the type constructors} by checking
 that every typed expression reduces to a superficially-correct value@~cite[vss-popl-2017].
Intuitively, this approach sacrifices some type safety in exchange for some performance.
@; TODO (but no apples-apples data to base this comparison)
@;  ... nobody really understands teh tradeoff

The existence of three approaches to the problem of soundness for a pair of
 languages raises two scientific questions.
Our contributions answer these questions.
@itemlist[
@item{
  The first question is how to model the different notions of soundness in a
   common framework.
  In particular, the third approach exists only in a specific
   compiler and abstract machine@~cite[vss-popl-2017]; leaving it open whether
   another language can satisfy a similar soundness.
   @; TODO not quite ... the criteria is whats unclear, the theorem is just one thing
  we equip one surface syntax and type system with three different semantics
   and three different notions of soundness, corresponding to the optional,
   type-sound, and tag-sound approaches (section N);
  @; TODO should we hammer "pairs of langs" here? or, "systematic derive"?
}
@item{
  The second question is how the three notions of soundness compare in an ``apples-to-apples''
   performance evaluation of three practical implementations for one programming
   language.
  We implement the tag-sound model for Typed Racket and present the first
   comparative evaluation of three semantics for the same migratory typing
   system (section L).
}
]@;
@;This paper begins with a survey of related work.
Derive tag sound, find two new points on the spectrum along the way.

@;This work is the first common framework,
@; the first re-implementation of Reticulated,
@; and the first rigorous comparative evaluation of multiple semantics.
