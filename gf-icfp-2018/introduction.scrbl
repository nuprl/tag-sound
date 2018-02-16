#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO more citations? for adding types to dynamic
@; - hack
@; - imperial college, javascript
@; - bigloo boo cecil
@; - 


People have come to realize that they want to add explicit, checked type
 annotations to an existing codebase@~cite[s-popl-1981 bg-oopsla-1993 wc-toplas-1997 st-sfp-2006 tf-dls-2006 wnlov-popl-2010 bat-ecoop-2014 vss-popl-2017 tfffgksst-snapl-2017].
At least two companies have reached the same conclusion.

Over the years, three approaches have emerged for bringing some benefits of
 static typing to a dynamically-typed language.
One approach is to check type annotations statically and erase the types
 during compilation@~cite[b-ordl-2004 bat-ecoop-2014].
These optional types may catch simple logical errors, but take a
 ``garbage in, garbage out'' approach to interactions
 with the dynamically-typed parts of the codebase.
A second approach is to enforce type soundness with runtime checks, so that
 programmers may use types to compositionally reason about the behavior
 of typed code@~cite[st-sfp-2006 tf-dls-2006].
The cost of the runtime checks, however, may be prohibitively high@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
A third approach is to enforce a non-compositional, type-tag notion of soundness
 by checking only value constructors at runtime@~cite[vss-popl-2017],
Intuitively, this approach trades some type safety for some performance.

The existence of three approaches to this problem of soundness for a pair of
 languages raises a number of scientific questions.
A first question is how to model the different notions of soundness in a
 common framework.
In particular, the only model for the third approach consists of a specific
 compiler and abstract machine@~cite[vss-popl-2017]; it is unclear how to
 generalize this model to a different language.
A second question is how these notions of soundness compare in an ``apples-to-apples''
 performance evaluation of three practical implementations for one programming
 language.
A third question is whether there are other promising notions of soundness
 that lie between the optional, type-sound, and tag-sound approaches.

Our contributions address these questions:
@itemlist[
@item{
  we model the optional, type-sound, and tag-sound approaches to migratory
   typing as three multi-language embeddings@~cite[mf-toplas-2007]
   that enforce soundness by checking dynamically-typed values that flow
   into statically-typed contexts;
}
@item{
  we systematically derive the tag-sound model and two other notions of soundness
   from the type-sound model, demonstrating new points along a so-called spectrum
   of soundness; and
}
@item{
  we implement the tag-sound model for Typed Racket and present the first
   comparative evaluation of three semantics for the same migratoy typing
   system.
}
]

@;This work is the first common framework,
@; the first re-implementation of Reticulated,
@; and the first rigorous comparative evaluation of multiple semantics.
