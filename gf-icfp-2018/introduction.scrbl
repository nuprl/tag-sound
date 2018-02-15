#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO
@; - examples need labels, need to stand out a little more
@; - M: don't need to mention Pycket, just wait until conclusion
@;   ... maybe turn it around, use Pycket to describe Racket
@; - intro needs to be fucking concrete ... best to use actual code


People have come to realize that they want to add explicit, checked type
 annotations to an existing codebase@~cite[vss-popl-2017].

Over the years, three approaches have emerged for bringing some benefits of
 static typing to a dynamically-typed language.
One approach is to check type annotations statically and erase the types
 during compilation.
These unsound types may catch simple logical errors, but take a
 ``garbage in, garbage out'' approach to interactions
 with the dynamically-typed parts of the codebase.
@; leave typed code at the mercy of ....
A second approach is to enforce type soundness with runtime checks, so that
 programmers may use types to compositionally reason about the correctness
 of typed code.
The cost of the runtime checks, however, may be prohibitively high@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
A third approach is to enforce a weaker, type-tag notion of soundness by
 checking only basic properties of values at runtime.
This approach has led to decent performance in Reticulated Python@~cite[vss-popl-2017],
 but it is unclear whether that success can be reproduced in another language.

In this work, we:
@itemlist[
@item{
  model the unsound, sound, and tag-sound approaches to
   migratory typing in a common framework;
}
@item{
  derive the tag-sound model by systematically removing three sources of
   performance overhead in the sound model;
}
@item{
  present two novel approaches that lie between the sound and tag-sound
   strategies; and
}
@item{
  compare the performance of the unsound, sound, and tag-sound approaches
   implemented as three semantics for Typed Racket.
}
]

This work is the first common framework,
 the first re-implementation of Reticulated,
 and the first rigorous comparative evaluation of multiple semantics.
