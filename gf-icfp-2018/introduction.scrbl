#lang gf-icfp-2018
@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; TODO examples need labels, need to stand out a little more

Migratory typing is a tool for software evolution.
If a dynamically-typed host language comes with a migratory typing system,
 developers can incrementally add type annotations to an existing codebase.
The static type checker then helps catch bugs, and the explicit type annotations
 serve as machine-checked comments.
If the migratory typing system additionally comes with a type soundness guarantee,
 then developers can use the type annotations to reason about correctness.

The vision of retrofitting static types on an existing language has inspired
 a lot of academic work on type-sound migratory typing systems.
These systems enforce type soundness with runtime checks.

@; TODO the challenge with typed/untyped interaction
@; TODO multi-language approach

At least three teams in industry have built migratory typing systems:
 Hack for PHP, TypeScript and Flow for JavaScript.
Unlike the academic works, these @emph{optionally typed} languages do not
 enforce type soundness; no matter the static type, an expression can reduce
 to any kind of value 
For example, if @${e} is a TypeScript expression and @${\rrEEstar} is a formal
 semantics for TypeScript, then:
@nested[#:style 'inset
 @;(@emph{erasure}) 
 @elem{If @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrEEstar v} then @${v} can be any kind of value.}
]@;
On one hand, optional typing provides a familiar semantics and avoids the
 performance question.
On the other hand, it severly limits the usefulness of static types.

@; TODO read https://github.com/Microsoft/TypeScript/issues/9825

Regarding performance, recent work by Takikawa and Greenman suggest that
 industry was right to avoid sound gradual typing.
They measured the performance of Typed Racket, a migratory typing system
 that provides a strong form of type soundness.
Let @${\rrNEstar} be a formal semantics for Typed Racket, then:
@nested[#:style 'inset
 @;(@emph{natural})
 @elem{If @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrNEstar v} then @${v} is a pair of integers.}
]@;
Typed Racket provides a similar, standard, compositional form of type soundness
 for all types, including first-class functions, delimited control operators,
 and first-class classes.
Unfortunately, the cost of enforcing this strong form of soundness can slow a
 working Racket program by over two orders of magnitude.
Given the choice between optional typing and unusably-slow soundness.

As the Typed Racket team struggled to improve performance (and met with moderate,
 but not order-of-magnitude, success), Vitousek et al devised a brilliant alternative.
They developed a migratory typing system for Python that offered a weak notion
 of type soundness with worst-case 10x performance cost.
To illustrate their soundness, let @${\rrKEstar} be the semantics for Reticulated:
@nested[#:style 'inset
 @;(@emph{locally-defensive})
 @elem{If @${\vdash e : \tpair{\tint}{\tint}} and
       @${e \rrKEstar v} then @${v} is a pair.}
]@;
Intuitively, they guarantee that every typed value matches its top-level type
 constructor.
This soundness is shallow and non-compositional, but better than nothing.

Vitouseks success raises two natural questions.
First, whether the result can be reproduced in another language.
Unfortunately they are no help in this sense ... the paper defines a compiler,
 proves a few desirable properties, and gives no advice to others seeking to
 build a similar compiler for a different language and type system.
Second, where there are three notions of soundness there might be others.

In this work, we explore the idea of a spectrum of type soundness and provide
 the first comparison of two semantics for one gradually typed language.
Contributions:
@itemlist[
@item{
  Systematically remove the sources of performance cost in the
   natural embedding and derive three semantics.
  The first two are novel; the third is a generalization of Reticulated.
}
@item{
  Prove soundness of five embeddings.
}
@item{
  Implement the third embedding, compare performance to Typed Racket,
   find similar overhead as Reticulated (vs Python).
}
]

As future work, we plan to combine this result with Pycket
 and collect data on users' experience with tag soundness.

