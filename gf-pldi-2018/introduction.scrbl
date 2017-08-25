#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Introduction}

A gradual typing system lets programmers trade the proof obligations
 of static typing for the run-time overhead of dynamic typing.
If a typed context @${C[\cdot]} expects an expression with type @${\tau}, then
 the gradual typing system will accept either a typed term @${e_0}
 (with a proof that @${\vdash e_0 : \tau})
 or a dynamically-typed expression @${e_1}; in the latter case, run-time checks ensure that
 the value of @${e_1} @emph{behaves as if} it had the static type @${\tau}.

The addition of run-time checks adds performance overhead.
The magnitude of this overhead depends on how the gradual typing system
 determines whether a value @${v} behaves like a value with the static type @${\tau};
 in other words, the overhead depends on the run-time interpretation of @${\tau}.

For example, let @${f} be a function that increments the first element in a
 list of numbers:
@;
 @exact|{$$f = \vlam{(xs : \tlist(\tint))}{(\efst{xs}) + 1}$$}|
@;
There are at least three ways to check whether untyped arguments to this
 function behave as values with type @$|{\tlist(\tint)}|.

One approach is to eagerly check that the argument is a list that only contains
 strings.
Thus the calls @${(f~``NaN'')} and @${(f~[1, ``NaN''])} result in dynamic type errors.
This is faithful to Reynold's notion of static typing@~cite[r-ip-1983],
 but adds linear-time overhead to the constant-time function.
Typed Racket@~cite[thf-popl-2008] implements this approach.

A second approach is to eagerly check that the argument is a list,
 but delay checking its elements until they are accessed.
Under this semantics, the call @${(f~[``NaN''])} fails with a dynamic type error
 and the call @${(f~[1, ``NaN''])} succeeds.
Reticulated implements this approach@~cite[vss-popl-2017].

A third approach is to ignore the type annotation.
TypeScript implements this approach@~cite[bat-ecoop-2014].
The TypeScript semantics of @${(f~``NaN'')} is the JavaScript semantics of
 the type-erased program.

Naturally, the semantics of dynamic typing affects the performance of
 gradually typed programs.
Typed Racket's "eager" semantics can slow programs by two or more orders of
 magnitude@~cite[tfgnvf-popl-2016], but the compiler can use type information
 to generate more efficient code@~cite[sthff-padl-2012].
Reticulated's "lazy" semantics typically adds no more than one order of
 magnitude@~cite[gm-tr-2017]; it remains to be seen whether Reticulated can
 implement safe, type-based optimizations.
TypeScript's "absent" types have no effect on performance.

Since the choice of how to dynamically enforce types has non-trivial implications
 for performance (and debugging), language designers should give programmers
 the freedom to choose their semantics.
We do this by extending the syntax of types, @${\tau}, with three modalities:
 an @emph{eager} modality @${\mnow},
 a @emph{lazy} modality @${\mlater},
 and a @emph{temporarily eager} modality @${\mtmp}.
In terms of the example above:
 the type @${\tlist^\mnow(\tint^\mnow)} eagerly checks any dynamically typed arguments;
 the type @${\tlist^\mnow(\tint^\mlater)} eagerly checks list-ness, but delays checking list elements;
 and the type @${\tlist^\mlater(\tint^\mlater)} has no run-time cost.

Contributions:
@itemlist[
@item{
  Describe dynamic type-checking strategies using modalities.
}
@item{
  A formal model whose type soundness statement generalizes the soundness
   of Typed Racket, Reticulated, StrongScript@~cite[rnv-ecoop-2015], and TypeScript.
}
@item{
  An implementation of modal migratory typing for Typed Racket, and a two-part
   performance evaluation: (1) comparing the cost of established type soundnesses
   (e.g. TR's generalized soundness vs. Reticulated's tag soundness), and
   (2) demonstrating how to systematically change modalities to improve performance.
}
]

@bold{Note:} we say "migratory typing"@~cite[tfffgksst-snapl-2017]
 because the type system does not include a dynamic type or a type consistency
 relation.
@; Our focus is integrating statically checked code and dynamically checked code.
