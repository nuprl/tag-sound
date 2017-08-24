#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Introduction}

@; write a fable? about correct-by-construction vs. trans.validation ?

A gradual typing system lets programmers trade the proof obligations
 of static typing for the run-time overhead of dynamic typing.
If a typed context @${C[\cdot]} expects an expression with type @${\tau}, then
 the gradual typing system will accept either a proof @${\vdash e_0 : \tau}
 or a dynamically-typed expression @${e_1}; in the latter case, run-time checks ensure that
 the value of @${e_1} @emph{behaves as if} it had the static type @${\tau}.

The question arises, how much overhead does a program incur due to dynamic type checks?
The answer depends on how the gradual typing system determines whether a value
 @${v} behaves like a value with the static type @${\tau}; in other words,
 it depends on the run-time interpretation of @${\tau}.

For example, let @${f} be a function that increments the first element in a
 list of numbers:

 @exact|{$$f = \lambda (xs : \mathsf{List(Int)}).\, xs[0] + 1$$}|
@;
There are at least three ways to check whether untyped arguments to this
 function behave as values with type @$|{\mathsf{List(Int)}}|.

One approach is to eagerly check that the argument is a list that only contains
 strings.
Thus the calls @${f("NaN")} and @${f([1, "NaN"])} result in dynamic type errors.
This is faithful to Reynold's notion of static typing@~cite[r-ip-1983],
 but adds @${O(n)} overhead to the constant-time function.
Typed Racket@~cite[thf-popl-2008] implements this approach.

A second approach is to eagerly check that the argument is a list,
 but delay checking its elements until they are accessed.
Under this semantics, the call @${f(["NaN"])} fails with a dynamic type error
 and the call @${f([1, "NaN"])} succeeds.
Reticulated implements this approach@~cite[vss-popl-2017].

A third approach is to ignore the type annotation.
TypeScript implements this approach@~cite[bat-ecoop-2014].
The TypeScript semantics of @${f("NaN")} is the JavaScript semantics of
 the type-erased program.

Naturally, the semantics of dynamic typing affects the performance of
 gradually typed programs.
Typed Racket's "eager" semantics can slow programs by two or more orders of
 magnitude@~cite[tfgnvf-popl-2016], but the compiler can use type information
 to generate more efficient code@~cite[sthff-padl-2012].
Reticulated's "lazy" semantics typically adds no more than one order of
 magnitude@~cite[gm-tr-2017].
It remains to be seen whether Reticulated can implement sound, type-based optimizations.
TypeScript's "absent" types have no effect on performance.

Since the choice of how to enforce types at run-time comes with non-trivial
 performance tradeoffs, we propose to give programmers a choice between
 eager, lazy, and absent type checking.
We can generalize all three approaches with a @emph{modality} on types.
The eager mode, @${\always}, denotes a static type.
The lazy mode, @${\eventually}, denotes a dynamically typed value.
Using these modalities, we can modify the example above to express eager,
 lazy, and strict semantics by changing the type.
The type @${\mathsf{List}^\always(\mathsf{Int}^\always)} eagerly checks
 any dynamically typed arguments.
The type @${\mathsf{List}^\always(\mathsf{Int}^\eventually)} eagerly checks
 list-ness, but delays checking its elements.
The type @${\mathsf{List}^\eventually(\mathsf{Int}^\eventually)} has no
 run-time cost.

Contributions:
@itemlist[
@item{
  A model of modal gradual types, statement of type soundness.
}
@item{
  Eager, lazy, and absent type checking are corrolaries of the model.
}
@item{
  An implementation of modal gradual types for Typed Racket, and a two-part
   performance evaluation: (1) we compare the performance of eager and lazy
   checking on identical programs (2) we show how to improve the performance
   of eager programs by adding profile-guided laziness.
}
]
