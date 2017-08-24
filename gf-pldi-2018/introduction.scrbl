#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Introduction}

@; write a fable? about correct-by-construction vs. trans.validation ?

A gradual typing system lets programmers trade the proof obligations
 of static typing for the run-time overhead of dynamic typing.
Suppose the safety of a program @${C[e]} depends on whether the expression @${e}
 has type @${\tau}.
To establish the type of @${e}, one can either build a proof @${\vdash e : \tau}
 using the static typing system, or let the language evaluate @${e} and
 check whether the resulting value (if any) happens to belong to the
 static type @${\tau}.
Both approaches ensure that ${C[e]} does not commit a type error.


 

To show that an expression @${e} has type @${\tau}, one can either
 prove @${\vdash e : \tau} within the static type system, or 

@; -----------------------------------------------------------------------------

Typed Racket suggests the cost can be high,
 if follow conventional wisdom and check eagerly.

Reticulated, third option.

TypeScript, on the other hand.
No soundness, at least nothing extra.
No cost.

Spectrum of soundness.
All three above instances of general scheme.
Since tradeoffs non-trivial, better give the programmer control.

Examples, Int dot, f cod is dot, id polymorphic.

Reminds of CBN CBV.
Typechecking is eager or lazy.

Gives control over costs, errors, optimizations.

Main contribution, model of type system and proofs of meta-theory properties.
Show how to express Typed Racket, Reticulated, and TypeScript semantics in the
 model.
Dart too?
Show how errors matter and change.

Two-part evalation.
First, for all configurations, measure fully-strict, fully-lax, tag-strict strategies.
Gives sense of overall cost of soundness.
Second, for slow fully-strict configurations, explore minimal changes to improve performance.
Towards a profiler that can suggest type-strictness changes.
