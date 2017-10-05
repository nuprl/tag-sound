#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Introduction}

Expressiveness, soundness, performance.
Three essential components of a gradual typing system, all three in tension.
Typed Racket has pretty good expressiveness and soundness, but not-so-good performance.
What to do?
Performance tuning is a viable approach.
Changing expressiveness is not viable;
 there's a performance problem if only (mutable) arrays can cross type boundaries.
Soundness tuning is also viable, and the subject of this paper.

Review.

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
There are at least two ways to check whether untyped arguments to this
 function behave as values with type @$|{\tlist(\tint)}|.
One way is to @emph{eagerly} check that the actual parameter @${xs} is a list
 and that its elements are all integers.
A second way is to @emph{lazily} check the types; for example,
 by (1) checking that @${xs} is a list before evaluating the body of the function
 and (2) checking that the return value of @${\efst{xs}} is an integer.

@; TODO tr and retic also differ in terms of type errors

Typed Racket implements the first approach, and ensures a generalized form
 of type soundness@~cite[tfffgksst-snapl-2017].
In short, if the expression @${e} has the static type @${\tau} and reduces
 to a value @${v}, then @${v} is of type @${\tau}.

Reticulated implements the second approach and ensures type-tag soundness@~cite[vss-popl-2017].
If @${e} has the static type @${\tau} and reduces to a value @${v}, then
 @${v} is of type @${\tagof{\tau}}.
For example, @${\tagof{\tlist{\tau}}} is @${\tlist} and
 @${\tagof{\tarrow \tau_0~\tau_1}} is @${\tarrow}, you know?

Based on two ad-hoc performance evaluations, the performance of Typed Racket
 and Reticulated is very different.
The performance overhead of gradual typing in Typed Racket can be two orders
 of magnitude or more@~cite[tfgnvf-popl-2016 greenman-jfp-2017].
The performance overhead of gradual typing in Reticulated is apparently within
 one order of magnitude no matter how the programmer mixes statically typed
 and dynamically typed code@~cite[gm-tr-2017].

These evaluations suggest that exchanging type soundness for tag soundness
 could drastically improve the performance of Typed Racket.
This paper provides an answer; contributions:
@itemlist[
@item{
  clear definition of tag soudness
}
@item{
  two strategies for tag soundness
}
@item{
  performance evaluation
}
]

An open question is whether programmers will accept tag soundness as an
 alternative to type soundness for reasoning about the correctness of their
 programs.

This paper is organized as follows.
@Section-ref{sec:background} outlines the general problem of implementing a
 performant gradual type system, and compares the particular approaches taken by
 Typed Racket and Reticulated.
@Section-ref{sec:design} lists our design goals for tag-sound gradual
 typing and presents a formal model.
@Section-ref{sec:evaluation} compares the performance of Tagged Racket
 to Typed Racket.
@Section-ref{sec:conclusion} concludes.
