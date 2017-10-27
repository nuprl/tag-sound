#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Introduction}

Gradual typing is supposed to be a nice unifying subject, right?
Implementations of gradual typing are anything but unifying.
More like polar opposites.
On one hand, Typed Racket implements sound gradual typing.
All guarantees of the type system are preserved in mixed programs,
 and the performance of such programs can be disastrous.
On the other hand, TypeScript implements unsound gradual typing.
Types are erased for runtime; performance is the same as JavaScript and the
 type system makes no promises about the dynamic behavior of a statically typed program.

TypeScript invokes sneers from academic types, but has a growing following
 of JavaScript programmers.
Typed Racket inspires fear in Racket programmers.

Great divide between the two.
Desirable to bridge this gap, all depends on the context of the programmer.
But what to do?
Vitousek etal demonstrate an interesting idea in the context of Python,
 specifically a compiler for Python with type annotations to base Python.
The compiler generates programs with decent performance and decent guarantees,
 falls between type soundness and type unsoundness.

TODO

Contributions:
@itemlist[
@item{
  formal model of the @emph{first-order embedding},
   statement and proof of @emph{type-tag soundness}
}
@item{
  systematic performance evaluation,
   performance of first-order embedding is order-of-magnitude improvement
}
@item{
  discussion of type-tag soudness, listing of surprising programs
   that are well-typed, incorrect, and potentially difficult to debug
}
]

This paper is organized as follows.
@Section-ref{sec:background} outlines the general problem of implementing a
 performant gradual type system, and compares the particular approaches taken by
 Typed Racket and Reticulated.
@Section-ref{sec:design} lists our design goals for tag-sound gradual
 typing and presents a formal model.
@Section-ref{sec:evaluation} compares the performance of Tagged Racket
 to Typed Racket.
@Section-ref{sec:conclusion} concludes.
