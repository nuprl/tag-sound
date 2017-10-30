#lang gf-pldi-2018
@title[#:tag "sec:evaluation"]{Evaluation}

Have implemented the embedding for Typed Racket.
The prototype runs the Typed Racket type checker,
 rewrites the program to have defensive checks,
 and disables Typed Racket's contract generation.


@section{Errors Matter}

Prototype gives poor error messages,
 expected A got B.
Not even using the contract system,
 see tech report.

Improving the error messages will cost a lot.
How much is unclear, because maybe can improve the contract system.


@section{Method}

Section 2 outlined our method.

Ten functional programs from Takikawa.
Ran each eight times on unloaded machine, size memory GhZ.
Run sequentially.

Racket v6.10.1.


@section{Results}

Two datasets on each plot, typed vs. tagged.
Max overhead is significantly lower.
Increase is typically linear,
 levels off when fully-typed because skip all codomain checks.
But not domain so maybe I need to finish that to submit this.


@section{Threats to Validity}

Early prototype,
 IO actions,
 disabled TR optimizer,

