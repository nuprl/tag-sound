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
Ran each eight times on a Linux machine with two physical AMD Opteron 6376 processors
 and 128GB RAM.@note{The Opteron is a NUMA architecture.}
Each the processors ran at 2.30 GHz using the performance CPU governor.

Using Racket v6.10.1.


@section{Results}

Two datasets on each plot, typed vs. tagged.
Max overhead is significantly lower.
Increase is typically linear,
 levels off when fully-typed because skip all codomain checks.
(Never skip domain checks, need to measure that version.)

@figure*["fig:tagged-performance"
         @elem{Tagged Racket (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample| )}
  (overhead-plot* (map list TR-DATA* TAG-DATA*))]


@section{Threats to Validity}

Early prototype,
 IO actions,
 disabled TR optimizer,

