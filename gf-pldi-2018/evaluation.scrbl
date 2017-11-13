#lang gf-pldi-2018
@title[#:tag "sec:evaluation"]{Evaluation}

@; TODO
@; - table with "MAX OVERHEAD" and "T/B RATIO"
@; -----------------------------------------------------------------------------

Based on the models, the natural, locally-defensive, and erased embeddings occupy
 three unique points on a spectrum between soundness and performance.
To measure how these embeddings stack up in a realistic setting,
 we have implemented a locally-defensive embedding as an extension of Typed Racket.
Since Typed Racket implements a natural embedding, this lets us compare the three approaches:
@itemlist[
@item{
  the natural embedding, as implemented by Typed Racket;
}
@item{
  the locally-defensive embedding, via our prototype; and
}
@item{
  the erasure embedding
}
]



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

Our implementation is an early prototype,
 significant threats to validity.

@; === things that make prototype too fast
Minimal error messages.


@; === things that make prototype too slow
Incompatible with TR optimizer.

Could optimize more checks.

@; === things that make prototype non-representative
Does not support objects.


@; === things about the benchmarks / experiment


@section{Experience}

Tag errors suck.
