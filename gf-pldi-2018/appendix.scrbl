#lang gf-pldi-2018
@title[#:style 'unnumbered]{Appendix}

This appendix contains:
@itemlist[
@item{
  complete definitions and proofs for the language embeddings discussed in the paper,
}
@item{
  brief descriptions of the benchmark programs,
}
@item{
  a set of figures comparing the running time of a configuration to the number
   of type annotations, and
}
@item{
  a comparison between the implementations of Typed Racket and Tag-Sound Racket.
}
]

Supplementary materials include:
 a PLT Redex development,
 code for the benchmarks,
 scripts to collect data,
 the source code for Tag-Sound Racket,
 a diff between Typed Racket and Tag-Sound Racket.


@section{Language Models}

See @figure-ref{fig:models-outline} for an illustration.

@figure["fig:models-outline" "Models Roadmap"
  @models-roadmap[
    #:D "Dynamic"
    #:S "Static"
    #:M "Multi-Language"
    #:E "Erasure Embedding"
    #:N "Natural Embedding"
    #:L "Co-Natural Embedding"
    #:F "Forgetful Embedding"
    #:K "Tagged Embedding"]]


@subsection{Definitions}

@definition[@elem{@${R}-divergence}]{
  An expression @${e} diverges for the reduction relation @${R} if for
   all @${e'} such that @${e~R~e'} there exists an @${e''} such that
   @${e'~R~e''}.
}


@subsection{Dynamic Typing}
@include-figure["fig:dyn-lang.tex" @elem{Dynamically-typed @${\langD}}]

@|D-SAFETY|
@proof{
  TODO
}


@subsection{Static Typing}
@include-figure*["fig:sta-lang.tex" @elem{Statically-typed @${\langS}}]

@|S-SAFETY|
@proof{
  TODO
}


@subsection{Multi-Language}
@include-figure["fig:mixed-lang.tex" @elem{Static/Dynamic Multi-language}]

The languages in subsequent sections extend the syntax of @${\langM}
 and use its typing judgments to formulate safety guarantees.


@subsection{Erasure Embedding}
@include-figure["fig:erasure-embedding.tex" "Erasure Embedding"]

@|E-SAFETY|
@proof{
  TODO
}


@subsection{Natural Embedding}
@include-figure*["fig:natural-embedding.tex" "Natural Embedding"]

@|N-SAFETY|
@proof{
  TODO
}


@subsection{Co-Natural Embedding}
@include-figure*["fig:conatural-embedding.tex" "Co-Natural Embedding"]

@|C-SAFETY|
@proof{
  TODO
}


@subsection{Forgetful Embedding}
@include-figure*["fig:forgetful-embedding.tex" "Forgetful Embedding"]

@|F-SAFETY|
@proof{
  TODO
}


@subsection{Tagged Embedding}
@include-figure*["fig:tagged-embedding.tex" "Tagged Embedding"]
@include-figure*["fig:tagged-completion.tex" "Tagged Completion"]

@|K-SAFETY|


@; =============================================================================
@section{Benchmark Descriptions}

yo looo
