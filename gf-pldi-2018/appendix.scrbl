#lang gf-pldi-2018
@title[#:style 'unnumbered]{Appendix}

This appendix contains:
@itemlist[
@item{
  complete definitions and proofs for the language embeddings discussed in the paper,
}
@item{
  brief descriptions of the benchmark programs, and
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
    #:E "Erased Embedding"
    #:N "Natural Embedding"
    #:L "Delayed Embedding"
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


@theorem[@elem{@${\langD} term safety}]{
  If @${\welldyn e} then either:
}
@itemlist[
@item{
  @${e~\rrDstar~v}
}
@item{
  @${e~\rrDstar~\typeerror}
}
@item{
  @${e~\rrDstar~\valueerror}
}
@item{
  @${e} diverges
}
]
@proof{
  TODO
}


@subsection{Static Typing}
@include-figure["fig:sta-lang.tex" @elem{Statically-typed @${\langS}}]

@theorem[@elem{@${\langS} type safety}]{
  If @${\wellsta e : \tau} then either:
}
@itemlist[
  @item{
    @${e~\rrSstar~v} and @${\wellsta v}
  }
  @item{
    @${e~\rrSstar~\valueerror}
  }
  @item{
    @${e} diverges
  }
]
@proof{
  TODO
}


@subsection{Multi-Language}
@include-figure["fig:mixed-lang.tex" @elem{Static/Dynamic Multi-language}]

The languages in subsequent sections extend the syntax of @${\langM}
 and use its typing judgments to formulate safety guarantees.


@subsection{Erased Embedding}
@include-figure["fig:erased-embedding.tex" "Type-Erased Embedding"]

@theorem[@elem{@${\langE} term safety}]{
  If @${\wellM e : \tau} then @${\wellEE e} and either:
}
@itemlist[
@item{
  @${e~\rrEEstar~v} and @${\wellEE v}
}
@item{
  @${e~\rrEEstar~\typeerror}
}
@item{
  @${e~\rrEEstar~\valueerror}
}
@item{
  @${e} diverges
}
]
@proof{
  TODO
}


@subsection{Natural Embedding}
@include-figure*["fig:natural-embedding.tex" "Natural Embedding"]

@theorem[@elem{@${\langN} type safety}]{
  If @${\wellM e : \tau} then @${\wellNE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrNEstar v} and @${\wellNE v : \tau}
}
@item{
  @${e \rrNEstar E[e']} and @${e' \rrD \typeerror}
}
@item{
  @${e \rrNEstar \valueerror}
}
@item{
  @${e} diverges
}
]
@proof{
  TODO
}


@subsection{Delayed Embedding}
@include-figure["fig:delayed-embedding.tex" "Lazy Embedding"]

@theorem[@elem{@${\langL} type safety}]{
  If @${\wellM e : \tau} then @${\wellLE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrLEstar v} and @${\wellLE v : \tau}
}
@item{
  @${e \rrLEstar E[e']} and @${e' \rrD \typeerror}
}
@item{
  @${e \rrLEstar \valueerror}
}
@item{
  @${e} diverges
}
]
@proof{
  TODO
}


@subsection{Forgetful Embedding}
@include-figure["fig:forgetful-embedding.tex" "Forgetful Embedding"]

@theorem[@elem{@${\langF} type safety}]{
  If @${\wellM e : \tau} then @${\wellFE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrFEstar v} and @${\wellFE v : \tau}
}
@item{
  @${e \rrFEstar E[e']} and @${e' \rrD \typeerror}
}
@item{
  @${e \rrFEstar \valueerror}
}
@item{
  @${e} diverges
}
]
@proof{
  TODO
}


@subsection{Tagged Embedding}
@include-figure["fig:tagged-embedding.tex" "Tagged Embedding"]

@theorem[@elem{@${\langK} type-tag safety}]{
  If @${\wellM e : \tau}
   and @${\tagof{\tau} = K}, then
   @${\wellM e : \tau \carrow e^+}
   and
   @${\wellKE e^+ : K}
   and either:
}
@itemlist[
@item{
  @${e^+ \rrKEstar v} and @${\wellKE v : K}
}
@item{
  @${e^+ \rrKEstar E[e']} and @${e' \rrD \typeerror}
}
@item{
  @${e^+ \rrKEstar \valueerror}
}
@item{
  @${e^+} diverges
}
]


@; =============================================================================
@section{Benchmark Descriptions}

yo looo
