#lang gf-pldi-2018
@title[#:style 'unnumbered]{Appendix}

@section{Source Languages}

@include-figure["fig:dyn-lang.tex" @elem{Dynamically-typed @|L_D|}]
@include-figure["fig:sta-lang.tex" @elem{Statically-typed @|L_S|}]


@section{Multi-Language}

@include-figure*["fig:mixed-lang.tex" @elem{Static/Dynamic Multi-language}]

Syntax and static typing for the combined language.


@section{The Embeddings}

This section spells out the details of each multi-language embedding.


@subsection{The Erased Embedding}
@include-figure["fig:erased-embedding.tex" "Type-Erased Embedding"]

@subsection{The Natural Embedding}
@include-figure["fig:natural-embedding.tex" "Natural Embedding"]

@subsection{The Lazy Embedding}
@include-figure["fig:delayed-embedding.tex" "Lazy Embedding"]

@subsection{The Forgetful Embedding}
@include-figure["fig:forgetful-embedding.tex" "Forgetful Embedding"]

@subsection{The Tagged Embedding}
@include-figure["fig:tagged-embedding.tex" "Tagged Embedding"]

