#lang gf-pldi-2018
@title[#:style 'unnumbered]{Appendix}

This appendix contains:
@itemlist[
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
@item{
  complete definitions for the embeddings discussed in the paper,
}
]

@;Supplementary materials include:
@; a PLT Redex development,
@; code for the benchmarks,
@; scripts to collect data,
@; the source code for Tag-Sound Racket,
@; a diff between Typed Racket and Tag-Sound Racket.


@; =============================================================================
@section{Benchmark Descriptions}

@bm-desc[
  "FSM"
  "Lihn Chi Nguyen"
  '()]{
  "Automata"
}

@figure["fig:benchmark-static" "Benchmark Size"
  @exact|{
\setlength{\tabcolsep}{0.2em}\begin{tabular}{lrrr}
Benchmark & \twoline{Untyped}{LOC} & \twoline{Annotation}{LOC} & \# Modules \\[1.5ex]\hline
{\tt sieve} & 35 & 17~~(49\%) & 2 \\[0.3ex]
{\tt fsm} & 182 & 56~~(31\%) & 4 \\[0.3ex]
{\tt morsecode} & 159 & 38~~(24\%) & 4 \\[0.3ex]
{\tt zombie} & 302 & 27~~\hphantom{0}(9\%) & 4 \\[0.3ex]
{\tt suffixtree} & 537 & 129~~(24\%) & 6 \\[0.3ex]
{\tt kcfa} & 229 & 53~~(23\%) & 7 \\[0.3ex]
{\tt snake} & 160 & 51~~(32\%) & 8 \\[0.3ex]
{\tt tetris} & 246 & 107~~(43\%) & 9 \\[0.3ex]
{\tt synth} & 835 & 139~~(17\%) & 10 \\[0.3ex]
\end{tabular}

}|]

@; =============================================================================
@section{Performance vs. Number of Typed Modules}

@figure*["fig:locally-defensive-linear"
         @elem{@|LD-Racket| (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample| )}
  (exact-plot* (map list TR-DATA* TAG-DATA*))]

@Figure-ref{fig:locally-defensive-linear} plots the number of typed modules (@|x-axis|)
 in a configuration against its running time in milliseconds (@|y-axis|).
To reduce visual overlap, the points representing configurations with @${N}
 modules are evenly spaced along the @|x-axis| along the interval @${N\pm 0.4}.

Three results stand out.
First, the orange points for @|LD-Racket| significantly out-perform the points
 for Typed Racket.
Second, the performance of @|LD-Racket| tends to increase linearly as the number
 of typed modules increases.
This increase levels off a bit at the right-most end because the implementation
 skips the codomain check on calls to statically-typed functions.
Third, the performance of Typed Racket has an umbrella shape.
The worst performance is in the middle, but the fully-typed performance is
 better than @|LD-Racket|.


@; =============================================================================
@section{Implementing Tagged Racket}

High-level architecture of Typed Racket:

@itemlist[
@item{
  type-check a module,
}
@item{
  use type environment to generate contracts for exported functions,
}
@item{
  optimize the module
}
@item{
  output Racket bytecode
}
]

To implement @|LD-Racket|, we modified step 2 and replaced step 3.

@subsection{Generating Type-Tag Contracts}

Typed Racket defines a function @hyperlink["https://github.com/racket/typed-racket/blob/master/typed-racket-lib/typed-racket/private/type-contract.rkt#L283"]{@racket[type->contract]} that
 (1) expects a type, (2) compiles the type to a data structure that describes a contract, (3) optimizes the representation of the data structure, and (4) compiles the data structure to Racket code that will generate an appropriate contract.
This ``data structure that describes a contract'' is called a @hyperlink["https://github.com/racket/typed-racket/tree/master/typed-racket-lib/typed-racket/static-contracts"]{static contract}.

We modified the @racket[type->contract] function to generate type-tag contracts
 by adding a new method to the static contracts API and a new function for static contracts.
The method converts a static contract to a Racket contract that checks it's type tag.
For example, the contract for a list type generates the tag check @racket[list?].
The function expects a static contract and a natural-number amount of fuel.
If the fuel is zero, it returns a tag version of the contract.
Otherwise, it recurs into the static contract and decrements the fuel if the contract
 is for a guarded type (e.g., an intersection type is unguarded).
Note: the initial fuel is always zero for the code we evaluate in this paper.


@subsection{Defending Typed Code}

We replaced the Typed Racket optimizer with a similarly-structured function that inserts type-tag checks.
The function is a fold over the syntax of a type-annotated program.
The fold performs two kinds of rewrites.

First, the fold rewrites almost every function application @racket[(f x)] to @racket[(check K (f x))], where @racket[K] is the static type of the application.
The exceptions, which do not get a check, are:
@itemlist[
@item{
  built-in functions that we trust to return a well-tagged value (e.g. @racket[map]),
}
@item{
  functions defined in statically-typed code (exception: accessor functions for user-defined @hyperlink["http://docs.racket-lang.org/reference/define-struct.html#%28form._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._struct%29%29"]{structs}),
}
]

Second, the fold defends typed functions from dynamically-typed arguments
 by translating a function like @racket[(λ (x) e)] to @racket[(λ (x) (check x) e)].
The structure of the check is based on the domain type of the function.

@; =============================================================================
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
@;@proof{
@;  TODO
@;}


@subsection{Static Typing}
@include-figure*["fig:sta-lang.tex" @elem{Statically-typed @${\langS}}]

@|S-SAFETY|
@;@proof{
@;  TODO
@;}


@subsection{Multi-Language}
@include-figure["fig:mixed-lang.tex" @elem{Static/Dynamic Multi-language}]

The languages in subsequent sections extend the syntax of @${\langM}
 and use its typing judgments to formulate safety guarantees.


@subsection{Erasure Embedding}
@include-figure["fig:erasure-embedding.tex" "Erasure Embedding"]

@|E-SAFETY|
@;@proof{
@;  TODO
@;}


@subsection{Natural Embedding}
@include-figure*["fig:natural-embedding.tex" "Natural Embedding"]

@|N-SAFETY|
@;@proof{
@;  TODO
@;}


@subsection{Co-Natural Embedding}
@include-figure*["fig:conatural-embedding.tex" "Co-Natural Embedding"]

@|C-SAFETY|
@;@proof{
@;  TODO
@;}


@subsection{Forgetful Embedding}
@include-figure*["fig:forgetful-embedding.tex" "Forgetful Embedding"]

@|F-SAFETY|
@;@proof{
@;  TODO
@;}


@subsection{Tagged Embedding}
@include-figure*["fig:tagged-embedding.tex" "Tagged Embedding"]
@include-figure*["fig:tagged-completion.tex" "Tagged Completion"]

@|K-SAFETY|


