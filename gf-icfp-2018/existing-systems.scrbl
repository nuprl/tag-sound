#lang gf-icfp-2018
@title[#:tag "sec:existing-systems"]{Existing Systems}

@; TODO
@; Shen ??

@(define num-systems 21)
@(define num-natural 4)
@(define num-erasure 11)
@(define TS "TypeScript")
@(define JS "JavaScript")


@Figure-ref{fig:existing-systems} classifies existing migratory and mixed-typed
 systems in terms of the three approaches.@note{The interested reader may
  wish to consult the technical report, in which we instantiate
  the framework of @section-ref{sec:design} for several existing systems@~cite[gf-tr-2018].}
Systems listed under the box labeled @emph{@|holong| embedding} enforce
 higher-order types at run-time.
Systems under the @emph{@|eolong| embedding} label provide an optional static type checker
 but do not use types to determine program behavior.
Systems under the @emph{@|folong| embedding} label enforce type boundaries
 with some form of first-order checks --- the details vary between systems.
In Dart 2 and Nom,
 every structured value is associated with run-time type
 information (e.g., the value is an object and is associated with a class name);
 the boundary checks perform a subtype test using this type information.
SafeTS is similar, however, the type information is structural rather than
 nominal and may gain new fields (but not methods) by crossing a boundary.
Reticulated and our @|TR_LD| prototype perform first-order checks similar
 to those outlined in @section-ref{sec:locally-defensive-embedding} and
 furthermore rewrite statically-typed code to protect against higher-order
 values.

The dashed lines in @figure-ref{fig:existing-systems} represent systems that
 offer a compromise between two approaches.
StrongScript and Thorn include two kinds of types: concrete types and like types.
Both types are checked statically, but only concrete types are enforced at
 run-time.
In other words, a program that uses only like types has @|eolong| behavior.
These similar systems are on different lines because only StrongScript supports
 higher-order types.

Pyret falls between the @|folong| and @|eolong| approaches.
If a program contains type annotations, then Pyret enforces each annotation
 with a run-time type constructor check.
A programmer can therefore opt-in to type-constructor
 soundness through disciplined use of type annotations.

There is no line between the @|holong| and @|folong| boxes because no
 existing systems explore that part of the design space.
This gap presents an opportunity for future work.


@(define MT @${^{\dagger}\!})
@figure["fig:existing-systems" @elem{Design space of migratory and mixed-typed systems.} @exact{
\begin{tikzpicture}
  \def\embeddingskip{4cm}
  \node (N)
    [draw,align=center]
    {\textbf{Higher-Order Embedding}};
  \node (Nsub)
    [align=center,below of=N,yshift=1ex]
    {Gradualtalk@|MT|@~cite[acftd-scp-2013], \\
     TPD@|MT|@~cite[wmwz-ecoop-2017], Typed Racket@|MT|@~cite[tf-popl-2008]};

  \node (NE)
    [align=center,below of=N,xshift=\embeddingskip]
    {StrongScript@~cite[rzv-ecoop-2015]};

  \node (E)
    [draw,align=center,below of=NE,xshift=\embeddingskip]
    {\textbf{Erasure Embedding}};
  \node (Esub)
    [align=center,below of=E,yshift=-3ex]
    {ActionScript@|MT|@~cite[rch-popl-2012], mypy@|MT|, \\
     Flow@|MT|, Hack@|MT|, Pyre@|MT|, Pytype@|MT|, \\
     rtc@|MT|@~cite[rtsf-sac-2013], Strongtalk@|MT|@~cite[bg-oopsla-1993], \\
     TypeScript@|MT|@~cite[bat-ecoop-2014], Typed Clojure@|MT|@~cite[bdt-esop-2016], \\
     Typed Lua@|MT|@~cite[mmi-dls-2015]};

  \node (ELD)
    [align=center,below of=E,xshift=-\embeddingskip]
    {Pyret@|MT|, \\
     Thorn@~cite[wnlov-popl-2010]};

  \node (LD)
    [draw,align=center,below of=ELD,xshift=-\embeddingskip]
    {\textbf{First-Order Embedding}};
  \node (LDsub)
    [align=center,below of=LD,yshift=1ex]
    {Dart 2, Nom@~cite[mt-oopsla-2017], Reticulated@|MT|@~cite[vss-popl-2017], \\
     SafeTS@~cite[rsfbv-popl-2015], @|TR_LD|@|MT| (@section-ref{sec:evaluation})};

  \node (legend)
    [align=right,right of=E,yshift=-20ex]
    {($\dagger$ : migratory typing system)};

  \draw[-,dashed] (N) -- (NE);
  \draw[-,dashed] (NE) -- (E);
  \draw[-,dashed] (LD) -- (ELD);
  \draw[-,dashed] (ELD) -- (E);
\end{tikzpicture}
}]

