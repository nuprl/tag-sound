#lang gf-icfp-2018
@title[#:tag "sec:existing-systems"]{Existing Systems}

@; TODO
@; Shen ??

@(define YES "X") @; @exact{\checkmark} not using checkmark, because don't want to suggest "no check = bad"
@(define NO "-")

@(define num-systems 22)
@(define num-natural 3)
@(define num-erasure 11)
@(define TS "TypeScript")
@(define JS "JavaScript")

The semantic framework developed in @section-ref{sec:design} suggests that a
 useful method to compare mixed-typed languages is to compare their notions
 of soundness and of type boundaries.
Any language that combines static and dynamic typing fits,
 whether or not the static type system is designed to accomodate the idioms of
 an existing dynamically-typed language.
For details, see the technical appendix@~cite[gf-tr-2018].

@Figure-ref{fig:existing-systems} illustrates by comparing the soundness
 guarantees of existing mixed-typed languages.
The three boxes in the figure are labeled with the three embeddings outlined
 in @section-ref{sec:design}; the languages directly below each box promise
 a similar notion of soundness.
Four languages---Gradualtalk, Nom, TPD, and Typed Racket---offer a generalized
 notion of type soundness for mixed-typed programs.
Eleven languages take the erasure approach, and do not use type annotations
 to constrain the behavior of a program.
Reticulated and our prototype are the only languages that provide type-constructor
 soundness.

In between the boxes for the embeddings, dashed lines connect two of the three
 pairs of embeddings.
The line between natural and erasure is labeled with the names of systems
 that offer a choice between full type soundness and type erasure.
The line between erasure and locally-defensive describes the soundness of Pyret,
 in which type annotations are optional but every annotation is enforced by
 a type-constructor check.
There is no line between natural and locally-defensive because there are no
 existing systems that bridge the gap.

@figure["fig:existing-systems" "Existing mixed-typed systems." @exact{
\begin{tikzpicture}
  \def\embeddingskip{4cm}
  \node (N)
    [draw,align=center]
    {\textbf{Natural Embedding}};
  \node (Nsub)
    [align=center,below of=N,yshift=1ex]
    {Gradualtalk@~cite[acftd-scp-2013], Nom@~cite[mt-oopsla-2017],\\
     TPD@~cite[wmwz-ecoop-2017], Typed Racket@~cite[tf-popl-2008]};

  \node (NE)
    [align=center,below of=N,xshift=\embeddingskip]
    {StrongScript@~cite[rzv-ecoop-2015], \\
     Thorn@~cite[wnlov-popl-2010]};

  \node (E)
    [draw,align=center,below of=NE,xshift=\embeddingskip]
    {\textbf{Erasure Embedding}};
  \node (Esub)
    [align=center,below of=E,yshift=-2ex]
    {ActionScript@~cite[rch-popl-2012], mypy, \\
     Flow, Hack, Pyre, Pytype, rtc@~cite[rtsf-sac-2013], \\
     Strongtalk@~cite[bg-oopsla-1993], TypeScript@~cite[bat-ecoop-2014], \\
     Typed Clojure@~cite[bdt-esop-2016], Typed Lua@~cite[mmi-dls-2015]};

  \node (ELD)
    [align=center,below of=E,xshift=-\embeddingskip]
    {Pyret};

  \node (LD)
    [draw,align=center,below of=ELD,xshift=-\embeddingskip]
    {\textbf{Locally-Defensive Embedding}};
  \node (LDsub)
    [align=center,below of=LD,yshift=2ex]
    {Reticulated@~cite[vss-popl-2017], {@|TR_LD|}};

  \draw[-,dashed] (N) -- (NE);
  \draw[-,dashed] (NE) -- (E);
  \draw[-,dashed] (LD) -- (ELD);
  \draw[-,dashed] (ELD) -- (E);
\end{tikzpicture}
}]

