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


Many existing languages support a combination of static and dynamic typing.
@Figure-ref{fig:existing-systems} illustrates the design space.
Some languages are @emph{migratory typing} systems that add static typing to a
 dynamically-typed language and support interactions between the host language and its typed twin.
Others are typed languages with a modicum of dynamic typing;
 @; TODO extrememA ... its really most-like-migratory
 in the extreme, such languages permit the definition of @emph{untyped values}
 and add @emph{implicit casts} to mediate between static and dynamic components.
Naturally, the design choices of these languages affect their @emph{soundness} guarantee.

Among the existing migratory typing systems, @integer->word[num-natural] languages
 (grouped in the first row) implement the natural embedding and promise
 a strong form of type soundness.
@Integer->word[num-erasure] languages use types only for static analysis,
 and thus implement the erasure embedding.
Reticulated is a migratory typing system for Python that enforces soundness
 at the level of type constructors.

The other languages in @figure-ref{fig:existing-systems} support diverse combinations
 of static and dynamic typing.@note{The appendix contains informal technical
 illustrations of the other languages, in the style of our semantic framework (@section-ref{sec:design}).}
Pyret is a new language with optional type annotations.
Each annotation is enforced by a type-constructor check at run-time, thus a
 fully-annotated Pyret program is likely sound at the level of type constructors.
Nom is a gradually-typed@~cite[svcb-snapl-2015] language in which every object
 has an intrinsic type, but may be bound to dynamically-typed variables.
Nom supports a strong form of type soundness.
Safe @|TS| is a type-sound variant of @|TS| that does not support sound
 interaction with @|JS|.
C# (version 4.0) includes a dynamic type; once a value is bound to a dynamically-typed
 variable, the C# compiler recompiles the expressions in scope.
Dart is a new language (incompatible with Dart 1.x) with a dynamic type similar to the C# type.
In Dart, a dynamically-typed variable may receive any kind of method call
 but cannot be sent directly to a statically-typed context.
StrongScript is an extension of TypeScript in which a variable may have either
 a static type, the dynamic type, or a @emph{like} type that constrains the
 local use of the variable.
StrongScript is a migratory typing system for JavaScript, but its practical
 utility is limited because a JavaScript context cannot invoke a typed function
 without explicitly casting its arguments to match the types.
In other words, the act of adding types to one module may necessitate the
 addition of types to another module.
Thorn is a direct predecessor to Dart 2.0 and StrongScript.

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

