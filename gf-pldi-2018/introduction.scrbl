#lang gf-pldi-2018

@title[#:tag "sec:introduction"]{Flavors of Migratory Typing}

Over the past two decades, software developers have migrated from the world
 of C++ and Java to the broad world of untyped languages: JavaScript, Perl,
 Python, Ruby (on Rails), and many others. About one decade ago, they
 discovered the cost of using languages without type systems. In response,
 academic researchers simultaneously proposed gradual
 typing@~cite[st-sfp-2006 svcb-snapl-2015] and migratory
 typing@~cite[thf-dls-2006 tfffgksst-snapl-2017], both of which allow
 developers to mix typed into untyped code. Using such systems, developers
 can incrementally equip a code base with types and migrate it to the typed
 world. 

In theory, these type systems provide developers with an ideal pathway to
 equip a code base with types. To begin with, developers can add types
 wherever needed, explicitly stating (and checking) invariants that will
 help future readers to understand the code. Better still, the software
 system keeps functioning, regression test suites remain applicable, and
 the added types may just reveal some long-hidden obscure errors; in
 contrast, a whole-sale port to a (completely) statically typed language
 merely forces developers to go through the whole development process
 again---without improving the well-tested system. All this theory can work
 only if the performance of the mixed-type code base remains acceptable. As
 Takikawa et al. have recently shown@~cite[gtnffvf-jfp-2017], however, the
 performance is definitely @emph{not} acceptable when the underlying type
 system is @emph{sound}.  By comparison, industrial implementations of
 gradual typing come without performance problems because they do not
 insist on conventional type soundness. 

From a type-theoretic perspective, academic migratory type systems use a
 type-directed ``natural'' embedding of typed code into an untyped
 context@~cite[mf-toplas-2007]. Roughly speaking, when an untyped value
 mixes with typed code, it gets ``type checked'' at run time; viewed from
 the typed perspective, a typed value gets protected with a checking
 wrapper when it flows into an untyped context. All of these checks and wrappers
 add a significant overhead when mixed-typed code is run; the performance
 improves only when (almost) the entire code base is equipped with
 types. Industrial variants of these type systems use an ``erasure
 embedding.''  The result is code that does not detect when a run-time
 state violates the type invariant of the source code; indeed, it may never
 signal such a violation; but, it relies on the existing run-time checks of
 the underlying untyped language to prevent type violations from turning
 into the segmentation faults (of unsafe languages such as C++).

This paper contributes (1) several models of migratory type systems that
 sit between these extremes (see @section-ref{sec:design}). The
 development is inspired by Reticulated Python@~cite[vksb-dls-2014],
 a pre-processor implementation of a gradual type system for Python. We state
 theorems that demonstrate to what extent each model is type-sound.  (2) We
 explain how to implement the most promising variant in Typed Racket so
 that we can compare ``apples with apples'' (see
 @section-ref{sec:implementation}). And finally, we present the results of
 applying Takikawa et al.'s method to this implementation (see
 @section-ref{sec:evaluation}). The speed-up improvements are dramatic,
 typically an order-of-magnitude improvement. We thus consider these results
 a first step toward the creation of a feasible, sound migratory type
 system.  @Section-ref{sec:background} starts the paper with a presentation of
 the background, and section @section-ref{sec:related-work} explains the context
 in some detail.
