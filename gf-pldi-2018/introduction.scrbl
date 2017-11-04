#lang gf-pldi-2018

@title[#:tag "sec:introduction"]{Three Flavors of Migratory Typing}

@; tfffgksst-snapl-2017

@; NOTE: 'migratory' and not 'gradual' because our static typing
@;   systems do not use a dynamic type,
@;   and do not have a type consistency relation

@; Racket -> LISP ->
@; Parentheses
@; Racketensis
@; Fungus ???
@; Bacteria ?

@; Reticulated Python -> Python -> python
@; Kingdom:  Animalia
@; Phylum: Chordata
@; Class:  Reptilia
@; Order:  Squamata
@; Suborder: Serpentes
@; Infraorder: Alethinophidia
@; Family: Pythonidae

@; JavaScript -> Java -> Coffee
@; Kingdom:  Plantae
@; Clade:  Angiosperms
@; Clade:  Eudicots
@; Clade:  Asterids
@; Order:  Gentianales
@; Family: Rubiaceae
@; Tribe:  Coffeeae
@; Genus:  Coffea

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

In theory, these type systems provide software developers with an ideal
 pathway to equip a code base with types. To begin with, developers can add
 types wherever needed. Better still, the software system keeps
 functioning, regression test suites remain applicable, and the added types
 may just reveal some long-hidden obscure errors; in contrast, a whole-sale
 port to a different language merely forces developers to go through the
 whole development process again---without improving the well-tested
 system. All this theory can work only if the performance of the mixed-type code
 base remains acceptable. As Takikawa et al. have recently
 shown@~cite[tfgnvf-popl-2016], however,  the performance is definitely
 @emph{not} acceptable when the underlying type system is @emph{sound}. 
 By comparison, industrial implementations of such type systems come
 without performance problems because they do not insist on type
 soundness. 

From a type-theoretic perspective, academic migratory type systems use a
 type-directed ``natural'' embedding of typed code into an untyped
 context@~cite[mf-toplas-2007]. Roughly speaking, when an untyped value
 mixes with typed code, it gets ``type checked'' at run time; viewed from
 the typed perspective, a typed value gets protected with a checking
 wrapper when it flows into an untyped context. All of these checks add a
 significant overhead when mixed-typed code is run; the performance
 improves only when (almost) the entire code base is equipped with
 types. Industrial variants of these type systems use an ``identity
 embedding.''  The result is code that does not catch the misuse of a typed
 value in an untyped context but relies on the existing run-time checks of
 the underlying untyped language to prevent the segmentation faults (of
 unsafe languages such as C++).

This paper contributes (1) several models of migratory type systems that
 sit between these two extremes. The development is inspired by Reticulated
 Python@~cite[vksb-dls-2014], an pre-processor implementation of a gradual
 type system for Python. We state theorems that explain to what extent each
 model is type-sound. (2) We add examples how things go wrong during an
 execution and remain unnoticed in these weaker systems. (3) We explain how
 to implement the most promising variant in Typed Racket, and we present
 the results of applying Takikawa et al.'s method to this
 implementation. The speed-up improvements are dramatic, in all cases at
 least one order of magnitude. We thus consider these results a first 
 step toward the creation of a feasible, sound migratory type system. 
