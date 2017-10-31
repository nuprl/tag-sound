#lang gf-pldi-2018
@title[#:tag "sec:introduction"]{Three Tribes of Migratory Typing}

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

The recent history of the world of programming languages has been shaped by
 two fundamental truths.
The first truth is that current dynamically typed languages are effective
 tools for building applications.
The second truth is that static typing systems are useful for maintaining
 large applications.

A migratory typing system is a type system and runtime
 that combines statically-typed and dynamically typed code.
Unlike gradual typing, migratory typing systems do not include a type
 that is implicitly compatible with any other type.

Two tribes have developed migratory typing systems to combine the benefits
 of static typing and dynamic typing in a single language.
One tribe, Racketensis, embeds untyped code using a type-directed "natural" embedding.
Untyped values get type-checked at runtime, comprehensively.
The other tribe, Coffeeae, erases types; the embedding is the trivial identity embedding.

@; TypeScript invokes sneers from academic types, but has a growing following
@;  of JavaScript programmers.
@; Typed Racket inspires fear in Racket programmers.
@; Great divide between the two.
@; Desirable to bridge this gap, all depends on the context of the programmer.

In the great plains of Indiana we have uncovered a mutant strain of python
 that exhibits characteristics of both tribes albiet in restrained form.
Less soundness, less overhead.

Have refined this strain in the laboratory, and compared more thoroghly
 its characteristics with the Racket and JavaScript strains of migratory typing.
In particular, have a formal model with the essentials and an Typed Racket
 functional implementation.
Many programs can run in Racket to simulate all three tribes.

Now it may be that the mutant is a happy compromise.
Or may be, having none of the desirable traits from the dominant strains
 this brand fades into obscurity.
Nevertheless we present it to the scientific community.

Contributions:
@itemlist[
@item{
  formal model of the @emph{first-order embedding},
   statement and proof of @emph{type-tag soundness}
}
@item{
  systematic performance evaluation,
   performance of first-order embedding is huge improvement
}
@item{
  discussion of type-tag soudness, listing of surprising programs
   that are well-typed, incorrect, and potentially difficult to debug
}
]

This paper is organized as follows.
@Section-ref{sec:background} outlines the general problem of implementing a
 performant gradual type system, and compares the particular approaches taken by
 Typed Racket and Reticulated.
@Section-ref{sec:design} lists our design goals for tag-sound gradual
 typing and presents a formal model.
@Section-ref{sec:evaluation} compares the performance of Tagged Racket
 to Typed Racket.
@Section-ref{sec:conclusion} concludes.
