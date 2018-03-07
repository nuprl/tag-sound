#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Apples-to-Oranges}

@; purpose: fill out all the history of the 3 embeddings, and anything else

@; -----------------------------------------------------------------------------

Migratory typing in general and the embeddings in particular have an
 intertwined history.
Our work is the first unified presentation and implementation of these ideas.

@; need to establish
@; - this is the related work section
@; - embeddings have long history
@; - we put something novel on top (reinforce, for reviewers)


@section{Migratory Typing}

The idea of equipping a dynamically typed language with static type information
 is nearly as old as dynamic typing.
Explain the references in the introduction.

This work is the direct descendant of Typed Racket@~cite[tf-popl-2008 tfffgksst-snapl-2017].
Typed Racket is the first sound migratory typing system (via the natural embedding)
 as has continued improving.
@;Tobin-Hochstadt and Felleisen introduced the idea of migratory typing
@; with Typed Racket@~cite[tf-dls-2006].
@;This led to a series of works on designing types to accomodate the idioms
@; of dynamically-typed Racket; see @citet[tfffgksst-snapl-2017] for an overview.
@;Other migratory typing systems target
@; JavaScript@~cite[bat-ecoop-2014],
@; Python@~cite[vksb-dls-2014], and
@; Smalltalk@~cite[acftd-scp-2013].

Migratory typing is closely related to gradual typing@~cite[st-sfp-2006 svcb-snapl-2015].
Gradual typing begins with a static typing system and generalizes it to allow
 dynamically typed code@~cite[gct-popl-2016];
 migratory typing begins with a dynamically typed language and designs a type
 system to accomodate its particular idioms.
@; In the broad sense, the term gradual typing@~cite[st-sfp-2006] describes
@;  any research that combines static and dynamic typing.
@; In the more precise sense defined by @citet[svcb-snapl-2015], a gradual typing
@;  system includes: (1) a dynamic type that may be implicitly cast to
@;  any other type; (2) a relation between types that are equal up to occurrences
@;  of the dynamic type; and (3) a proof that replacing any
@;  static type with the dynamic type can only affect the semantics of a term
@;  by removing a boundary error.


@section{Natural Embedding}

Typed Racket and other migratory typing systems implement the natural embedding.
The original formalization is from Matthews and Findler's multi-language semantics.
Other multi-language systems use the natural embedding.
The name is from Matthews and Findler, the idea goes back much further
 at least to work on typed FFIs.

@;@parag{Multi-Language Semantics}
@;@citet[mf-toplas-2007] introduce the first formal semantics for a multi-language.
@;
@; barret tratt
@; new ahmed
@; matthews-findler
@; gray findler flatt


@section{Erasure Embedding}

The erasure embedding is the original and most successful approach to migratory
 typing.
Goes back to MACLISP and Common Lisp.

TypeScript and Flow are popular erasure embeddings for JavaScript,
 Hack is an erasure embedding for PHP,
 and mypy is an erasure embedding for Python.

More precisely, the above are pluggable type systems.
A pluggable type system starts with a type-annotated program,
 checks the annotations,
 and compiles a host-language program.
This is slightly different from embedding.


@section{Locally-Defensive Embedding}

The locally-defensive embedding is distilled from Vitousek's transient semantics.
First, the history.
Vitousek developed transient to avoid the challenge of implementing proxies that
 preserve object identity.
This is just one of many nice properties in the implementation,
 its a very simple way to get some kind of soundness.
@;Transient is the motivation for our work;
@; we began by trying to implement a variant of their compiler for Typed Racket,
@; but needed a deeper understanding of why the compiler was correct,
@; what design choices were essential, and
@; how the idea of rewriting statically-typed code related to other multi-language embeddings.

Darts checked mode might implement a locally-defensive embedding.
We don't know of anything older.
As far as we know, it's an original Vitousek idea to address the
 challenges of migratory typing.

The idea of rewriting an expression to add explicit safety checks goes back
 at least to @citet[h-scp-1994], from whom we adopt the name @emph{completion}.


@section{Anti-Erasure Embedding}

The erasure embedding treats a mixed-typed program as an untyped program.
In principle, one could design a dual embedding that treats the whole program
 as typed by reconstructing types for untyped code.
Researchers have worked on variants of this @emph{reconstruction embedding}
 problem for decades with modest success.
There are two problems: the technical challenge of efficiently inferring
 precise types, and the ergonimic challenge of debugging using the inferred types.
By contrast it is usually much easier to figure out why a programmer-supplied
 type does not match programmer-supplied code.


@section{Theoretical Performance of Mixed-Typed Programs}

Space-efficient contracts.
Greenberg's semantics for space-efficient manifest contracts@~cite[g-popl-2015 g-tfp-2016].



@section{Practical Performance of Mixed-Typed Programs}

@citet[tfgnvf-popl-2016] introduce a method for systematically evaluating
 the performance of a gradual typing system.
They apply the method to Typed Racket and find that its performance is a serious
 problem.
@citet[bbst-oopsla-2017] apply the method to a tracing JIT back-end for a subset of Typed
 Racket and report order-of-magnitude improvements without sacrificing soundness,
 performance, or error messages.

@citet[gm-pepm-2018] apply the Takikawa evaluation method to Reticulated
 and find that the overhead of type-tag soundness is within 10x on their benchmarks.
@citet[mt-oopsla-2017] evaluate the performance of an object calculus and
 report that natural-embedding gradual typing can yield an efficient implementation
 if the language of types is restricted to a finite set of base types.
@citet[rat-oopsla-2017] demonstrate that an optimizing virtual machine for
 JavaScript@~cite[cf-ecoop-2016] can efficiently support a co-natural embedding
 when static types match the virtual machine's runtime types.


@parag{Alternative Soundness}

Most papers with a type soundness theorem dress it up like Milners.

Two related works led us towards the idea of a spectrum of type soundness.
@emph{Like types} are static type annotations that are erased before run-time@~cite[bfnorsvw-oopsla-2009 rzv-ecoop-2015].
Programmers can switch between like types and normal types to exchange
 soundness for performance without sacrificing any static type checking.

The @emph{progressive types} vision paper describes a type system in which
 programmers can decide whether certain errors are caught statically or dynamically@~cite[pqk-onward-2012].
This offers a choice between (1) statically proving an expression is universally correct,
 and (2) letting the run-time dynamically check whether the code is safe in practice.
