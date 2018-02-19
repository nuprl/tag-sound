#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Related Work}

@; -----------------------------------------------------------------------------

@; TODO
@; - "twin language" is special case of "multi-language"
@;   not sure if related work on soundness for N languages ... 

@parag{Gradual Typing}
In the broad sense, the term gradual typing@~cite[st-sfp-2006] describes
 any research that combines static and dynamic typing.
In the more precise sense defined by @citet[svcb-snapl-2015], a gradual typing
 system includes: (1) a dynamic type that may be implicitly cast to
 any other type; (2) a relation between types that are equal up to occurrences
 of the dynamic type; and (3) a proof that replacing any
 static type with the dynamic type can only affect the semantics of a term
 by removing a boundary error.


@parag{Migratory Typing}

Tobin-Hochstadt and Felleisen introduced the idea of migratory typing
 with Typed Racket@~cite[tf-dls-2006].
This led to a series of works on designing types to accomodate the idioms
 of dynamically-typed Racket; see @citet[tfffgksst-snapl-2017] for an overview.
Other migratory typing systems target
 JavaScript@~cite[bat-ecoop-2014],
 Python@~cite[vksb-dls-2014], and
 Smalltalk@~cite[acftd-scp-2013].


@parag{Gradual Typing Performance}

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


@parag{Type-Tag Soundness}

@; TODO colors are weird

@citet[vss-popl-2017] present a compiler from a statically-typed source language
 to a Python-like target language and prove a type-tag soundness theorem.
Using the ideas from the calculus, they implement a locally-defensive embedding
 of Reticulated (a statically typed variant of Python) into Python 3.
Their so-called transient semantics is the motivation for our work;
 we began by trying to implement a variant of their compiler for Typed Racket,
 but needed a deeper understanding of why the compiler was correct,
 what design choices were essential, and
 how the idea of rewriting statically-typed code related to other multi-language embeddings.

The idea of rewriting an expression to add explicit safety checks goes back
 at least to @citet[henglein-scp-1994], from whom we adopt the name @emph{completion}.


@;@parag{Space-Efficient Contracts}
@;
@;The forgetful embedding is due to Greenberg's semantics for space-efficient
@; manifest contracts@~cite[g-popl-2015].

@;@parag{Multi-Language Semantics}
@;@citet[mf-toplas-2007] introduce the first formal semantics for a multi-language.
@;
@; barret tratt
@; new ahmed
@; matthews-findler
@; gray findler flatt


@parag{Final Algebra Semantics}

The co-natural embedding is directly inspired by Findler and Felleisen's technique
 for higher-order contracts@~cite[ff-icfp-2002] and prior work on lazy contract checking@~cite[fgr-ifl-2007 dtw-pepm-2012].
We conjecture that this embedding could be viewed as a final algebra semantics@~cite[w-jcss-1979].
@; in contrast to the natural embedding.


@parag{Spectrum of Type Soundness}

Two related works led us towards the idea of a spectrum of type soundness.
@emph{Like types} are static type annotations that are erased before run-time@~cite[bfnorsvw-oopsla-2009 rzv-ecoop-2015].
Programmers can switch between like types and normal types to exchange
 soundness for performance without sacrificing any static type checking.

The @emph{progressive types} vision paper describes a type system in which
 programmers can decide whether certain errors are caught statically or dynamically@~cite[pqk-onward-2012].
This offers a choice between (1) statically proving an expression is universally correct,
 and (2) letting the run-time dynamically check whether the code is safe in practice.

