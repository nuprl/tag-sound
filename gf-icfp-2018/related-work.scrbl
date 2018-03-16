#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Related Work}

@; purpose: fill out all the history of the 3 embeddings, and anything else

@; TODO
@; - add transparent proxies, chaperones ?

@; -----------------------------------------------------------------------------

@;Migratory typing in general and the embeddings in particular have an
@; intertwined history.
@;Since our work is the first unified presentation and implementation of these ideas,
@; it is important to acknowledge where they came from.


The idea of equipping a dynamically typed language with static type information
 is almost as old as dynamic typing@~cite[m-maclisp-1974].
Early work in this area focused on type inference strategies in the hope that all the dynamically-typed code could be replaced@~cite[s-popl-1981 wc-toplas-1997 agd-ecoop-2005].
Over the past decade, researchers changed focus to designing sound @emph{multi-language} systems@~cite[gff-oopsla-2005 st-sfp-2006 mf-toplas-2007].

@; oh sage ktgff-tech-2007

This works builds directly on Typed Racket, a migratory typing system for
 Racket developed by Tobin-Hochstadt and others@~cite[tf-popl-2008 tsth-esop-2013 tf-icfp-2010 tfdfftf-ecoop-2015 tfffgksst-snapl-2017].
Other migratory typing systems target
 JavaScript@~cite[bat-ecoop-2014],@note{See also, Flow: @url{https://flow.org/}}
 PHP,@note{Hack: @url{http://mypy-lang.org/}}
 Python@~cite[vksb-dls-2014],@note{See also, mypy: @url{http://mypy-lang.org/}}
 and Smalltalk@~cite[acftd-scp-2013].

Migratory typing is closely related to gradual typing@~cite[st-sfp-2006 svcb-snapl-2015].
Gradual typing begins with a static typing system and generalizes it to allow
 fine-grained combinations of typed and untyped code@~cite[gct-popl-2016];
 migratory typing begins with a dynamically typed language and designs a type
 system to accomodate its particular idioms.
A migratory typing system can be gradual, and a gradual typing system can be
 a migratory typing system.
@; though the latter is unlikely

@; In the broad sense, the term gradual typing@~cite[st-sfp-2006] describes
@;  any research that combines static and dynamic typing.
@; In the more precise sense defined by @citet[svcb-snapl-2015], a gradual typing
@;  system includes: (1) a dynamic type that may be implicitly cast to
@;  any other type; (2) a relation between types that are equal up to occurrences
@;  of the dynamic type; and (3) a proof that replacing any
@;  static type with the dynamic type can only affect the semantics of a term
@;  by removing a boundary error.

@; rtsf-oops-2013 ??? ruby type checker


@section{Natural Embedding}

@citet[mf-toplas-2007] introduce the name @emph{natural embedding} to describe
 a type-directed strategy for converting Scheme values to ML values and vice-versa.
Typed Racket@~cite[tf-dls-2006 tf-popl-2008], GradualTalk@~cite[acftd-scp-2013],
 and SafeTypeScript@~cite[rsfbv-popl-2015] are three migratory typing systems
 that implement the natural embedding.

@citet[nl-arxiv-2018] demonstrate that the natural embedding checks are ``natural''
 in a categorical sense.


@;@parag{Multi-Language Semantics}
@;@citet[mf-toplas-2007] introduce the first formal semantics for a multi-language.
@;
@; barret tratt
@; new ahmed
@; matthews-findler
@; gray findler flatt


@section{Erasure Embedding}

The erasure embedding is the original approach to migratory typing.
Both MACLISP and Common Lisp supported optional type annotations@~cite[m-maclisp-1974 s-lisp-1990].
The idea of pluggable type systems@~cite[bg-oopsla-1993] was a modern revival of optional typing.
And currently, at least four industry teams are maintaining optional typing / erasure embedding
 systems --- for JavaScript, PHP, and Python.

@; cmscgbwf-dls-2011

@section[#:tag "sec:related-work:locally-defensive"]{Locally-Defensive Embedding}

The locally-defensive embedding is distilled from Vitousek's transient semantics.
Vitousek developed transient to avoid the challenge of adding proxies that
 preserve object identity to the Python language@~cite[vksb-dls-2014].
Later work proved that the approach provided a constructor-level notion of
 soundness@~cite[vss-popl-2017] at relatively low cost to mixed-typed programs@~cite[gm-pepm-2018].

In this work, we use the name @emph{locally defensive} rather @emph{transient} because the
 latter conflates two of the three novel ideas that characterize the approach.
The first novel idea is to check only type constructors at a boundary.
The second is to forget typing obligations unless they are crucial to the
 soundness of the current context.
The third is to implement forgetful constructor checks with in-line assertions
 rather than monitors.
@; Each step individually leads to a different embedding ... appendix has 1/2 and 2/3

@; https://www.dartlang.org/dart-2

The idea of rewriting an expression to add explicit safety checks goes back
 at least to @citet[h-scp-1994], from whom we adopt the name @emph{completion}.


@section{Anti-Erasure Embedding}

The erasure embedding treats a mixed-typed program as an untyped program.
In principle, one could design a dual embedding that treats the whole program
 as typed by reconstructing types for untyped code.
Researchers have worked on variants of this @emph{reconstruction embedding}
 problem for decades with modest success.
There are two problems: the technical challenge of efficiently inferring
 precise types, and the ergonomic challenge of debugging using the inferred types.
By contrast it is usually much easier to figure out why a programmer-supplied
 type does not match programmer-supplied code.

@; am-popl-1991
@; hr-fpca-1995
@; ffkwf-pldi-1996
@; wc-toplas-1997
@; mff-popl-2006
@; hms-dls-2016
@; rch-popl-2012


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

@; Most papers with a type soundness theorem dress it up like Milners.

Two related works led us towards the idea of a spectrum of type soundness.
@emph{Like types} are static type annotations that are erased before run-time@~cite[bfnorsvw-oopsla-2009 rzv-ecoop-2015].
Programmers can switch between like types and normal types to exchange
 soundness for performance without sacrificing any static type checking.

The @emph{progressive types} vision paper describes a type system in which
 programmers can decide whether certain errors are caught statically or dynamically@~cite[pqk-onward-2012].
This offers a choice between (1) statically proving an expression is universally correct,
 and (2) letting the run-time dynamically check whether the code is safe in practice.
