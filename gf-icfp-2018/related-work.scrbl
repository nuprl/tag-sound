#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Related Work}

@; -----------------------------------------------------------------------------

The idea of equipping a dynamically typed language with static type information
 is almost as old as dynamic typing@~cite[m-maclisp-1974].
Early work in this area focused on type inference strategies in the hope that
 all the dynamically-typed code could be replaced@~cite[s-popl-1981
 wc-toplas-1997 agd-ecoop-2005].
Over the past decade, researchers turned to the problem of creating a
 multi-language system@~cite[gff-oopsla-2005]
 that provides a type soundness guarantee@~cite[st-sfp-2006 tf-dls-2006 mf-toplas-2007 gktff-sfp-2006].

Migratory typing is closely related to gradual typing@~cite[st-sfp-2006 svcb-snapl-2015].
In the broad sense, the term gradual typing@~cite[st-sfp-2006] describes
 any type system that allows dynamically-typed code.
In the more precise sense@~cite[svcb-snapl-2015], a gradual typing
 system includes: (1) a dynamic type that may be implicitly cast to
 any other type; (2) a relation between types that are equal up to occurrences
 of the dynamic type; and (3) a proof that replacing any
 static type with the dynamic type can only affect the semantics of a term
 by removing a boundary error.
Ultimately, gradual typing and migratory typing have different goals;
 see @citet[gct-popl-2016].


@section{Natural Embedding}

@citet[mf-toplas-2007] introduce the name @emph{natural embedding} to describe
 a type-directed strategy for converting between (higher-order) Scheme values
 and ML values.
The name suggests that this inductive-checking, higher-order-wrapping technique
 is the obvious approach to the problem; indeed, earlier work on typed foreign-function
 interfaces@~cite[r-jfp-2008] and remote procedure calls@~cite[ok-popl-2003] used a similar approach.
For a semantic justification, see @citet[fb-flops-2006] and @citet[nl-arxiv-2018].
Typed Racket@~cite[tf-dls-2006 tf-popl-2008], GradualTalk@~cite[acftd-scp-2013],
 and @emph{TPD}@~cite[wmwz-ecoop-2017] are three migratory typing systems that implement the natural embedding.


@section{Erasure Embedding}

The erasure embedding, also known as optional typing or pluggable
 types@~cite[b-ordl-2004], is the oldest approach to migratory typing.
Strongtalk@~cite[bg-oopsla-1993] is an early, optional type checker for Smalltalk.
Modern optional typing systems exist for
 ActionScript@~cite[rch-popl-2012],
 Clojure@~cite[bdt-esop-2016],
 Dart,@note{@url{https://www.dartlang.org/}}
 JavaScript@~cite[bat-ecoop-2014 cvgrl-arxiv-2017],
 Lua@~cite[mmi-dyla-2014],
 Ruby@~cite[rtsf-oops-2013],
 PHP,@note{@url{http://hacklang.org/}}
 and Python.@note{@url{http://mypy-lang.org/}}
@citet[ddems-icse-2011] and @citet[pacpe-issta-2008] have implemented pluggable
 type systems for Java.


@section[#:tag "sec:related-work:locally-defensive"]{Locally-Defensive Embedding}

The locally-defensive embedding is directly inspired by the transient semantics
 for Reticulated Python@~cite[vksb-dls-2014 vss-popl-2017].
The transient approach begins with a surface language expression and elaborates
 into a typed core language.
In other words, the main judgment has the form @${\Gamma \vdash e \carrow e' : \tau}
 where both @${e'} and @${\tau} are outputs.
At first we tried adapting this compiler from Reticulated's expression-level
 migratory typing to Typed Racket's module-level gradual typing, but struggled
 with the lack of a precise specification for the @${\carrow} judgment.
The locally-defensive semantics thus separates surface-syntax typing (@figure-ref{fig:multi-preservation})
 from evaluation-syntax typing (@figure-ref{fig:locally-defensive-preservation});
 a suitable completion judgment (@${\carrow}) is one that inserts enough
 constructor checks into a typed surface expression to produce a constructor-typed
 expression.

@citet[h-scp-1994] introduces the name @emph{completion} to decribe an untyped
 expression annotated with explicit type constructor checks.
Our completion judgment is a kind of typed coercion; see @citet[shb-icfp-2009]
 for related work.

The name ``locally-defensive'' is an attempt to tease apart three ideas
 regarding typed/untyped boundaries.
The first is to check only first-order properties at a boundary.
The second is to check a higher-order value against its dynamically-most-recent
 type, and no previous types.
The third is to rewrite typed code instead of monitoring dynamically-typed values.


@section{Reconstruction Embedding}

Whereas the erasure embedding converts typed code to untyped code,
 in principle a @emph{reconstruction embedding} could convert all untyped code
 to typed code.
Researchers have worked on variants of this problem for decades.
Soft typing systems combined Hindley-Miler inference with flexible kinds of types@~cite[awl-popl-1994 wc-toplas-1997].
@citet[ffkwf-pldi-1996], @citet[mff-popl-2006], @citet[hms-dls-2016], and @citet[rch-popl-2012]
 applied variants of set-based flow analysis@~cite[h-lfp-1994].
@citet[hr-fpca-1995] inferred types from the completion of an untyped term;
 that is, from a term with all implicit constructor-checks made explicit.
In practice there are two major challenges:
 quickly inferring precise types@~cite[mfsw-hosc-2005],
 and debugging type errors that involve the inferred types@~cite[tfffgksst-snapl-2017].


@section{Performance of Mixed-Typed Programs}

Researchers quickly noticed the inefficiency of the natural embedding
 and proposed theoretical solutions both for gradual typing@~cite[htf-hosc-2010 sw-popl-2010 sgt-esop-2009],
 and for the more general context of higher-order contracts@~cite[g-popl-2015 g-tfp-2016].
Recent work has explored the practical performance of migratory typing systems.
@citet[aft-dls-2013] report the performance of mixed-typed Gradualtalk programs.
@citet[tfgnvf-popl-2016] introduce a systematic method for performance evaluation and
 report a high overhead for mixed-typed programs in Typed Racket;
 @citet[bbst-oopsla-2017] demonstrate that a tracing JIT compiler can significantly
 reduce this overhead.
@citet[mt-oopsla-2017] propose a new language in which all types are
 un-parameterized class names (i.e., atoms in an alphabet @${\Sigma}) and report
 low overhead for mixed-typed programs.
@citet[rat-oopsla-2017] suggest that runtime type tests should be integrated
 with the safety checks of the host language.


@section{Type Soundness}

@; Most papers with a type soundness theorem dress it up like Milners.

Three related works led us towards the idea of a spectrum of type soundness.
Like types are optional first-order types;
 a programmer can mark any such type as ``concrete'' or ``like'' to enable
 or disable run-time enforcement@~cite[wnlov-popl-2010 rzv-ecoop-2015].
It is unclear, however what soundness means for like types.
Confined gradual typing@~cite[afgt-oopsla-2014] gives the programmer control
 over the implicit coercions that a gradual typing system would normally insert.
The progressive types@~cite[pqk-onward-2012] vision paper describes a type system in which
 programmers can decide whether certain errors are caught statically or dynamically.
This offers a choice between (1) statically proving an expression is universally correct,
 and (2) letting the run-time dynamically check whether the code is safe in practice.

