#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Related Work}

@; Note: the evaluation in rzv-ecoop-2015 does not report the performance of
@;  code that does any runtime type checking

@; -----------------------------------------------------------------------------

The idea of equipping a dynamically typed language with static type information
 goes back at least to MACLISP@~cite[m-maclisp-1974].
Early work in this area focused on type inference strategies in the hope that
 all the dynamically-typed code could be replaced@~cite[s-popl-1981
 wc-toplas-1997 agd-ecoop-2005].
Over the past decade, researchers turned to the problem of creating a
 multi-language system@~cite[gff-oopsla-2005]
 that provides a type soundness guarantee@~cite[st-sfp-2006 tf-dls-2006 mf-toplas-2007 gktff-sfp-2006].
Recent work addresses stronger guarantees, such as parametricity@~cite[ajsw-icfp-2017 isi-icfp-2017].

Migratory typing is closely related to gradual typing@~cite[st-sfp-2006 svcb-snapl-2015].
In the broad sense, the term gradual typing@~cite[st-sfp-2006] describes
 any type system that allows dynamically-typed code.
In the more precise sense@~cite[svcb-snapl-2015], a gradual typing
 system includes: (1) a dynamic type that may be implicitly cast to
 any other type; (2) a relation between types that are equal up to occurrences
 of the dynamic type; and (3) a proof that replacing any
 static type with the dynamic type can only (a) remove a static type error
 or (b) remove a run-time boundary error.
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
 JavaScript@~cite[bat-ecoop-2014 cvgrl-arxiv-2017],
 Lua@~cite[mmi-dyla-2014],
 Ruby@~cite[rtsf-oops-2013],
 PHP,@note{@url{http://hacklang.org/}, accessed 2018-03-10.}
 and Python.@note{@url{http://mypy-lang.org/}, accessed 2018-03-10.}
@citet[ddems-icse-2011] and @citet[pacpe-issta-2008] add pluggable type systems to Java.

The Dart language v1.x implements the erasure embedding,@note{@url{https://v1-dartlang-org.firebaseapp.com/}, accessed 2018-05-10.}
 however Dart 2.0 enforces types with run-time checks.@note{@url{https://www.dartlang.org/guides/language/sound-dart}, accessed 2018-05-10.}
Users have the option to disable the inserted checks, thereby trading soundness
 for performance.


@section[#:tag "sec:related-work:locally-defensive"]{Locally-Defensive Embedding}

The locally-defensive embedding is directly inspired by the transient semantics
 for Reticulated Python@~cite[vksb-dls-2014 vss-popl-2017], a migratory typing
 system for Python that includes a dynamic type (@${\star}) and type compatibility
 relation.
The transient approach begins with a surface language expression and elaborates
 into a typed intermediate language.
In other words, the main judgment has the form @${\Gamma \vdash e \carrow e' : \tau}
 where both @${e'} and @${\tau} are outputs.
At first we tried adapting the Reticulated elaboration to Typed Racket, but struggled
 with the lack of a precise specification for the @${\carrow} judgment in
 terms of the surface language.
In particular, the inclusion of a dynamic type lets Reticulated adopt a more
 flexible notion of boundary --- a true model of transient may insert run-time
 checks for different reasons than our multi-language model (@section-ref{sec:locally-defensive-embedding}).

@citet[h-scp-1994] introduces the name @emph{completion} to decribe an untyped
 expression annotated with explicit type constructor checks.
Our completion judgment is a kind of typed coercion; see @citet[shb-icfp-2009]
 for related work.

The name ``locally-defensive'' is an attempt to tease apart three design choices
 apparent in @citet[vksb-dls-2014] regarding typed/untyped boundaries.
The first is to check only first-order properties at a boundary.
The second is to check a data structure or higher-order value against its
 dynamically-most-recent type, and no previous types.
The third is to rewrite typed code instead of monitoring dynamically-typed values.


@section{Reconstruction Embedding}

Whereas the erasure embedding converts typed code to untyped code,
 in principle a @emph{reconstruction embedding} could convert all untyped code
 to typed code.
Researchers have worked on variants of this problem for decades.
Soft typing systems combined Hindley-Milner inference with flexible kinds of types@~cite[awl-popl-1994 wc-toplas-1997].
@citet[ffkwf-pldi-1996], @citet[mff-popl-2006], @citet[hms-dls-2016], and @citet[rch-popl-2012]
 applied variants of set-based flow analysis@~cite[h-lfp-1994].
@citet[hr-fpca-1995] inferred types from the completion of an untyped term;
 that is, from a term with all implicit constructor-checks made explicit.
In practice there are two major challenges:
 quickly inferring precise types@~cite[mfsw-hosc-2005],
 and debugging type errors that involve the (potentially large) inferred types@~cite[tfffgksst-snapl-2017].


@section[#:tag "sec:related-work:performance"]{Performance of Mixed-Typed Programs}

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


@section{Comparing Gradual Typing Systems}

@citet[stw-pldi-2015] is the first work to rigorously compare gradual typing
 systems.
The paper defines three calculi for gradual typing and relates them with
 fully-abstract@~cite[p-tcs-1977] translations.
Unlike the migratory typing systems that have arisen in practice, the three calculi
 provide identical soundness guarantees.
@; Recent work by @citet[kas-arxiv-2018] suggests some calculi may lead to an efficient implementation.

@citet[clzv-ecoop-2018] study the relationship of four different designs of
object-oriented gradual typing. The paper presents a core language, dubbed
KafKa, which is implemented in .NET and provably type-sound.  The
comparison rests on four translations from the surface syntax to KafKa,
each of which formulates a different semantics of gradual typing.  Finally,
the paper applies the four semantics to examples, showing that the
resulting behaviors are distinct. 

By contrast, this paper assigns three different semantics to a surface
language. It then articulates soundness theorems about each of these
semantics; the theorems demonstrate how the three semantics differ with
respect to the kind of properties that the type system correctly predicts.
Furthermore, this paper presents the results of comparing the performance
of the three semantics, fully implemented for the same language and
exhaustively evaluated on the same benchmark suite.
