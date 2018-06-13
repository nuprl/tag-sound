#lang gf-icfp-2018
@title[#:tag "sec:related-work"]{Related Work}

@; Note: the evaluation in rzv-ecoop-2015 does not report the performance of
@;  code that does any run-time type checking

@; -----------------------------------------------------------------------------

The idea of equipping a dynamically typed language with static type information
 goes back at least to the compiler hints in MACLISP@~cite[m-maclisp-1974].
Early work focused on type reconstruction for dynamically-typed
 programs@~cite[s-popl-1981 wc-toplas-1997 agd-ecoop-2005].
Over the past decade, researchers turned to the problem of creating a
 multi-language system@~cite[gff-oopsla-2005]
 that provides a type soundness guarantee@~cite[st-sfp-2006 tf-dls-2006 mf-toplas-2007 kf-toplas-2010].
Recent work addresses stronger guarantees such as parametricity@~cite[ajsw-icfp-2017 isi-icfp-2017].


@section{Gradual Typing}

Migratory typing is closely related to gradual typing@~cite[st-sfp-2006 svcb-snapl-2015].
In the broad sense, the term gradual typing@~cite[st-sfp-2006] has come to describe
 any type system that allows some amount of dynamic typing.
In the precise technical sense@~cite[svcb-snapl-2015], a gradual typing
 system includes: (1) a dynamic type that may be implicitly cast to
 any other type; (2) a relation between types that are equal up to occurrences
 of the dynamic type; and (3) a proof that replacing any
 static type with the dynamic type can only (3a) remove a static type error
 or (3b) remove a run-time boundary error.
@; gradual guarantee proofs in : @~cite[lt-popl-2017 isi-icfp-2017 mt-oopsla-2017].

Ultimately, gradual typing and migratory typing have different goals.
Migratory typing always starts with a dynamically typed language, whereas gradual
 typing may begin with a static type system and add a dynamic type@~cite[cs-popl-2016 gct-popl-2016 lt-popl-2017].


@section{Concrete Types}

Thorn is a statically-typed language that allows dynamically-typed methods@~cite[bfnorsvw-oopsla-2009 wnlov-popl-2010].
In particular:
 every value in Thorn is an instance of a class;
 every value has a (concrete) type, i.e., the name of its class; and
 a method may be defined for a dynamically-typed argument, in which case
 the method uses a run-time subtype check before interacting with its argument.
This approach sacrifices expressiveness in favor of straightforward run-time checks.
@citet[rzv-ecoop-2015] apply the concrete approach to TypeScript and allow
 limited interaction with structurally-typed JavaScript objects;
 method calls are permitted, but typed and JavaScript objects
 cannot extend one another.@note{@citet[tsdtf-oopsla-2012] introduce
 @emph{opaque class contracts} to support mixed-typed class hierarchies.}
@citet[mt-oopsla-2017] develop a theory of concrete and gradual@~cite[svcb-snapl-2015]
 typing and present an efficient implementation.
Dynamic typing in Dart 2 is based on the concrete approach.@note{@url{https://www.dartlang.org/guides/language/sound-dart}, accessed 2018-05-10}


@section{Natural Embedding}

@citet[mf-toplas-2007] introduce the name @emph{natural embedding} to describe
 a type-directed strategy for converting between Scheme
 and ML values.
The name suggests that this inductive-checking, higher-order-wrapping technique
 is the obvious approach to the problem; indeed, earlier work on typed foreign-function
 interfaces@~cite[r-jfp-2008] and remote procedure calls@~cite[ok-popl-2003] used a similar approach.
@citet[nl-fscd-2018] provide a semantic justification; in brief, if an embedding
 allows untyped functions and is not equivalent to the natural wrapping strategy,
 then it cannot satisfy type soundness.


@section{Erasure Embedding}

@; NOT ERASURE, types affect behavior!
@; MACLISP@~cite[m-maclisp-1974] and Common Lisp@~cite[s-lisp-1990]
@;  accept optional type hints to guide compilation.

The erasure approach is better known as optional typing, and the idea
 dates back to Common Lisp@~cite[s-lisp-1990] and Strongtalk@~cite[bg-oopsla-1993].
Many languages now have optional type checkers.
@Figure-ref{fig:existing-systems} lists some examples;
 the pluggable type checkers for Java@~cite[ddems-icse-2011 pacpe-issta-2008]
 apply the same principles to a statically-typed host language.

@; @note{Dart 1.x, @url{https://v1-dartlang-org.firebaseapp.com/}, accessed 2018-05-10.}
@; @note{Dart 2.0, @url{https://www.dartlang.org/guides/language/sound-dart}, accessed 2018-05-10.}


@section[#:tag "sec:related-work:locally-defensive"]{Locally-Defensive Embedding}

The locally-defensive embedding is directly inspired by the transient semantics
 for Reticulated Python@~cite[vksb-dls-2014 vss-popl-2017], a migratory and
 gradual@~cite[svcb-snapl-2015] typing system for Python.
The transient approach begins with a surface language expression and elaborates
 into a typed intermediate language.
In other words, the main judgment has the form @${\Gamma \vdash e \carrow e' : \tau}
 where both @${e'} and @${\tau} are outputs.
At first we tried adapting this elaboration to Typed Racket, but struggled
 with the lack of a specification for the @${\carrow} judgment in
 terms of the surface language.
In particular, Reticulated has a dynamic type (@${\star}) and thus a more
 flexible notion of type boundary.
A true model of transient may insert run-time checks for different reasons than
 the twin-language model of @section-ref{sec:locally-defensive-embedding}.

@citet[h-scp-1994] introduces the name @emph{completion} to decribe an untyped
 expression annotated with explicit type constructor checks.
The completion judgment in @section-ref{sec:locally-defensive-embedding}
 is more precisely a type-directed coercion insertion judgment@~cite[b-types-1995 shb-icfp-2009].

The name ``locally-defensive'' is an attempt to separate specification from
 implementation, and to tease apart three design choices
 apparent in Reticulated@~cite[vksb-dls-2014] regarding boundary terms.
The first idea is to check only first-order properties at a boundary.
The second is to check a data structure or higher-order value against its
 dynamically-most-recent type and no previous types, thereby implementing
 @emph{forgetful} space-efficiency@~cite[g-popl-2015].
The third is to rewrite typed code instead of monitoring dynamically-typed values.


@section{Type Reconstruction}

While the erasure embedding converts typed code to untyped code,
 a @emph{reconstruction embedding} could convert all untyped code
 to typed code.
Researchers have worked on variants of this problem for decades.
Soft typing combines Hindley-Milner inference with a non-standard
 grammar of types@~cite[awl-popl-1994 wc-toplas-1997].
Set-based flow analysis infers a type based on values, primitive operations,
 and control-flow@~cite[h-lfp-1994 ffkwf-pldi-1996 mff-popl-2006 pmw-dls-2009
 hms-dls-2016 rch-popl-2012].
Still another method is to infer types from the completion of an untyped term;
 that is, from a term with all implicit constructor-checks made explicit@~cite[hr-fpca-1995].
In practice there are two major challenges to type reconstruction:
 quickly inferring precise types@~cite[mfsw-hosc-2005]
 and debugging type errors that involve the (potentially large) inferred types@~cite[tfffgksst-snapl-2017].


@section[#:tag "sec:related-work:performance"]{Performance of Mixed-Typed Programs}

@citet[htf-hosc-2010] propose a first solution to the (space) inefficiency of
 the natural embedding.
Other theoretical solutions address the issue for gradual typing@~cite[htf-hosc-2010 sw-popl-2010 sgt-esop-2009],
 and more generally for higher-order contracts@~cite[g-popl-2015].@note{@url{https://arxiv.org/abs/1604.02474}}

Recent work evaluates the performance of practical migratory typing systems.
@citet[aft-dls-2013] report the performance of mixed-typed Gradualtalk programs.
@citet[tfgnvf-popl-2016] introduce a systematic method for performance evaluation and
 report a high overhead for mixed-typed programs in Typed Racket.
@citet[bbst-oopsla-2017] demonstrate that a tracing JIT compiler can significantly
 reduce the overhead in Typed Racket.
@citet[mt-oopsla-2017] report excellent performance data for a
 @emph{concrete}@~cite[clzv-ecoop-2018] gradual typing system on their benchmarks.
@citet[rat-oopsla-2017] suggest integrating run-time type checks with
 the shape tests of an optimizing virtual machine.


@section{Type Soundness}

Soundness is an important property of any type system, as it relates
 ahead-of-time claims to run-time outcomes.
Soundness for migratory typing systems is furthermore an incredibly
 subtle property, as this paper demonstrates.
At least four prior works address aspects of the subtlety of soundness for
 a mixed-typed language.
The early work on Typed Racket@~cite[tf-dls-2006] explains why
 soundness for a pair of languages requires a more general theorem than
 soundness for a single language.
A @tt{like} type system@~cite[wnlov-popl-2010 rzv-ecoop-2015]
 allows the programmer to decide between enforced and erased types.
Confined gradual typing@~cite[afgt-oopsla-2014] offers a choice between
 a static type error and a run-time check in the natural approach.
Lastly, the progressive types@~cite[pqk-onward-2012] vision
 paper describes a type system with a tunable set of run-time errors.@note{By contrast, this paper makes an argument for ``preservation-ive types''.}
Removing one kind of error from the set makes the static type system more
 conservative.


@section{Comparing Gradual Typing Systems}

@citet[stw-pldi-2015] define three calculi for gradual typing and relate them with
 fully-abstract@~cite[p-tcs-1977] translations.
The three calculi provide identical soundness guarantees.
@;Recent work by @citet[kas-arxiv-2018] suggests that some calculi may lead to an
@; efficient implementation.

@(define kafka "KafKa")

@citet[clzv-ecoop-2018] study the relationship of four different designs of
object-oriented gradual typing. The paper presents a core language, dubbed
@|kafka|, which is implemented in .NET and provably type-sound.  The
comparison rests on four translations from the surface syntax to @|kafka|,
each of which formulates a different semantics of gradual typing.  Finally,
the paper applies the four semantics to examples, showing that the
resulting behaviors are distinct.

By contrast, this paper assigns three different semantics to one surface
language and proves soundness theorems that demonstrate how the three semantics
differ with respect to the kind of properties that the type system correctly predicts.
Furthermore, this paper presents the results of comparing the performance
of the three semantics, implemented for the same language and
exhaustively evaluated on the same benchmark suite.
