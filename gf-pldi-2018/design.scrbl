#lang gf-pldi-2018
@title[#:tag "sec:design"]{Five Embeddings}

@include-figure["fig:common-syntax.tex" @elem{Common syntax and semantics}]

The goal of a type-directed embedding is to describe how three
 classes of values may cross language boundaries:
 (1) values of a base type,
 (2) finite values of a parameterized type,
 and (3) infinite values of a parameterized type.@note{By finite and infinite, we refer to these values' observable behaviors.}
As representative examples, we use integers, pairs, and (anonymous, single-argument) functions.
Scaling an embedding to accomodate other types and values is usually straightforward,
 as we discuss in @section-ref{sec:implementation}.

@Figure-ref{fig:common-syntax} introduces the common syntactic
 and semantic notions.
Expressions @${e} include variables, value forms, and the application of a
 function or primitive operation to arguments.
The unary primitive operations @${\vfst} and @${\vsnd} are projection functions for pair values;
 the binary primitives @${\vsum} and @${\vquotient} are integer arithmetic operators.

The semantics of the primitive operations is given by the partial @${\delta} function.
In a real language, these primitives would be implemented by a runtime system
 that manipulates the machine representation of values.
As such, we treat calls to @${\delta} as cross-language function calls.
The result of such a function call is either a value, a token indicating
 a cross-language boundary error, or undefined behavior.

Undefined behavior due to @${\delta} is a categorical evil.
The baseline soundness requirement for our models is that they rule out
 programs that can lead to undefined behavior.

Other components in @figure-ref{fig:common-syntax} help define semantics.
An answer @${A} is either an expression or an error token.
Evaluation contexts @${E} impose a left-to-right order of evaluation for the
 extension of this base with call-by-value functions.
Lastly, the meta-function @${\cclift{E}{\rrR}} lifts a
 notion of reduction@~cite[b-lambda-1981]
 over evaluation contexts in a way that detects and propagates errors@~cite[redex-book].


@section{Source Languages}
@include-figure["fig:dyn-delta.tex" @elem{Dynamic Typing}]
@include-figure["fig:sta-delta.tex" @elem{Static Typing}]

The language @${\langD} defined in @figure-ref{fig:dyn-delta} is
 dynamically-typed.
An @${\langD} expression @${e} is well-formed according to the typing judgment
 @${\GammaD \welldyn e} if it contains no free variables.
The notion of reduction @${\rrD} defines the semantics of well-formed expressions;
 in essence, it reduces a valid application of values to a normal answer and
 maps an invalid application to a token representing a type-tag error@~cite[henglein-scp-1994].

The language @${\langS} in @figure-ref{fig:sta-delta} is a statically-typed
 counterpart to @${\langD}.
Types in @${\langS} describe four interesting classes of @${\langD} values:
 integers, natural numbers, pairs, and functions.
The type for natural numbers is representative of subset types
 that do not have a matching low-level type tag@~cite[c-lp-1983].
Migratory typing systems must accomodate such types, because they have emerged
 in dynamically-typed programming languages.
An @${\langS} expression @${e} is well-typed if @${\GammaS \wellsta e : \tau}
 can be derived using the rules in @figure-ref{fig:sta-delta} for some type
 @${\tau}.@note{These typing rules are not syntax directed; see the PLT Redex
 models in our artifact for a syntax-directed implementation.}
The purpose of this typing judgment is to guarantee that all application forms
 apply a function and all primitive operations receive arguments for which
 @${\delta} is defined.
If this is true, then the notion of reduction @${\rrS} is defined for all
 well-typed expressions.

Both languages are sound in a precise sense.
For @${\langD}, soundness means that the evaluation of any well-formed expression
 either produces a valid answer or runs forever.
Expressions cannot send the evaluator to an undefined state.

@|D-SOUNDNESS|
@;
@proof-sketch{
  By progress and preservation lemmas@~cite[type-soundness] for the @${\welldyn} relation.
  In other words, @${e \ccD A} is defined for all well-formed expressions
   @${e} and if it maps @${e} to another expression, then the result is well-formed.
}

The analogous soundness theorem for @${\langS} guarantees
 that evaluation via @${\rrSstar} never leads to undefined behavior
 even though the reduction relation calls the partial @${\delta} function
 and never raises tag errors.
Additionally, we can prove that evaluation preserves types;
 if an expression has type @${\tau} and evaluates to a value @${v}, then
 @${v} also has type @${\tau}.
This enhancement allows programmers to use static type information to reason about the run-time
 behavior of programs.

@|S-SOUNDNESS|
@;
@proof-sketch{
  By progress and preservation of the @${\wellsta \cdot : \tau} relation.
  (The only boundary error is division by zero.)
}


@; -----------------------------------------------------------------------------
@section{Multi-Language Syntax}
@include-figure["fig:mixed-delta.tex" @elem{Multi-Language @${\langM}}]

@Figure-ref{fig:mixed-delta} defines the syntax and typing rules of a
 multi-language based on @${\langD} and @${\langS}.
The multi-language @${\langM} recursively extends the common syntax in @figure-ref{fig:common-syntax}
 with boundary expressions, combined value forms, and combined type contexts.
This language comes with two mutually-recursive typing judgments:
 a well-formedness judgment @${\Gamma \wellM e} for dynamically-typed expressions
 and a type-checking judgment @${\Gamma \wellM e : \tau} for statically-typed expressions.
Note that the typing rules prevent a dynamically-typed expression from
 directly referencing a statically-typed variable, and vice-versa.
Cross-language references must go through a @${\vdyn} or @${\vsta} boundary
 expression, depending on the context.

By intention, the definition of @${\langM} does not include a semantics.
The rest of this section introduces @integer->word[NUM-EMBEDDINGS]
 alternative semantics, each with unique tradeoffs.
@Figure-ref{fig:mixed-delta} does include a meta-function that
 defines two mutually-recursive reduction relations from two notions of reduction.
We use @${\DSlift{E}{\rrR}{E'}{\rrRp}}, pronounced ``@${\rrR}-static bowtie-@${E} @${\rrRp}-dynamic'',
 to build: (1) a reduction relation @${\ccR} for statically-typed expressions,
 and (2) a reduction relation @${\ccRp} for dynamically-typed expressions.
Informally, @${\ccR} applied to a statically-typed expression @${e}
 applies @${\rrR} provided @${e} is not currently evaluating a boundary term;
 otherwise @${\ccR} dispatches to the analogous @${\ccRp} and the two
 flip-flop for nested boundaries.
The payoff of this technical machinery is that a statically-typed term @${e}
 cannot step via @${\ccR} to a type-tag error if @${e} does not embed
 dynamically-typed code, which facilitates the proof of the soundness theorems.


@; -----------------------------------------------------------------------------
@section{The Erasure Embedding}
@include-figure["fig:erasure-delta.tex" "Erasure Embedding"]
@include-figure*["fig:natural-delta.tex" "Natural Embedding"]

Intuitively, we can create a multi-language that avoids undefined behavior
 but does not guarantee any kind of type soundness
 in two easy steps.
First, let statically-typed values and dynamically-typed values freely cross boundary terms.
Second, base the evaluator on the dynamically-typed notion of reduction.

@Figure-ref{fig:erasure-delta} specifies this @emph{erasure semantics} for
 the @${\langM} language.
The notion of reduction @${\rrEE} extends the dynamically-typed reduction to handle
 type-annotated functions and boundary expressions; it ignores the types.
Its definition relies on an extension of evaluation contexts
 to allow reduction under boundaries
 and take the appropriate closure of @${\rrEE}.
The typing judgment @${\Gamma \wellEE e} recursively extends the notion of
 a well-formed program to ignore any type annotations.
Using @${\Gamma \wellEE \cdot} as a run-time invariant, we can state a soundness theorem for
 @${\langE}:

@|E-SOUNDNESS|
@;@proof-sketch{
@; By progress and preservation of @${\wellEE}.
@;}

Clearly, the erasure embedding is unsound with respect to static types.
One can easily build a well-typed expression that reduces to a value
 with a completely different type.
For example, @${(\edyn{\tint}{\vlam{x}{x}})}
 has the static type @${\tint} but evaluates to a function.
Worse yet, well-typed expressions may produce unexpected errors (a category I disaster)
 or silently compute nonsensical results (a category II disaster).

To illustrate this second kind of danger, recall the classic story of
 Professor Bessel, who @emph{
  announced that a complex number was an ordered pair of reals
  the first of which was nonnegative}@~cite[r-ip-1983].
A student might use the type @${(\tpair{\tint}{\tnat})}
 to model (truncated) Bessel numbers and define a few functions based on the lecture notes.
Calling one of these functions with the dynamically-typed value @${\vpair{1}{-4}}
 may give a result, but probably not the right one.

Despite the lack of safety, the erasure embedding has found increasingly widespread use.
For example,
 Hack, @;@note{@url{http://hacklang.org/}},
 TypeScript, @;@note{@url{https://www.typescriptlang.org/}},
 and Typed Clojure@~cite[bdt-esop-2016] implement this embedding by
 statically erasing types and re-using the PHP, JavaScript, or Clojure
 runtime.
@; @note{Anecdotal evidence of nasty TypeScript bugs from the @href["http://plasma.cs.umass.edu/"]{PLASMA group} at UMass.}

@; python annotations API @note{@url{https://www.python.org/dev/peps/pep-3107/}}
@; pluggable type systems @~cite[bracha-pluggable-types].


@; -----------------------------------------------------------------------------
@section{The Natural Embedding}
@include-figure*["fig:conatural-delta.tex" "Co-Natural Embedding"]

In order to provide some kind of type soundness, an embedding must restrict
 the dynamically-typed values that can flow in to typed contexts.
A natural kind of restriction is to let a value @${v} cross a boundary
 expecting values of type @${\tau} only if @${v} matches the canonical forms
 of the static type.
For base types, this requires a generalized kind of type-tag check.
For parameterized types that describe finitely-observable values,
 this requires one tag check and a recursive check of the value's components.

This inductive checking strategy fails, however, for types that describe
 values with infinitely many observable behaviors, such as a function
  or a stream.
@;;For instance, it is generally impossible to check whether a run-time value @${v}
@;; matches a function type.
@;;@;@note{It may be possible
@;;@;  to dynamically check the type @${(\tarr{\tau_d}{\tau_c})} in a pure language
@;;@;  if @${\tau_d} describes a small number of values, but this check is impossible
@;;@;  in any language worth building a migratory typing system for.}
@;;The same problem arises for types such as @${(\mathsf{Stream}~\tau)} that
@;; describe infinite sources of data.
The classic solution is to use a coinductive strategy and monitor the
 future behaviors of values@~cite[ff-icfp-2002].
For function types, this means a boundary expecting values of type
 @${(\tarr{\tau_d}{\tau_c})} accepts any function value
 and signals a boundary error if a future application of that value produces
 a result that does not match the @${\tau_c} type.
Instead of finding a good reason that the value is typed,
 the language allows the value as long as there is no evidence that the value
 is not well-typed.

@Figure-ref{fig:natural-delta} specifies a natural embedding by extending
 the multi-language with function monitor values.
A monitor @${(\vmonfun{\tarr{\tau_d}{\tau_c}}{v})} associates a type to a value;
 new reduction rules ensure that applying the monitor to an argument is
 the same as applying the underlying value @${v} across two boundary expressions.
Statically-typed functions crossing into dynamically-typed code
 are also wrapped in monitors.
Such wrappers check that dynamically-typed arguments match the function's
 static type.

Monitor values establish a key invariant: every value in statically-typed
 code is either a well-typed value or a monitor that encapsulates a
 potentially-dangerous value.
This invariant yields a kind of type soundness that is nearly as strong
 as @${\langS} soundness.

@|N-SOUNDNESS|
@proof-sketch{
  By progress and preservation lemmas for the @${\Gamma \wellNE \cdot : \tau} relation.
  The lack of type-tag errors in statically-typed code follows from the
   definition of @${\ccNS}.
}

@; TODO need to be explicit that TR compiles to R?

Typed Racket implements the natural embedding by compiling static types
 to contracts that check dynamically-typed code at run-time@~cite[thf-popl-2008].
Under the protection of the contracts, Typed Racket may replace certain primitive operations
 with faster, unsafe versions that are defined for a subset of the Racket value domain@~cite[sthff-padl-2012].
This compilation technique can improve the performance of typed code.
 However, the overhead of checking the contracts is a significant problem in
 mixed programs@~cite[greenman-jfp-2017 tfgnvf-popl-2016].


@; -----------------------------------------------------------------------------
@section{Soundness vs. Performance}

The erasure embedding promises nothing in the way of type soudness,
 and lets values freely cross boundary expressions.
The natural embedding is ideally type sound (for a language that makes no
 attempt to connect run-time boundary errors to source-program boundary terms@~cite[tfffgksst-snapl-2017])
 but imposes a large performance overhead.
In the context of Typed Racket, Takikawa @|etal| observed that a straightforward
 implementation of the natural embedding can slow down a working program
 by two orders of magnitude.

At a high level, the performance overhead of the natural embedding comes from three sources:
  checking, indirection, and allocation.
By @emph{checking}, we refer to the cost of validating a type-tag and recursively
 validating the components of a structured value.
For example, checking a list structure built from @${N} pair values requires
 (at least) @${2N} recursive calls.
Function monitors add an @emph{indirection} cost.
Every call to a monitored function incurs one additional boundary-crossing.
If a value repeatedly crosses boundary terms, these type-checking layers
 can accumulate without bound.@note{In a language with a JIT compiler,
  layers of indirection may also affect inlining decisions.}
Finally, the @emph{allocation} cost of building a monitor value
 may lead to significant performance overhead.

The following three embeddings address these costs systematically.
Consequently, they demonstrate that the erasure and natural embeddings lie on
 opposite ends of a spectrum between soundness and performance.


@; -----------------------------------------------------------------------------
@section{The Co-Natural Embedding}
@include-figure*["fig:forgetful-delta.tex" "Forgetful Embedding"]

The natural embedding eagerly checks values that cross a type boundary.
For most values, this means that a successful boundary-crossing requires
 a linear-time traversal of the value's components.
The exception to this linear-cost rule is the function type.
To check that a dynamically-typed value matches a function type,
 the natural embedding performs a type-tag check and allocates a monitor.

In principle, an embedding can apply the same delayed-checking strategy to values
 of every parameterized type.
This reduces the cost of all boundary terms to at most
 one type-tag check and one monitor application.

@Figure-ref{fig:conatural-delta} gives the details of this @emph{co-natural}
 embedding as an extension of the natural embedding.
In total, this language @${\langL} has four kinds of value forms:
 integers, pairs, functions, function monitors, and pair monitors.
The reduction rules define how the projections @${\vfst} and @${\vsnd}
 act on pair monitors; in short, they act as projections across a boundary.
Finally when a pair value crosses a boundary, it gets wrapping in a checking
 (or protective) monitor.

From a theoretical standpoint, the change from a natural to a co-natural embedding
 delays error-checking until just before an expression would reach an undefined
 state.
The co-natural embedding is still type sound in the same sense as the natural embedding:

@|C-SOUNDNESS|
@proof-sketch{ Similar to the natural embedding. }
@; TODO actual link to appendix

There are expressions, however, that reduce to an error in the natural embedding
 and reduce to a value in the co-natural embedding; for instance
 @${(\vfst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{6}{-1}})})}.

The switch from eager to delayed run-time checks also affects performance.
Instead of checking the contents of a pair exactly once, at a boundary, the
 co-natural embedding described in @figure-ref{fig:conatural-delta} performs
 a check for each application of @${\vfst} or @${\vsnd}.
@;@citet[fgr-ifl-2007] have explored one method for dynamically reducing this cost.
@; ... for our purposes we just care about O(n) -> O(1) ???


@; -----------------------------------------------------------------------------
@section{The Forgetful Embedding}

%%% INTERLUDE
% - need to know typed functions under a monitor "have a typing"
% - because functions are delayed computations
% - and need to know that after substitution, they will compute _some result_ safely
%   (doesn't matter what the result it, just need to get there safely)
% ...
% - monitor annotations allowed to diverge because
%   Importing module doesn't know origin of value (looks untyped to me)

The second source of performance overhead in the natural embedding is the
 indirection cost of monitors.
Each time a function value crosses a boundary, it accumulates a new monitor.
Pair values in the co-natural embedding suffer the same overhead;
 a call to @${\vfst} may factor through an unbounded number of monitor wrappers.
To reduce the indirection cost, we need a way to collapse layers of monitors.

A simple, efficient, and type-sound way to reduce the indirection cost
 is to forget all but the most-recently-applied monitor@~cite[g-popl-2015].
When a boundary expecting type @${\tau} finds a value of the form
 @${(\vmon{\tau'}{v})}, drop the @${\tau'} monitor and return @${(\vmon{\tau}{v})}.
After all, if a function @${(\vlam{\tann{x}{\tau}}{e})} is well-typed,
 then the function body @${e} cannot depend on any properties of the old
 type @${\tau'} for soundness.

@Figure-ref{fig:forgetful-delta} presents a forgetful, final embedding that
 co-natural and forgetful monitoring strategies.
Intuitively, the only difference between the forgetful language @${\langF}
 and the language in @figure-ref{fig:conatural-delta}
 is that @${\langF} prevents monitors from stacking up.
The details in @figure-ref{fig:forgetful-delta} address the fact that monitors
 in @${\langF} no longer have a one-to-one correspondence with the type boundaries
 that a value has crossed.
In particular, if the value @${(\vmon{\tau}{v})} is in a dynamically-typed
 context, then @${v} is @emph{not} necessarily a statically-typed value.
@; TODO technically application should be "check type, substitute if OK",
@;      its not right to just substitute
We address this potential confusion in two steps.
First, when the evaluator applies a function monitor to an argument, it
 checks whether the call is crossing a type boundary.
If so, it interposes a @${\vdyn} or @${\vsta} boundary.
Second, the boundaries @${(\esta{\tau}{v})} and @${(\edyn{\tau}{v})}
 perform identical checks.
The @${\mchk{\tau}{\cdot}} meta-function factors out the common work of checking
 a value and dropping any existing monitor.

The language @${\langF} satisfies the same notion of soundness as the co-natural @${\langC}
 and the natural @${\langN}:

@|F-SOUNDNESS|
@proof-sketch{
  By progress and preservation of the @${\wellFE \cdot : \tau} relation.
  The key invariant is that if @${x} is a variable of type
   @${\tau}, then the forgetful semantics ensures that the value substituted
   for @${x} has the expected type.
  This value may be different from the value substituted by the natural semantics,
   but that distinction is not important for proving type soundness.
}

The forgetful embedding performs just enough run-time type checking to
 ensure that statically-typed code does not reach an undefined state, nothing more.

@;In short, the combination of monitor values and forgetful semantics
@; takes the compositional reasoning property out of the static type system.


@; -----------------------------------------------------------------------------
@section{The Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-delta.tex" "Locally-Defensive Embedding"]

The final source of performance overhead in the natural embedding is the cost of
 allocating monitor values.
To remove this cost, we must replace the run-time analysis that monitors implement with
 a static analysis that predicts where to insert soundness-enforcing run-time checks.

For a typical notion of type soundness in a language with
first-class functions, predicting such checks is impossible
 without a whole-program analysis.
The key insight is to pick a sufficiently weak notion of soundness@~cite[vss-popl-2017].
Our contribution is to demonstrate that this type-tag soundness arises systematically
 from the co-natural and forgetful embeddings.


@subsection{Monitor-Free Semantics}

The co-natural embedding decomposes deep checks at a boundary expression
 to one shallow check at the boundary and a set of shallow checks, one
 for each time the value is observed.
The forgetful embedding ignores the history of a value;
 local type annotations completely determine the type checks in a context.
Combining these two embeddings yields another semantics with
 local, defensive type-tag checks.
In @${\langF}, these defensive checks occur in exactly three kinds of expressions:
  (1) at boundary terms,
  (2) at function call and return, and
  (3) at calls to the projections @${\vfst} and @${\vsnd}.

We can statically determine whether an expression @emph{might} require a run-time check
 with a typing system that assumes any structured value can produce any kind
 of value.
Function applications @${(e_0\,e_1)} and projections @${(\efst{e})} in this
 system need a type that represents any kind of value.
In order to use these expressions in a context that requires a certain kind of
 value, for example @${(\esum{2}{\ehole})}, we add a form @${(\echk{K}{e})} to
 internalize the notion of a type-tag check.

@Figure-ref{fig:locally-defensive-delta} defines a typing system @${\Gamma \wellKE e : K}
 that makes these ideas precise.
To begin, type-tags @${K} represent integers, natural numbers, pairs, functions,
 and unknown values.
The meta-function @${\tagof{\cdot}} relates a type @${\tau} to a type-tag,
 and the subtyping relation @${K \subt K'} states when values of tag @${K}
 can safely be given to a context expecting values of a different tag.
As for the typing system: (1) the rules for value constructors conclude
 with a non-trivial tag; (2) the rules for elimination forms require a non-trivial
 tag and conclude with the @${\kany} tag; and (3) the rules for @${\vdyn} and
 @${\vchk} conclude a non-trivial tag that is justified with a run-time check.

@Figure-ref{fig:locally-defensive-delta} additionally defines a semantics for
 well-tagged expressions.
Crucially, dynamically-typed arguments
 to typed functions get tag-checked by the @${\mchk{K}{\cdot}} meta-function.
Also important for proving that type-tag errors only
 occur in dynamically-typed code is the addition of the ``dummy'' boundary
 expressions @${(\edyn{\kany}{e})} and @${(\esta{\kany}{e})}.
These expressions are a technical device to quarantine function bodies.


@subsection{Check Completion}
@include-figure["fig:locally-defensive-completion-delta.tex" @elem{Completion (selected rules)}]

Unlike our previous languages, there is a gap between static typing for
 the multi-language @${\langM} and the language @${\langK} in @figure-ref{fig:locally-defensive-delta}.
If an expression @${e} has the static type @${\tau} and the type-tag of @${\tau}
 is @${K}, it is not necessarily true that @${e} is well-tagged via the @${\wellKE} relation.

We bridge this gap with a @emph{completion}@~cite[henglein-scp-1994] function.
Informally, a completion function @${\carrow} takes a well-typed term @${\wellM e : \tau}
 and adds @${\vchk} forms to enforce the type-checker's assumptions against
 dynamically-typed pairs and functions.
Such a function is correct if it maps well-typed expressions to
 semantically-equivalent well-tagged expressions.

For @${\langK}, the completion function we use inserts checks to the three
 forms shown in @figure-ref{fig:locally-defensive-completion-delta} and
 otherwise folds over expressions.
We leave as open the question of how to define a completion function that
 generates the minimum number of @${\vchk} expressions.@note{@citet[henglein-scp-1994]
  defines a rewriting system that is provably optimal, but possibly non-terminating.}


@subsection{Type-Tag Soundness}

We state soundness for @${\langK} in terms of the static typing judgment
 of the mixed language and the semantics of @${\langK}.

@|K-SOUNDNESS|
@proof-sketch{
  The completion function simply adds checks around every expression with type-tag
   @${\kany} to enforce the expression's static type.
  Soundness follows from progress and preservation lemmas for the @${\wellKE \cdot : K} relation.
}

@;Type-tag soundness is superficially different from soundness for the forgetful, final language @${\langF}; however,
@; we conjecture that the semantics are observationally equivalent.
