#lang gf-pldi-2018
@title[#:tag "sec:design"]{Five Embeddings}

@include-figure["fig:common-syntax.tex" @elem{Common syntax and semantics}]

The high-level goal of a type-directed embedding is to describe how three
 classes of values may cross language boundaries:
 (1) values of a base type,
 (2) ``finite'' values of a parameterized type,
 and (3) ``infinite'' values of a parameterized type.@note{By ``finite'' and ``infinite'', we refer to these values' observable behaviors.}
As representative examples, we use integers, pairs, and (anonymous, single-argument) functions.
Scaling an embedding to accomodate other types and values is typically straightforward,
 as we discuss in @section-ref{sec:implementation}.

To begin, @figure-ref{fig:common-syntax} introduces some common syntactic
 and semantic notions.
Expressions @${e} include variables, value forms, and the application of a
 function or primitive operation to arguments.
The unary primitive operations @${\vfst} and @${\vsnd} are projection functions for pair values;
 the binary primitives @${\vsum} and @${\vquotient} are integer arithmetic operators.

The semantics of the primitive operations is given by the @${\delta} meta-function.
In a real language, these primitives would be implemented by a runtime system
 that manipulates the machine representation of value forms.
As such, we treat calls to @${\delta} as cross-language function calls.
The result of such a function call is either a value, a token indicating
 a cross-language boundary error, or undefined behavior.

Undefined behavior due to @${\delta} is a categorical evil.
The baseline soundness requirement for our models is that they rule out
 programs that can lead to undefined behavior.

Other components in @figure-ref{fig:common-syntax} help define semantics.
An answer @${A} is either an expression or an error token.
Evaluation contexts @${E} impose a left-to-right, call-by-value order of evaluation.
Lastly, the meta-function @${\cclift{E}{\rrR}} lifts a
 notion of reduction@~cite[b-lambda-1981]
 over evaluation contexts in a way that detects and propagates errors.


@section{Source Languages}
@include-figure["fig:dyn-delta.tex" @elem{Dynamic Typing}]
@include-figure["fig:sta-delta.tex" @elem{Static Typing}]

The language @${\langD} defined in @figure-ref{fig:dyn-delta} is a
 dynamically-typed lambda calculus.
An @${\langD} expression @${e} is well-formed according to the typing judgment
 @${\GammaD \welldyn e} if it contains no free variables.
The notion of reduction @${\rrD} defines the semantics of well-formed expressions;
 in essence, it maps a valid application of values to a normal answer and
 maps an invalid application to a token representing a type-tag error@~cite[henglein-scp-1994].

The language @${\langS} in @figure-ref{fig:sta-delta} is a statically-typed
 counterpart to @${\langD}.
Types in @${\langS} describe four interesting classes of @${\langD} values:
 integers, natural numbers, pairs, and functions.
The type for natural numbers is representative of subset types@~cite[c-lp-1983]
 that do not have a matching low-level type tag.
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
Consequently, such expressions cannot send the evaluator to an undefined state.

@|D-SAFETY|
@;
@proof-sketch{
  By progress and preservation lemmas for the @${\welldyn} relation.
  In other words, @${e \ccD A} is defined for all well-formed expressions
   @${e} and if it maps @${e} to another expression, then the result is well-formed.
}

For @${\langS}, an analogous soundness theorem can guarantee that evaluation
 via @${\rrSstar} never leads to undefined behavior.
This is a useful property; however, there are two easy ways to strengthen it.
First, we can remove the @${\tagerror} clause because the reduction relation
 @${\ccS} never produces a type-tag error.
Second, we can prove that evaluation preserves types; if
 if an expression has type @${\tau} and evaluates to a value @${v}, then
 @${v} also has type @${\tau}.
This second enhancement differentiates @emph{strong type soundness} from
 @emph{weak type soundness} in the literature@~cite[type-soundness],
 and lets programmers use static type information to reason about the run-time
 behavior of programs.

@|S-SAFETY|
@;
@proof-sketch{
  By progress and preservation of the @${\wellsta \cdot : \tau} relation.
  Note that the only source of boundary errors is division by zero.
}

Proving type soundness for @${\langS} is relatively straightforward.
But once we allow @${\langS} expressions to contain arbitrary embedded @${\langD} expressions,
 it will be impossible to prove the same type safety theorem (because an
 @${\langD} expression can evaluate to a type-tag error).
The challenge is to find a useful notion of soundness that yields a practical
 implementation.


@; -----------------------------------------------------------------------------
@section{Multi-Language Syntax}
@include-figure["fig:mixed-delta.tex" @elem{Multi-Language @${\langM}}]

@Figure-ref{fig:mixed-delta} defines the syntax and typing rules of a
 multi-language for @${\langD} and @${\langS}.
The multi-language @${\langM} recursively extends the common syntax in @figure-ref{fig:common-syntax}
 with boundary expressions, combined value forms, and combined type contexts.
This language comes with two mutually-recursive typing judgments:
 a well-formedness judgment @${\Gamma \wellM e} for dynamically-typed expressions
 and a type-checking judgment @${\Gamma \wellM e : \tau} for statically-typed expressions.
Note that the typing rules prevent a dynamically-typed expression from
 directly referencing a statically-typed variable, and vice-versa.
Cross-language references must go through a @${\vdyn} or @${\vsta} boundary
 expression, depending on the context.

The definition of @${\langM} does not include a semantics.
This is intentional; the rest of this section will introduce @integer->word[NUM-EMBEDDINGS]
 alternative semantics, each with unique tradeoffs.

@Figure-ref{fig:mixed-delta} does, however, include a meta-function that
 defines two mutually-recursive reduction relations from two notions of reduction.
We use @${\DSlift{E}{\rrR}{E'}{\rrRp}}, or ``@${\rrR}-static bowtie-@${E} @${\rrRp}-dynamic'',
 to build: (1) a reduction relation @${\ccR} for statically-typed expressions,
 and (2) a reduction relation @${\ccRp} for dynamically-typed expressions.
The idea is that @${\ccR} applied to a statically-typed expression @${e} will
 apply @${\rrR} provided @${e} is not currently evaluating a boundary term;
 otherwise @${\ccR} will dispatch to the analogous @${\ccRp} and the two will
 flip-flop for nested boundaries.
The payoff of this technical machinery is that a statically-typed term @${e}
 cannot step via @${\ccR} to a type-tag error if @${e} does not embed
 dynamically-typed code.


@; -----------------------------------------------------------------------------
@section{The Erasure Embedding}
@include-figure["fig:erasure-delta.tex" "Erasure Embedding"]

If we can settle for a multi-language that avoids undefined behavior
 but does not guarantee any kind of type soundness, we can define a semantics
 in three easy steps.
First, let any statically-typed value pass into dynamically-typed code.
Second, let any dynamically-typed value pass into statically-typed code.
Third, base the evaluator on the dynamically-typed notion of reduction.

@Figure-ref{fig:erasure-delta} implements this @emph{erasure semantics} for
 the @${\langM} language.
The notion of reduction @${\rrEE} extends the dynamically-typed reduction to handle
 type-annotated functions and boundary expressions; it ignores the types.
There is no need to use the @${\bowtie} meta-function to define the evaluator;
 we just extend evaluation contexts to allow reduction under boundaries
 and take the appropriate closure of @${\rrEE}.
The typing judgment @${\Gamma \wellEE e} recursively extends the notion of
 a well-formed program to ignore any type annotations.
Using @${\Gamma \wellEE \cdot} as a run-time invariant, we can prove soundness for
 @${\langE}:

@|E-SAFETY|
@proof-sketch{
 By progress and preservation of @${\wellEE}.
}

Clearly, the erasure embedding is unsound with respect to static types.
One can easily build a well-typed expression that reduces to a value
 with a completely different type.
For example, @${(\edyn{\tint}{\vlam{x}{x}})}
 has the static type @${\tint} but evaluates to a function.
Worse yet, well-typed expressions may produce unexpected errors (a category I disaster),
 or silently compute nonsensical results (a category II disaster).
To illustrate this second kind of danger, recall the story
 of Professor Bessel@~cite[r-ip-1983]:

@blockquote{
  Professor Bessel announced that a complex number was an ordered pair of reals
  the first of which was nonnegative
}
@;
A student might use the type @${(\tpair{\tint}{\tnat})}
 to model (truncated) Bessel numbers and define a few functions based on the lecture notes.
Calling one of these functions with the dynamically-typed value @${\vpair{1}{-4}}
 may give a result, but probably not the right one!

Despite the lack of type safety, the erasure embedding has found increasingly widespread use.
For example,
 Hack@note{@url{http://hacklang.org/}},
 TypeScript@note{@url{https://www.typescriptlang.org/}},
 and Typed Clojure@~cite[bdt-esop-2016] implement this embedding@exact{\textemdash}by
 statically erasing types and re-using the PHP, JavaScript, or Clojure
 runtime.
@; @note{Anecdotal evidence of nasty TypeScript bugs from the @href["http://plasma.cs.umass.edu/"]{PLASMA group} at UMass.}

@; python annotations API @note{@url{https://www.python.org/dev/peps/pep-3107/}}
@; pluggable type systems @~cite[bracha-pluggable-types].


@; -----------------------------------------------------------------------------
@section{The Natural Embedding}

@include-figure*["fig:natural-delta.tex" "Natural Embedding"]

A type-safe embedding must check dynamically-typed values flowing in to typed contexts.
The natural way to implement checks is to interpret the boundary type as a checking scheme.
@; in essence, canonical forms
For base types, the check is typically straightforward.
For covariant type constructors, it suffices to check outermost type-tag
 of an incoming value and recursively check its components.
The recursive check is potentially expensive for large values, but it
 suffices to ensure type safety.

This ``inductive'' checking strategy fails, however, for higher-order values.
It is generally infeasible to check whether a run-time value @${v} is
 built from an expression with the static type @${(\tarr{\tau_d}{\tau_c})}.
@; TODO awkward
More broadly, the same problem arises for any value with unknown size,
 such as a port that delivers an infinite stream of data.
The classic solution is
 to use a ``coinductive'' strategy and monitor such values@~cite[ff-icfp-2002].
For function types, this means the boundary type
 @${(\tarr{\tau_d}{\tau_c})} accepts any dynamically-typed function @${v}
 and signals a boundary error if a future application of @${v} produces
 a result that does not match the @${\tau_c} type.
Instead of checking that @${v} is well typed, the boundary monitors @${v}
 for any evidence that @${v} is not well typed.

@; TODO fixup
A type-safe embedding must also defend statically-typed
 functions against dynamically-typed arguments.
When a function crosses from static to dynamic, its future arguments
 must be monitored.

@Figure-ref{fig:natural-delta} implements a natural embedding by extending
 the multi-language with monitor values.
A function monitor @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})} associates a type to a value;
 new reduction rule ensure that applying the monitor to an argument is
 the same as applying the underlying value @${v} across two boundary expressions.
@; monitor at boundary is the same as a function

Monitor values establish a key invariant: every value in statically-typed
 code is either well-typed, or a monitor that encapsulates a dynamically-typed
 expression.
With this invariant and an appropriate typing rule for monitors, one can
 prove a type safety theorem that guaratees the absence of type errors in
 statically-typed code.

@|N-SAFETY|
@proof-sketch{
  By progress and preservation lemmas for the @${\Gamma \wellNE e : \tau} judgment.
  See the appendix for proof, and the full definition of the @${\rrNEstar} reduction relation.
  Intuitively, @${\rrNEstar} applies @${\ccD} in dynamically-typed code,
   @${\ccS} in statically-typed code, and uses boundary expressions to determine
   which is which.
}


@; -----------------------------------------------------------------------------
@section{Soundness vs. Performance}

The erasure and natural embeddings are opposites in terms of type soundness
 and performance.
The erasure embedding promises nothing in the way of type soudness,
 and lets values freely cross boundary expressions.
The natural embedding is ideally type sound (for a language that makes no
 attempt to connect run-time boundary errors to source-program boundary terms@~cite[tfffgksst-snapl-2017])
 but imposes a large performance overhead.
In the context of Typed Racket, Takikawa etal observed that a straightforward
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
This single layer of indirection may affect the inlining decisions in a JIT-compiled language;
 furthermore, layers of indirection accumulate as values repeatedly cross boundaries.
@; TODO really need to emphasize the N-levels,
@;  important to bring in the JIT, but not at the expense of de-emphasizing
@;  how important-important the wrapping is
Finally, the @emph{allocation} cost of building a monitor value at run-time
 may have significant implications for performance.

@Figure-ref{fig:natural-cost} summarizes the cost of checking a
 value in terms of the meta-variables @${C}, @${A}, @${I}, and @${O}.
The variable @${C} denotes the cost of a type-tag check, for example @${i \in \naturals}.
Similarly, the variable @${A} denotes the cost of allocating one function monitor.
It may be possible to estimate @${C} and @${A} without running the program.
The variables @${I} and @${O} denote the number of times a function value crosses a
 boundary and the number of times it is applied.
The values of @${I} and @${O} depend on the run-time behavior a program.

The embeddings in the following three sections address these costs systematically.
Consequently, they demonstrate that the erasure and natural embeddings lie on
 opposite ends of a spectrum between soundness and performance.


@; -----------------------------------------------------------------------------
@section{The Co-Natural Embedding}
@include-figure*["fig:conatural-delta.tex" "Co-Natural Embedding"]

The natural embedding checks values eagerly whenever possible.
Consequently, a boundary expecting values of type @${\tau} typically
 requires one type-tag check for each type constructor in the @${\tau} type.
For example, if @${\tau} is the pair type @${\tpair{\tint}{\tnat}} then a
 boundary expecting a value of type @${\tau} must perform three type-tag checks.

The exception to this linear-cost rule is the function type.
To check that a dynamically-typed value has type @${(\tarr{\tau_d}{\tau_c})},
 the natural embedding performs one type-tag check and allocates a monitor to
 delay checking the function's domain and codomain.

Therein lies the insight for a co-natural embedding strategy.
If a language has one monitor value for each parameterized type,
 then it can check any dynamically-typed value with (at most) one type-tag check and one
 monitor allocation.

@; TODO note no need to protect pairs???
@; ... well I guess its obvious enough

@Figure-ref{fig:conatural-delta} outlines the details for our multi-language
 as an extension of the natural embedding language @${\langN}.
The new value @${\vmonpair{(\tpair{\tau_0}{\tau_1})}{v}} monitors a pair value.
If @${v_m} is such a monitor, then every call @${(\efst{v_m})} checks that
 the first component of @${v} matches the @${\tau_0} type.

Proving natural type soundness for this embedding is straightforward.
For any expression @${e} with type @${\tau}, if @${e} evaluates to a value
 then the value has type @${\tau} --- either from first principles or because
 the value is a monitor.

@emph{Remark}:
whether the natural or co-natural embedding performs fewer type-checks in
 a particular program depends on its data access patterns.
For example, the following program is at the ``break even'' point between
 the two embeddings:

@${
\hfill
 (\vlam{(x:\tpair{\tint}{\tint})}{(\efst{x} + \efst{x})})
\hfill }

Suppose this function is invoked on a dynamically-typed pair of integers.
Under the natural embedding, the boundary-crossing will check both components
 of the pair --- even though the function only accesses the first component.
Under the co-natural embedding, the boundary-crossing will only check the tag.
The two calls to @${\vfst}, however, will both trigger a type check.
@emph{End Remark}


@; -----------------------------------------------------------------------------
@section{The Forgetful Embedding}
@include-figure*["fig:forgetful-delta.tex" "Forgetful Embedding"]

The second source of performance overhead in the natural embedding is the
 indirection cost of monitors.
Each time a function value crosses a boundary, it accumulates a new type-checking
 monitor.
The same holds true of pairs (or any co-variant, parameterized type) in the
 co-natural embedding.
Put another way, our type-safe embeddings are space-inefficient.

A direct way to remove the indirection cost is to keep only the most recent monitor.
When a boundary expecting type @${\tau} finds a value of the form
 @${\vmon{\tau}{v}}, we forget the old monitor and return @${\vmon{\tau'}{v}}.
We call this approach a forgetful embedding, based on Greenbergs similar proposal
 for space-efficient contracts.@note{Greenberg proposes three space-efficient
  contract calculi: forgetful, heedful, and eidetic. We use forgetful because
  it admits a monitor-free implementation.}

It is far less obvious that a forgetful embedding can provide any kind of type
 soundness, given that it neglects to enforce certain static types.
@;Moreover, collapsing monitors loses the one-to-one correspondence between
@; boundary-crossings and monitors that was present in the natural embeddings.
@; TODO ... I mean it wasn't obvious to me that soundness would work,
@;   and had to add some non-obvious reduction rules to do so (looing under monitors)

@; TODO
However is possible to prove the natural embedding soundness,
 namely that terms do not get stuck.

The intuition --- due to Greenberg --- is that a forgetful embedding can be type
 sound provided no expression depends on a value having a forgotten type.

To illustrate, consider the statically-typed expression @${(\vsum~1~\efst{x})}.
This expression is well-typed if the variable @${x} has the static type @${\tpair{\tint}{\tau}}
 for some type @${\tau}.
With the co-natural embedding, the run-time value of @${x} could be
 any statically type pair, or any monitor of the form @${(\vmonpair{(\tpair{\tint}{\tau})}{v})}
That @${v} could be a monitor.
If it is, there's only chance for errors; no chance that @${\deltaS} will get stuck.
@; TODO would also work for Nat, I don't think this "intuition" is helping anyone
For functions, need to check the original static domain and the codomain
 that the caller expects.
@; ok the intuition defs needs to be here

@; TODO call this a "forgetful final embedding"
@Figure-ref{fig:forgetful-delta} extends our multi-language with a forgetful
 embedding.
The syntax of value forms prevents nested monitors.
Consequently, there is no distinction between ${\fromdyn} boundaries and
 @${\fromsta} boundaries; both must check a value against a type.
The new reduction rules implement the checks necessary to prevent stuck states.
The reduction rules for pairs check the contents of a monitored pair against
 the expectations of the context.
The rules for applying a function check that the argument is within the function's
 domain, and introduce a boundary to check the function's codomain.
With the addition of typing rules for the collapsed monitors, one can
 show that forgetful satisfies a variant of natural type safety:

@|F-SAFETY|
@proof-sketch{By progress and preservation of the @${\wellFE} judgment. See appendix.}


@; -----------------------------------------------------------------------------
@section{Errors Matter!}

The type safety theorem for the forgetful embedding is nearly identical
 to the natural embedding type safety.
This gives the illusion that we have improved performance without any
 obvious loss.
In fact, type safety holds because the theorem suffers two significant limitations
 in our context.

First, the delayed type checking of monitors lets many values
 pretend to have an incorrect static type.
For instance, the value @${(\vmonpair{(\tpair{\tnat}{\tnat})}{\vpair{4}{-4}})}
 is well-typed in the co-natural embedding.
A statically typed function can return this value; the function's clients
 will only observe an error if they access the second component of this pair.@note{This
  kind of latent error is analogous to the pitfalls of undiscovered lazy
  computations in Haskell programs.}

Second, type safety says nothing about how a well-typed value may be used by
 an enclosing expression.
In a statically-typed language, the type of a value is a complete guarantee;
 any context must respect the type.
This is not true in the forgetful embedding.
The well-typed pair value @${(\vmonpair{(\tpair{\tnat}{\tnat})}{\vpair{-1}{\vlam{x}{x}}})}
 may be used as a pair of integers or a pair of functions depending on local type
 annotations and access patterns.

In short, the combination of monitor values and forgetful semantics
 takes the compositional reasoning property out of the static type system.


@; -----------------------------------------------------------------------------
@section{The Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-delta.tex" "Locally-Defensive Embedding"]

An embedding that combines the co-natural and forgetful strategies
 checks only type-tags at elimination forms.
For our multi-language, these elimination forms are function applications
 and pair accessors --- statically-typed functions need protection against arguments
 outside their domain, and statically-typed expressions need protection against
 values produced by dynamically-typed functions and pairs.

The @emph{type-tagging} system in @figure-ref{fig:well-tagged} precisely
 describes where tag checks are required.
The judgment @${\Gamma \wellKE e : K} holds if the expression @${e} has
 type-tag @${K} in the type context @${\Gamma}, where variables in @${\Gamma}
 are assumed to have the correct tag.
@; TODO why not just (x:K) in gamma? problem with boundaries?
A type-tag @${K} either corresponds to a type constructor, or represents
 a dynamically-typed value with an unknown tag.
The meta-function @${\tagof{\cdot}} maps a type to its tag.

Few well-typed terms are well-tagged.
So introduce check form to make it so.
@;The type system ensures that:
@; (1) functions make no assumptions about their input, and
@; (2) elimination forms make no assumption about what result they will receive.
@;If a program type-checks using the rules in @figure-ref{fig:well-tagged},
@; then it is safe to evaluate without any instrumentation.
@;No monitors required.


@subsection{Automatic Completion}
@include-figure["fig:locally-defensive-completion-delta.tex" @elem{Completion (selected rules)}]

Queue from similar work by Vitousek and Henglein,
 time for completions.

Rather than force programmers to insert @${\vchk} expressions,
 we can better support the goals of migratory typing by statically rewriting
 programs.
See @figure-ref{fig:tagged-completion-delta} for the ideas, the appendix has the details.
@; WHAT IS IT
@; WHY NAMED THAT?
After Henglein, we call this @emph{completion}.

NOTE: (1) these checks are an overapproximation (2) our completion is not minimal.


@subsection{Type-Tag Soundness}

Bringing it all together, get soundness result for the multi-language.

@|K-SAFETY|

@emph{Remark}: we conjecture that for all source expressions @${e},
 the forgetful embedding and tagged embedding are observationally equivalent.
(Isn't there a simple class of counterexamples to rule out?)
At any rate they are similar to one another and very different from the
 natural embedding ... future work for readers:
 there should be a way to make this precise!
