#lang gf-icfp-2018
@title[#:tag "sec:design"]{Apples-to-Apples Logic and Metatheory}

@; TODO
@; - the multi-language approach
@; - natural, tag, erasure [[nothing else!]]
@; ? why do we call it embedding?
@; - A @mytech{migratory typing system} is XXX and must YYY

@; -----------------------------------------------------------------------------

In this section we equip one syntax for @mytech{mixed-typed programs} (@figure-ref{fig:multi-syntax})
 with one type system (@figure-ref{fig:multi-preservation}) and three semantics
 (sections @secref{sec:natural-embedding}, @secref{sec:locally-defensive-embedding},
 and @secref{sec:erasure-embedding}).
Each semantics satisfies a unique soundness condition.

@Figure-ref{fig:multi-syntax} presents the syntax.
The grammar for @${\exprdyn} defines an untyped host language; the
 grammar @${\exprsta} defines an explicitly-typed twin language.
Both expression languages, @${\exprdyn} and @${\exprsta}, describe a lambda
 calculus extended with integers, pairs, related primitive operations,
 and @emph{boundary terms}.
The @${\exprdyn} boundary term @${(\esta{\tau}{\exprsta})} embeds a
 typed expression in an untyped context.
Conversely, the @${\exprsta} boundary term @${(\edyn{\tau}{\exprdyn})} embeds
 a dynamically-typed expression; the type annotation @${\tau} describes the
 context's assumptions about the value of the embedded expression.

The syntax intentionally does not include recursive functions, arbitrary-length
 data structures, mutable values, or infinite values such as streams.
Incorporating these values and their types is straightforward given a strategy
 that handles basic values, immutable data structures, and anonymous functions.
See @secref{sec:implementation} for details.
@; simple as possible ... well I guess pairs could be immutable boxes

@Figure-ref{fig:multi-preservation} defines a type system for this
 surface language.
An expression @${e} is well-formed, written @${\cdot \wellM e}, if it
 has no free variables and all its embedded terms are well-typed.
An expression is well-typed, written @${\cdot \wellM \exprsta : \tau},
 if it has no free variables, does not apply a function or primitive operation
 to an argument outside its domain, and all its embedded terms are well-typed.

The challenge is to define a sound semantics for well-typed expressions.
Specifically, we are looking for a reduction relation @${\rastar} that provides:
@itemlist[
@item{
  @emph{soundness for a single language}: for expressions without boundary
   terms, the typing judgment in @figure-ref{fig:multi-preservation} is sound
   with respect to the reduction semantics;
}
@item{
  @emph{expressive boundary terms}: the static and dynamic twin languages can
   share values at any type;
  @; e.g. no rule (dyn t->t v) ==> error to prohibit sharing all function
}
@item{
  @emph{soundness for the pair of languages}: for all expressions,
   evaluation preserves some property, though it may be weaker than a standard
   notion of type soundness.
}
]
With these goals in mind, the following three subsections give strategies for
 embedding untyped expressions (@${\exprdyn}) within typed expressions (@${\exprsta})
 and vice-versa.
Each embedding is made of five basic ingredients:
 a notion of reduction @${\rrD} for dynamically-typed expressions;
 a notion of reduction @${\rrS} for statically-typed expressions;
 a function @${\vfromdyn} that imports a dynamically-typed value into a typed context;
 a function @${\vfromsta} that imports a statically-typed value into an untyped context;
 and a judgment form that is both implied by the typing judgment in
 @figure-ref{fig:multi-preservation} and sound with respect to a semantics derived from the
 four previous components.

The starting point for these embeddings is the @mytech{evaluation syntax}
 and @${\delta} function in @figure-ref{fig:multi-reduction}.
The syntax provides a uniform language for reduction relations:
 the expression grammar @${e} is the domain of evaluation,
 evaluation ends in either a value @${v} or error @${\eerr},
 and the order of evaluation is guided by contexts @${\ES}.
There are two kinds of error.
Since this is a multi-language system, a @mytech{boundary error} @${\boundaryerror}
 can occur when one language receives an incompatible value from another.
A @mytech{tag error} @${\tagerror} occurs when value of the wrong shape reaches
 an elimination form.
@; GAAAH
High level: boundary errors and tag errors both occur because of bad values;
 boundary error is from an impedence mismatch between languages,
 tag error is from a mismatch between components in one language.
Evaluation contexts have two levels.
A pure context @${\ebase} does not contain boundary terms;
 an evaluation context @${\esd} may contain boundary terms.
This distinction is important if the embedding has two notions of reduction
 for typed and untyped code.

The @${\delta} function assigns meaning to the primitives.
The primitives @${\vfst} and @${\vsnd} extract the first and second components
 of a pair value, respectively.
The primitive @${\vsum} adds integers and the primitive @${\vquotient} performs
 integer division.
Division by zero raises a boundary error because one language (math) received
 an incompatible value from another language (@${\exprdyn} or @${\exprsta}) 

@include-figure["fig:multi-syntax.tex" @elem{Twin languages syntax}]
@include-figure["fig:multi-preservation.tex" @elem{Twin languages static typing judgments}]
@include-figure["fig:multi-reduction.tex" @elem{Common semantic notions}]


@; -----------------------------------------------------------------------------
@section[#:tag "sec:natural-embedding"]{Natural Embedding}
@include-figure*["fig:natural-reduction.tex" "Natural Embedding"]
@include-figure*["fig:natural-preservation.tex" "Property judgments for the natural embedding"]

In order to provide some kind of type soundness, an embedding must restrict
 the dynamically-typed values that can flow into typed contexts.
A natural kind of restriction is to let a value @${v} cross a boundary
 expecting values of type @${\tau} only if @${v} matches the canonical forms
 of the static type, and raise a @${\boundaryerror} otherwise.
For base types, this requires a generalized kind of type-tag check.
For non-base types that describe finitely-observable values,
 this requires one tag check and a recursive check of the value's components.

This inductive checking strategy fails, however, for types that describe
 values with infinitely many observable behaviors, such as a function
  or an object.
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
 are wrapped in monitors.
Such wrappers check that dynamically-typed arguments match the function's
 static type.
Dynamically-typed functions that enter statically-typed code are wrapped
 in monitors to check the results they produce.
Monitor values establish a key invariant: every value in statically-typed
 code is either a well-typed value or a monitor that encapsulates a
 potentially-dangerous value.
This invariant yields a soundness like that of @${\langS}, in which only dynamically-typed
 code can raise a type-tag error.
@; TODO still unclear, this previous sentence

@theorem[@elem{@${\langE} type soundness}]{
  If @${\wellM e : \tau}
   then @${\wellNE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrNEstar v \mbox{ and } \wellNE v : \tau} }
    @item{ @${e \rrNEstar \ctxE{e'} \mbox{ and } e' \ccND \tagerror} }
    @item{ @${e \rrNEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@;
@proof-sketch{
  By progress and preservation lemmas for the @${\Gamma \wellNE \cdot : \tau} relation.
  The lack of type-tag errors in statically-typed code follows from the
   definition of @${\ccNS}.
}

@; TODO need to be explicit that TR compiles to R?

Typed Racket implements the natural embedding by compiling static types
 to contracts that check dynamically-typed code at run-time@~cite[tf-popl-2008].
Under the protection of the contracts, Typed Racket may replace certain primitive operations
 with faster, unsafe versions that are defined for a subset of the Racket value domain@~cite[stff-padl-2012].
This compilation technique can improve the performance of typed code.
 However, the overhead of checking the contracts is a significant problem in
 mixed programs@~cite[gtnffvf-jfp-2017 tfgnvf-popl-2016].


@; -----------------------------------------------------------------------------
@; TODO make new section? idk ... I like this as is and will like it better with simulation theorems
@section{Soundness vs. Performance}

The erasure embedding promises nothing in the way of type soudness,
 and lets values freely cross boundary expressions.
The natural embedding is ideally type sound@~cite[tfffgksst-snapl-2017]
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
  indirection may also affect inlining decisions.
  @; TODO does Spenser's work validate this?
  }
Finally, the @emph{allocation} cost of building a monitor value
 also adds to the performance overhead.

The following three embeddings address these costs systematically.
Consequently, they demonstrate that the erasure and natural embeddings lie on
 opposite ends of a spectrum between soundness and performance.



@; -----------------------------------------------------------------------------
@section[#:tag "sec:locally-defensive-embedding"]{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-reduction.tex" "Locally-Defensive Embedding"]
@include-figure*["fig:locally-defensive-preservation.tex" "Property judgments for the locally-defensive embedding"]

The final source of performance overhead in the natural embedding is the cost of
 allocating monitor values.
@; TODO probably incorrect, definitely too loose
To remove this cost, we must replace the run-time analysis that monitors implement with
 a static analysis that predicts where to insert soundness-enforcing run-time checks.
@; TODO trying to say two things at once ...
@;  1. a whole-program approach is needed (because need the whole typing derivation)
@;  2. want to weaken the soundness criteria

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
The type-tags @${K} represent integers, natural numbers, pairs, functions,
 and unknown values.
The meta-function @${\tagof{\cdot}} relates a type @${\tau} to a type-tag,
 and the subtyping relation @${K \subt K'} states when values of tag @${K}
 can safely be given to a context expecting values with a different tag.
@; TODO stop saying 'trivial' ... just use 'Any' at least
As for the typing system: (1) the rules for value constructors conclude
 with a non-trivial tag; (2) the rules for elimination forms require a non-trivial
 tag and conclude with the @${\kany} tag; and (3) the rules for @${\vdyn} and
 @${\vchk} conclude a non-trivial tag that is justified with a run-time check.

@; TODO horrible paragraph, rewrite this
@Figure-ref{fig:locally-defensive-delta} additionally defines a semantics for
 well-tagged expressions.
Crucially, dynamically-typed arguments
 to typed functions get tag-checked by the @${\mchk{K}{\cdot}} meta-function.
To prove that type-tag errors only
 occur in dynamically-typed code, we add the ``dummy'' boundary
 expressions @${(\edyn{\kany}{e})} and @${(\esta{\kany}{e})}.


@subsection{Check Completion}

Unlike our previous languages, there is a gap between static typing for
 the multi-language @${\langM} and the language @${\langK} in @figure-ref{fig:locally-defensive-delta}.
If an expression @${e} has the static type @${\tau} and the type-tag of @${\tau}
 is @${K}, it is not necessarily true that @${e} is well-tagged via the @${\wellKE} relation.

@; TODO check usage of 'completion'
We bridge this gap with a @emph{completion}@~cite[henglein-scp-1994] elaboration pass.
Informally, a completion takes a well-typed term @${\wellM e : \tau}
 and adds @${\vchk} forms to enforce the type-checker's assumptions against
 dynamically-typed pairs and functions.
Such an elaboration is sound if it maps well-typed expressions to
 a similar, well-tagged expressions.
For @${\langK}, the completion elaborator we use inserts checks to the three
 forms shown in @figure-ref{fig:locally-defensive-completion-delta} and
 otherwise folds over expressions.


@subsection{Type-Tag Soundness}

We state soundness for @${\langK} in terms of the static typing judgment
 of the mixed language and the semantics of @${\langK}.

@theorem[@elem{@${\langK} type-tag soundness}]{
  If @${\wellM e : \tau}
   and @${\tagof{\tau} = K}, then
   @${\wellM e : \tau \carrow e'}
   and
   @${\wellKE e' : K}
   and either:
@itemlist[
  @item{ @${e^+ \rrKEstar v} and @${\wellKE v : K} }
  @item{ @${e^+ \rrKEstar E[\edyn{\tau'}{e'}] \mbox{ and } e' \ccKD \tagerror} }
  @item{ @${e^+ \rrKEstar \boundaryerror} }
  @item{ @${e^+} diverges }
]}@;
@proof-sketch{
  The completion simply adds checks around every expression with type-tag
   @${\kany} to enforce the expression's static type.
  Soundness follows from progress and preservation lemmas for the @${\wellKE \cdot : K} relation.
}

@;Type-tag soundness is superficially different from soundness for the forgetful, final language @${\langF}; however,
@; we conjecture that the semantics are observationally equivalent.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:erasure-embedding"]{Erasure Embedding}
@include-figure["fig:erasure-reduction.tex" "Erasure Embedding"]
@include-figure["fig:erasure-preservation.tex" "Property judgments for the erasure embedding"]

Intuitively, we can create a multi-language that avoids undefined behavior
 but ignores type annotations
 in two easy steps.
First, let statically-typed values and dynamically-typed values freely cross boundary terms.
Second, base the evaluator on the dynamically-typed notion of reduction.

@Figure-ref{fig:erasure-delta} specifies this @emph{erasure semantics} for
 the @${\langM} language.
The notion of reduction @${\rrEE} extends the dynamically-typed reduction to handle
 type-annotated functions and boundary expressions.
Its definition relies on an extension of evaluation contexts
 to allow reduction under boundaries
 and takes the appropriate closure of @${\rrEE}.
The typing judgment @${\Gamma \wellEE e} extends the notion of
 a well-formed program to ignore any type annotations.
As a result, the soundness theorem for @${\langE} resembles that of @${\langD}.

@theorem[@elem{@${\langE} soundness}]{
  If @${\wellM e : \tau}
   then @${\wellEE e} and either:
  @itemlist[
    @item{ @${e \rrEEstar v} and @${\wellEE v} }
    @item{ @${e \rrEEstar \tagerror} }
    @item{ @${e \rrEEstar \boundaryerror} }
    @item{ @${e} diverges }
  ]
}@;
@;@proof-sketch{
@; By progress and preservation of @${\wellEE}.
@;}

Clearly, the erasure embedding completely lacks predictability with respect to static types.
One can easily build a well-typed expression that reduces to a value
 of a completely different type.
For example, @${(\edyn{\tint}{\vlam{x}{x}})}
 has the static type @${\tint} but evaluates to a function.
Worse yet, well-typed expressions may produce unexpected errors (a category I disaster)
 or silently compute nonsensical results (a category II disaster).

@; TODO remove this, silliness
To illustrate this second kind of danger, recall the classic story of
 Professor Bessel, who @emph{
  announced that a complex number was an ordered pair of reals
  the first of which was nonnegative}@~cite[r-ip-1983].
A student might use the type @${(\tpair{\tnat}{\tint})}
 to model (truncated) Bessel numbers and define a few functions based on the lecture notes.
Calling one of these functions with the dynamically-typed value @${\vpair{-1}{1}}
 may give a result, but probably not the right one.

Despite its disrespect for types, the erasure embedding has found increasingly widespread use.
For example,
 Hack, @;@note{@url{http://hacklang.org/}},
 TypeScript, @;@note{@url{https://www.typescriptlang.org/}},
 and Typed Clojure@~cite[bdt-esop-2016] implement this embedding by
 statically erasing types and re-using the PHP, JavaScript, or Clojure
 runtime.
@; @note{Anecdotal evidence of nasty TypeScript bugs from the @href["http://plasma.cs.umass.edu/"]{PLASMA group} at UMass.}

@; python annotations API @note{@url{https://www.python.org/dev/peps/pep-3107/}}
@; pluggable type systems @~cite[bracha-pluggable-types].
