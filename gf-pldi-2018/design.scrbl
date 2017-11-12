#lang gf-pldi-2018
@title[#:tag "sec:design"]{Models}

@section{Source Languages}

@include-figure["fig:source-lang.tex" @elem{Base languages, typing rules, and semantics}]

To begin, @figure-ref{fig:source-lang} presents two base languages.
Each is a lambda calculus with integers and pairs.
Language @${\langD} is dynamically typed; language @${\langS} is statically typed.
Their syntax is nearly identical, but @${\langS} functions require a type
 annotation on their parameter.

The types in @${\langS} describe four interesting classes of @${\langD} values:
 integers, natural numbers, pairs, and functions.
Abstractly, these types illustrate: (1) a base type, (2) a refinement of a
 base type, (3) a co-variant type constructor, and (4) a type for a higher-order
 value.
If a multi-language embedding can handle these four examples, then it can
 scale to almost any type found in a non-dependent programming language.
See @section-ref{sec:implementation} for discussion of untagged unions,
 recursive types, and parametric polymorphism.

Both languages include a syntactic judgment that describes when an expression
 is well formed.
For @${\langS}, the judgment @${\Gamma \welldyn e} claims that the free
 variables in @${e} are bound in the set @${\Gamma}.
For @${\langS}, the stronger judgment @${\Gamma \wellsta e : \tau}
 claims that @${e} has the static type @${\tau} in type context @${\Gamma},
 and furthermore all sub-expressions of @${e} have an appropriate static type.

The semantics of each language is defined as the context closure
 of a simpler reduction relation.
The reduction relation is a partial function from expressions to answers;
 an answer @${A} is either an expression or an error token.
As the name ``dynamic typing'' suggests, the reduction relation for @${\langD}
 maps ill-typed expressions to a token indicating a type error.
For example, the application of any integer to any other value @${v} is an
 error, e.g. @${(2~v) \rrD \typeerror}.
The reduction relation for @${\langS} is undefined for such expressions.
There is no answer @${A} such that @${(2~v) \rrS A} is defined.

Naturally, there is an important connection between the well-formedness
 judgments and the semantics.
This can be characterized in an appropriate @emph{term safety} theorem for the languages.
For @${\langD} one can show that evaluation never reaches an undefined state:

@|D-SAFETY|

For @${\langS}, one can prove a stronger @emph{type safety} theorem that (1) rules out type errors
 and (2) states that types are preserved in evaluation.

@|S-SAFETY|

The embeddings will each have a safety theorem
 that falls somewhere between term safety and type safety.
@; gee are you finished with intro material yet????


@; -----------------------------------------------------------------------------
@section{Multi-Language Syntax}

@include-figure["fig:mixed-delta.tex" @elem{Multi-Language @${\langM}}]

@Figure-ref{fig:mixed-delta} defines the syntax and typing rules of a
 multi-language for @${\langD} and @${\langS}.
The multi-language @${\langM} extends the common syntax in @figure-ref{fig:source-lang}
 with boundary expressions, combined value forms, and combined type contexts.
The mutually-recursive well-formedness rules for @${\langM} control how an
 expression can mix static and dynamic typing.
Informally, an expression @${e} has type @${\tau} in context @${\GammaS},
 written @${\GammaS \wellM e : \tau}, if all statically-typed sub-expressions
 of @${e} are well-typed and all dynamically-typed sub-expressions are
 well-formed.
Note that the typing rules prevent a dynamically-typed expression from
 directly referencing a statically-typed variable.
Cross-context references must go through a boundary.

In order to turn this multi-language into an embedding,
 we need to instantiate the (partial) functions
 @${\fromdyn} and @${\fromsta} that transport values between static and dynamic contexts.
@; TODO we are NOT 'exploring' in section 3 of a PLDI submission!!!!!

@; ... should "recipe" go in the mixed-lang figure?
@; - static->dyn dyn->sta
@; - common reduction rules (but ... how to reference those later?)


@; -----------------------------------------------------------------------------
@section{The Erased Embedding}

@include-figure["fig:erased-delta.tex" "Type-Erased Embedding"]

The simplest @|EGOOD| pair of embedding functions lets any value cross any boundary:

@exact|{
  $\hfill\fromdyn(\tau, v) = v \hfill$

  $\hfill\fromsta(\tau, v) = v \hfill$
}|

Using these functions, @figure-ref{fig:erased-delta} defines an @emph{erased embedding}
 by extending
 the dynamically-typed reduction relation @${\rrD} with new cases for typed
 functions and boundary expressions.
@; TODO add note that need to update the old rule for applying non-function?
@;      ... does appendix take care about this?
The new rules simply ignore the types.

Clearly this embedding is not type safe.
One can easily build a well-typed expression that reduces to a value
 with a completely different type, for example @${(\edyn{\tint}{\vlam{x}{x}})}.
Worse yet, well-typed expressions may produce unexpected errors,
 or silently compute nonsensical results, for example when a function expecting
 a natural number is applied to an integer.
In short, erased types cannot be used to reason about program behavior.

@;@exact|{
@;$ ((\vlam{\tann{x}{\tnat}}{42 / (x + 1)})~\edyn{\tnat}{-1}) $
@;}|

Despite the lack of type safety, the erased embedding does satisfy a term
 safety theorem:
 for any expression @${e} such that @${\wellM e : \tau}, evaluation of
 @${e} never reaches an undefined state.
The proof follows by progress and preservation of the @${\Gamma \wellEE e}
 judgment sketched in @figure-ref{fig:erased-delta}.

@emph{Remark}:
An equivalent way to define the erased embedding is to first remove the type
 annotations and second re-use the dynamically-typed reduction relation.
This simple idea has found increasingly widespread use; see, for example,
 TypeScript, the Python annotations API, and Pluggable Type Systems.
@emph{End Remark}
@; TODO cite


@; -----------------------------------------------------------------------------
@section{The Natural Embedding}

@include-figure*["fig:natural-delta.tex" "Natural Embedding"]

A type-safe embedding must check dynamically-typed values flowing in to typed contexts.
The natural way to implement checks is to interpret the boundary type as a checking scheme.
@; in essence, canonical forms
For base types, the check is typically straightforward.
For covariant type constructors, it suffices to check outermost type-tag
 @; TODO cite appel
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
 @; TODO cite FF
 to use a ``coinductive'' strategy and monitor such values.
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
}


@; -----------------------------------------------------------------------------
@section{Soundness vs. Performance}
@include-figure["fig:natural-cost.tex" "Approximate cost of the natural embedding"]

The erased and natural embeddings are opposites in terms of type soundness
 and performance.
The erased embedding promises nothing in the way of type soudness,
 and lets values freely cross boundary expressions.
The natural embedding is ideally type sound (for a language that makes no
 attempt to connect run-time boundary errors to source-program boundary terms)
 @; TODO cite MT1/MT2
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
Consequently, they demonstrate that the erased and natural embeddings lie on
 opposite ends of a spectrum between soundness and performance.


@; -----------------------------------------------------------------------------
@section{The Co-Natural Embedding}
@include-figure["fig:conatural-delta.tex" "Lazy Embedding"]

Remove recursion from @${\delta} with a new kind of monitor.
Same strategy used for functions.
Easy in our functional language, difficult in general,
 need to add a new class of values with same API as the old,
 probably need to change the language.

@Figure-ref{fig:conatural-delta} extends the syntax of the functional language
 with monitors for pairs.
The @${\delta} relation is extended with the obvious cases to check the
 contents of monitored pairs at run-time.

Note, could be far more expensive than just checking the pair, consider a function
 that performs two reads.
The function is twice as slow with the new guards.

@exact|{
 $$(\vlam{(x:\tpair{\tint}{\tint})}{(\efst{x} + \efst{x})})$$
}|

But this is arguably bad style, requires two data stucture accesses as well.
Maybe a compiler should re-write (CSE) before inserting the tag checks.

Can prove a safety theorem much like natural safety.

@theorem["lazy safety"]{
  If @${\cdot \wellsta e : \tau} then @${\cdot \wellLE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrLEstar v} and @${\cdot \wellLE v : \tau}
}
@item{
  @${e \rrLEstar \typeerror}
}
@item{
  @${e \rrLEstar \valueerror}
}
@item{
  @${e} diverges
}
]

Same soundness, but different behaviors!
@emph{Type soundness} does not change by making checks lazy,
 it only delays value errors from "immediately at the boundary" to
 "only until access".
Allows somewhat latent type errors,
 but nothing serious because if an access happens to read a bad value,
 this will be reported.
No matter where it happens.
@; Gradual guarantee?


@section{The Forgetful Embedding}
@include-figure["fig:forgetful-delta.tex" "Forgetful Embedding"]

Adopt rationale proposed by Greenberg, contracts exist to make partial
 operations total.

@Figure-ref{fig:forgetful-delta} shows the changes to the delta relation.
Crossing boundaries collapses monitors.
Lost invariant about boundaries, so function application does extra checking.
Typing rules axiomative monitors.

Soundness is the same
@theorem["forgetful safety"]{
  If @${\cdot \wellsta e : \tau} then @${\cdot \wellFE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrFEstar v} and @${\cdot \wellFE v : \tau}
}
@item{
  @${e \rrFEstar \typeerror}
}
@item{
  @${e \rrFEstar \valueerror}
}
@item{
  @${e} diverges
}
]


@; -----------------------------------------------------------------------------
@section{What have we lost?}

Type soundness is the same.
No loss?
No no no no no.
There is loss.


@; -----------------------------------------------------------------------------
@section{The Tagged Embedding}
@include-figure["fig:tagged-delta.tex" "Tagged Embedding"]

After collapsing monitors, left with a small number of checks only within
 typed code.
Introduce a type system to clarify 

Can remove monitors by extending syntax as shown in @figure-ref{fig:tagged-delta}.
Has N parts.

Type system declares when a term is well-tagged.

Static rewriting converts a well-typed program to a well-tagged program
 by inserting checks in typed code.

Reduction relation implements the tag checking.

Intuition:
@itemlist[
@item{
  Typed code that @emph{reads} from a possibly-untyped value must tag-check
   the result.
}
@item{
  Typed values that receive @emph{writes} from possible-untyped contexts must
   be prepared to accept any kind of input.
}
]

For reads, the solution is to insert a check between a data structure and its clients.
For writes in the form of function application, the function must tag-check its input.
Other writes --- for example writes to a mutable data structure --- do not
 need to check their input provided the language runtime supports writing
 any kind of value to the data structure (should be no problem in a dynamically-typed language).

@;More efficient.
@;Loses codomain errors in untyped code.
@;Does more checks than necessary in typed code.

@; ... suffers all the problems of the lazy and forgetful,
@; ... gains significant performance?
