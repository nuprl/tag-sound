#lang gf-pldi-2018
@title[#:tag "sec:design"]{Temporary: Models Only}


See techreport for proofs and PLT Redex models.


@; -----------------------------------------------------------------------------
@section{Dynamic Typing}

@include-figure["fig:dyn-lang.tex" "Dynamic Typing"]

@Figure-ref{fig:dyn-lang} defines a simple functional language.
Value forms @${v} are integers, pairs, and anonymous functions.
@; choses to represent base values, read-only data, and higher-order data
Expressions @${e} consist of variables, constructors, function application,
 and primitive operation applications.
An expression @${e} is well-formed in variable context @${\Gamma}, written
 @${\Gamma \welldyn e}, if all free variables of @${e} are bound in the context.
The (total) function @${\delta} interprets primitive operations.
The reduction relation @${\rrD} maps closed expressions to answers @${A};
 an answer is either an expression, a token representing a type error,
 or a token indicating a boundary error.
@; TODO clarify boundary error, our view of \delta as a language boundary
The function @${\vevalD} defines the semantics of expressions in terms
 of the @${\rrD} relation.

The language in @figure-ref{fig:dyn-lang} is a minimal example of a "safe"
 programming language.
For any closed expression @${e}, the answer @${\vevalD(e)} is well-defined:

@theorem[@elem{term safety}]{
  If @${\cdot \welldyn e} then either:
  }
@itemlist[
@item{
  @${e~\rrDstar~v}
}
@item{
  @${e~\rrDstar~\typeerror}
}
@item{
  @${e~\rrDstar~\valueerror}
}
@item{
  @${e} diverges
}
]

@definition["divergence"]{
  An expression @${e} diverges if for all @${e'} such that @${e~\rrDstar~e'}
   there exists an @${e''} such that @${e'~\rrD~e''}
}

@proof-sketch{
  By progress and preservation lemmas for @${\cdot \welldyn e}
   and the @${\rrD} relation.
}


@; -----------------------------------------------------------------------------
@section{Static Typing}

@include-figure["fig:sta-lang.tex" "Static Typing"]

@Figure-ref{fig:sta-lang} defines a statically typed functional language.
Value forms @${v} are integers, pairs, and type-annotated anonymous functions.
Expressions @${e} consist of variables, constructors, function applications,
 and primitive operation applications.
Types @${\tau} describe non-negative integers, integers, pairs, and
 functions.
@; TODO explain why natural, why subtyping
An expression @${e} has type @${\tau} in type context @${\Gamma} if
 the judgment @${\Gamma \wellsta e : \tau} holds according to the (non-algorithmic)
 rules in @figure-ref{fig:sta-lang}.
The subtyping relation @${\subt} defines a kind of subset relation on types.
The @${\Delta} relation assigns types to primitive operations.
The partial function @${\delta} assigns meaning to primitive operations.
Note that this @${\delta} function does produce type errors.
Likewise, the reduction relation @${\rrS} maps expressions to expressions or
 boundary errors.
The function @${\vevalS} defines the semantics of expressions.

The language in @figure-ref{fig:sta-lang} is type safe.
If an expression is well typed, then the answer @${\vevalS(e)} is well-defined.

@theorem[@elem{type safety}]{
  If @${\cdot \wellsta e : \tau} then either:
}
@itemlist[
  @item{
    @${e~\rrSstar~v} and @${\cdot \wellsta v}
  }
  @item{
    @${e~\rrSstar~\valueerror}
  }
  @item{
    @${e} diverges
  }
]

@proof-sketch{
  By progress and preservation lemmas for the @${\cdot \vdash e : \tau}
   and @${\rrS} relations.
}


@; -----------------------------------------------------------------------------
@section{Migratory Typing, the syntax}

@include-figure["fig:mixed-lang.tex" "Syntax for the mixed language"]

@Figure-ref{fig:mixed-lang} defines the syntax and typing rules for a
 multi-language that combines @figure-ref["fig:dyn-lang" "fig:sta-lang"].
The boundary expression @${(\edyn{\tau}{e})} embeds a dynamically-typed expression
 @${e} within a statically-typed context.
The boundary expression @${(\esta{\tau}{e})} embeds a statically-typed expression
 in a dynamically-typed context.
In order to handle mixed terms, the typing judgments @${\Gamma \welldyn e} and
 @${\Gamma \wellsta e : \tau} are extended with mutually-recursive rules
 to handle boundary expressions.
The other typing rules carry over unchanged.
Note that the re-use of the old rules correctly prevents a statically-typed
 expression from referencing a variable bound by a dynamically-typed function.

@Figure-ref{fig:mixed-lang} does not define a semantics for the mixed
 language.
Intuitively a language could re-use @${\vevalD} for dynamically-typed expressions
 and @${\vevalS} for statically-typed expressions, but of course the real
 question is what to do with boundary expressions.
The following sections will describe five semantics, each with a safety
 theorem of the form:

@fake-theorem["safety"]{
  If @${\Gamma \wellsta e : \tau} then @good{e} and either:
}
@itemlist[
@item{
  @${e} reduces to a value @${v} such that @good{v}
}
@item{
  @${e} reduces to a well-defined error state
}
]

Safety for dynamically-typed expressions is analogous; just replace
 @${\Gamma \wellsta e : \tau} with @${\Gamma \welldyn e} and relax the definition
 of @emph{good} accordingly.
@; cite techreport ... TODO make a blog post about how to publish a tech report

@; TODO note about safety/expressiveness/performance

@;The semantics of these boundary terms should find a balance between allowing
@; "safe" values to cross the boundary and disallowing mixes that lead to
@; undefined behavior.
@;In this spirit, one bad choice for the semantics would be to disallow all
@; mixed terms --- safe or unsafe --- by reducing all boundary terms to a value error.
@;Another poor choice would be to let any value cross a boundary and use
@; the @|step_S| reduction relation on statically-typed terms.
@;This can easily lead to a stuck expression, for instance
@; @$|{((\edyn{(\tint \tarrow \tint)}{0})~0)}|
@; would reduce to the stuck application @${(0~0)}.


@; -----------------------------------------------------------------------------
@section{The Type-Erased Embedding}

@include-figure["fig:type-erased-embedding.tex" "Type-Erased Embedding"]

One straightforward way to define a semantics for the mixed language is to
 extend the reduction relation for dynamically typed expressions.
The new rules ignore the type annotations on function parameters and
 boundary expressions; see @figure-ref{fig:type-erased-embedding} for the details.

To prove that this semantics is @emph{term safe}, we define a judgment
 @${\Gamma \wellEE e} as an extension of the relation in @figure-ref{fig:dyn-lang}
 that checks whether an expression is closed.
After this addition, it is straightforward to prove that the evaluation
 of well-typed terms never reaches an undefined state:

@theorem["type-erased safety"]{
  If @${\cdot \wellsta e : \tau} then @${\cdot \wellEE e} and either:
}
@itemlist[
@item{
  @${e~\rrEEstar~v} and @${\cdot \wellEE v}
}
@item{
  @${e~\rrEEstar~\typeerror}
}
@item{
  @${e~\rrEEstar~\valueerror}
}
@item{
  @${e} diverges
}
]

This semantics is cleary not type safe.
One can easily build a well-typed expression that reduces to a value
 with a completely different type, for example @${(\edyn{\tint}{\vlam{x}{x}})}.
When ill-typed subterms are used in a larger context, it is possible for a
 well-typed program to fail in subtle ways because the static types
 are utterly meaningless at runtime:

@$|{\begin{array}{l}
  C = ((\vlam{\tann{x}{\tnat}}{\vquotient~42~(\vsum~x~1)})~\bullet)
\\
  e = \edyn{\tnat}{-1}
\\
  \cdot \wellsta C[e] : \tnat
\\
  C[e] \rrEEstar \valueerror
\end{array}}|

Worse yet, evaluation can "go wrong" without signaling an error.
For one example, consider what happens at runtime when a dynamically-typed
 context adds a negative number to a monotonically increasing counter.

@; TODO need more examples of silent failures

Note that an equivalent way to define the same semantics is translate expressions
 to the syntax in @figure-ref{fig:dyn-lang} by removing type annotations, then
 re-using the @${\rrD} reduction relation.
This alternative is similar to what TypeScript implements.
@; TODO cite
@; TODO and it influences the monitor-free design


@; -----------------------------------------------------------------------------
@section{The Natural Embedding}

@; TODO note somewhere that could get type soundness by NO SHARING,
@;      but laffer curve

@include-figure["fig:natural-embedding.tex" "Natural Embedding"]

@Figure-ref{fig:natural-embedding} extends the multi language with
 monitor values.
A monitor @${(\vmonfun{\tau}{v})} associates a value with a type.

@theorem["natural safety"]{
  If @${\cdot \wellsta e : \tau} then @${\cdot \wellNE e : \tau} and either:
}
@itemlist[
@item{
  @${e \rrNEstar v} and @${\cdot \wellNE v : \tau}
}
@item{
  @${e \rrNEstar \typeerror}
}
@item{
  @${e \rrNEstar \valueerror}
}
@item{
  @${e} diverges
}
]

In particular, this safety guarantees the absence of type errors in statically
 typed code, but makes no guarantee about dynamically typed sub-expressions.

@; May be possible to type-check dynamically-typed functions when they enter typed code.
@; Not practical to check the context that receives a typed function.


@; -----------------------------------------------------------------------------
@section{The Lazy Embedding}
@; TODO avoid saying "lazy", want to rename this

@include-figure["fig:lazy-embedding.tex" "Lazy Embedding"]

Remove recursion from @${\delta} with a new kind of monitor.
Same strategy used for functions.
Easy in our functional language, difficult in general,
 need to add a new class of values with same API as the old,
 probably need to change the language.

@Figure-ref{fig:lazy-embedding} extends the syntax of the functional language
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

@include-figure["fig:forgetful-embedding.tex" "Forgetful Embedding"]

Adopt rationale proposed by Greenberg, contracts exist to make partial
 operations total.

@Figure-ref{fig:forgetful-embedding} shows the changes to the delta relation.
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


@section{The Tagged Embedding}

@include-figure["fig:tagged-embedding.tex" "Tagged Embedding"]

@figure*["fig:tagged-extras" "Tagged Extras"
  @exact|{\input{fig:tagged-extras.tex}}|]

After collapsing monitors, left with a small number of checks only within
 typed code.
Introduce a type system to clarify 

Can remove monitors by extending syntax as shown in @figure-ref{fig:tagged-embedding}.
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
