#lang gf-pldi-2018
@title[#:tag "sec:design"]{Temporary: Models Only}


See techreport for proofs and PLT Redex models.


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
@;    for all @${e'} such that @${e~\rrDstar~e'}, there exists an @${e''}
@;     such that @${e'~~\rrD~~e''}
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

@Figure-ref{fig:mixed-lang} does not define a semantics.

@; TODO add recipe for an embedding?
@; TODO 


@;Before we can run programs that combine dynamically-typed and statically-typed
@; expressions, we need a syntax for mixed expressions.
@;
@;@; ... boundary terms ...
@;
@;@$|{
@;  \begin{array}{l c l}
@;    e_D & = & \ldots \mid \esta{\tau}{e_S}
@;  \\
@;    e_S & = & \ldots \mid \edyn{\tau}{e_D}
@;  \end{array}
@;}|
@;
@;
@;The new @|L_D| expression @embed-sta["\\tau" "e_S"] embeds a statically-typed
@; expression into a dynamically-typed context.
@;The new @|L_S| expression @embed-dyn["\\tau" "e_D"] similarly embeds a
@; dynamically-typed expression into a statically typed context.
@;
@;Static typing for these expressions is straightforward, mutually-recursive
@; (for suitable definition of @${\Gamma}):
@;
@;@exact|{
@;\begin{mathpar}
@;  \inferrule{
@;    \Gamma \wellsta e_S : \tau
@;  }{
@;    \Gamma \welldyn \edyn{\tau}{e_S}
@;  }
@;
@;  \inferrule{
@;    \Gamma \welldyn e_D
@;  }{
@;    \Gamma \wellsta \esta{\tau}{e_D} : \tau
@;  }
@;\end{mathpar}
@;}|
@;
@;
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
@;
@;
@;@subsection{Identity Embedding}
@;
@;One approach to migratory typing is to let any value cross a type boundary
@; and ignore the conclusions of the static type checker.
@;Put another way, this approach treats @|well_S| as an optional static analysis
@; that can rule out bad expressions and has no relation to the semantics.
@;
@;The semantics is an extension of the @|step_D| relation.
@;Very important not to use @|step_S| anymore.
@;
@;@exact|{ \begin{mathpar}
@;  \inferrule*{
@;  }{
@;    \edyn{\tau}{v} \dynstep v
@;  }
@;
@;  \inferrule*{
@;  }{
@;    \esta{\tau}{v} \dynstep v
@;  }
@;
@;  %\inferrule*{
@;  %  e' = \vsubst{e}{x}{v}
@;  %}{
@;  %  (\vlam{(x:\tau)}{e})~v \dynstep e'
@;  %}
@;\end{mathpar} }|
@;
@;Safety for an identity-embedded migratory typing system guarantees that
@; well-formed expressions have a well-defined semantics.
@;
@;@theorem[@elem{identity embedding term safety}]{
@;  If @well-sta["e" "\tau"] then either:}
@;  @itemlist[
@;  @item{
@;    @dyn*["e" "v"] and @well-dyn{v}
@;  }
@;  @item{
@;    @${e} diverges
@;  }
@;  @item{
@;    @dyn*["e" type-error]
@;  }
@;  @item{
@;    @dyn*["e" value-error]
@;  }
@;  ]
@;
@;No other extensions needed.
@;
@;This is the approach taken by TypeScript.
@;Simple to implement and explain, performs as well as dynamic typing.
@;The downside is that types cannot be used to reason about the behavior of
@; expressions; it is entirely possible to give a well-typed function ill-typed
@; inputs and have it (erronously) return a value.
@;@; Reynolds example?
@;
@;
@;@subsection{Natural Embedding}
@;
@;The natural embedding uses boundary type annotations to check values at run-time.
@;@Figure-ref{fig:natural-embedding} presents a limited kind of natural embedding.
@;This version checks integer values, recursively checks pair values, and
@; prevents functions from crossing.
@;With this semantics for boundary terms, it is possible to prove a nearly-conventional
@; type safety theorem:
@;
@;@theorem[@elem{natural embedding type safety}]{
@;  If @well-sta["e" "\\tau"] then either:}
@;  @itemlist[
@;  @item{
@;    @sta*["e" "v"] and @well-sta["v" "\\tau"]
@;  }
@;  @item{
@;    @${e} diverges
@;  }
@;  @item{
@;    @sta*["e" "e'"] and @dynstep["e'" type-error]
@;  }
@;  @item{
@;    @sta*["e" value-error]
@;  }
@;  ]
@;
@;@include-figure["fig:natural-embedding.tex" "Natural Embedding"]
@;
@;In particular, this safety guarantees the absence of type errors in statically
@; typed code, but makes no guarantee about dynamically typed sub-expressions.
@;
@;The trouble with function values is two-fold.
@;First, an untyped function used in a typed context might return a "bad" value.
@;Second, a typed function used in an untyped context might receive a "bad" value.
@;
@;Maybe possible to type-check dynamically-typed functions when they enter typed
@; code.
@;But probably not practical to check the context that receives a typed function.
@;So need another approach.
@;At any rate, the "exhaustively check" approach is also impractical for
@; large objects (e.g., databases) or infinite objects (e.g., streams).
@;If the MT system wants to share such values, cannot provide "immediate accountability".
@;
@;To allow functions across boundaries, we extend the language with new values
@; that represent "monitored functions".
@;The reduction relation for a monitor ensures that it matches its type.
@;See @figure-ref{fig:natural-monitors} for the details.
@;
@;@include-figure["fig:natural-monitors.tex" "Function Monitors"]
@;
@;
@;
@;
@;
@;
@;
@;
@;
@;@; =============================================================================
@;
@;
@;
@;
@;The identity embedding is unacceptable to programmers who want to use types
@; to reason about the behavior of their programs.
@;The natural embeddings is unacceptable to programmers with performance
@; requirements.
@;This section presents an embedding that represents a compromise.
@;In theory, this embedding has significantly better performance than the
@; natural embedding --- each boundary crossing and eliminator incurs one
@; near-constant time check.
@;The shallow performance cost enables an equally shallow safety theorem:
@; if you pay for tag checks, you can trust the type-tags of all values.
@;
@;In the natural embedding, type boundaries suffer three kinds of costs.
@;The costs are (1) checking a value, (2) allocating a monitor, and (3)
@; the indirection cost of monitors.
@;@; TODO what about the later checks for each monitor?
@;@;   this story is not really cohesive
@;We will systematically reduce these costs in three steps.
@;First we introduce new monitors to avoid traversing a data structure
@; at a type boundary.
@;Second we reduce indirection at the cost of "forgetting" past boundaries.
@;Third we remove monitors altogether with a rewriting scheme;
@; saves performance but loses error messages in untyped code.
@;
@;All this in the context of our lambda calculus (?).
@;
@;
@;@section{Lazy Boundary Checks}
@;
@;First we deal with the linear-time cost of checking pairs at a boundary.
@;The goal is to make this a near-constant cost.
@;No more recursion.
@;
@;Can apply the same strategy used for functions.
@;For functions we were forced to be lazy because it was impossible to check
@; exhaustively.
@;For pairs, laziness is the "right" choice.
@;(Okay maybe this version isn't performant. I don't know. But it's on the
@; road to a performant implementation.)
@;
@;Add new kind of value, new typing rules, new reduction relation.
@;Figure to demonstrate.
@;Instead of eagerly checking the pair, delay until reads.
@;
@;Note, could be far more expensive than just checking the pair, consider a function
@; that performs two reads.
@;The function is twice as slow with the new guards.
@;
@;@exact|{
@; $$(\vlam{(x:\tpair{\tint}{\tint})}{(\efst{x} + \efst{x})})$$
@;}|
@;
@;But this is arguably bad style, requires two data stucture accesses as well.
@;Maybe a compiler should re-write (CSE) before inserting the tag checks.
@;
@;@emph{Type soundness} does not change by making checks lazy,
@; it only delays value errors from "immediately at the boundary" to
@; "only until access".
@;Allows somewhat latent type errors,
@; but nothing serious because if an access happens to read a bad value,
@; this will be reported.
@;No matter where it happens.
@;
@;
@;@section{Forgetful Monitors}
@;
@;Previous step was uncontroversial in terms of soundness,
@; questionable in terms of performance.
@;Now going further, definitely to gain performance and lose something
@; of soundness (though the same theorem can be proved).
@;
@;New semantics for monitors, "mon mon" reduces to "mon".
@;This is the forgetful space-efficient semantics formalized by Greenberg.
@;
@;Quick discussion about how this is sound?
@;Probably obvious, but probably good to give intuition for the tech report proof.
@;
@;
@;@section{Removing Monitors}
@;
@;Another controversial step.
@;Replace monitors with inlined checks.
@;Only rewrite in typed code.
@;
@;Two rules:
@;@itemlist[
@;@item{
@;  Typed code that @emph{reads} from a possibly-untyped value must tag-check
@;   the result.
@;}
@;@item{
@;  Typed values that receive @emph{writes} from possible-untyped contexts must
@;   be prepared to accept any kind of input.
@;}
@;]
@;
@;For reads, the solution is to insert a check between a data structure and
@; its clients.
@;For writes in the form of function application, the function must tag-check
@; its input.
@;Other writes --- for example writes to a mutable data structure --- do not
@; need to check their input provided the language runtime supports writing
@; any kind of value to the data structure (should be no problem in a dynamically-typed language).
@;
@;More efficient.
@;Loses codomain errors in untyped code.
@;Does more checks than necessary in typed code.
@;
@;
@;@section{Further Improvements}
@;
@;@; trusted cod
@;@; already-checked dom (unify?)
@;
@;Redundant tag checks, remove.
@;Slogan is, @emph{you can trust the tags}.
