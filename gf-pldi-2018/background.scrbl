#lang gf-pldi-2018
@title[#:tag "sec:background"]{MT via Multi-Lang}

@; TODO
@; - make sure Sec 1 lists all tradeoffs (???)
@;   also Sec 1, more guarantees = more optimization but apparently not much at stake
@; - NEED TO CHANGE VARIABLE RULES ... cannot reference a static variable in dyn context and vice-versa
@; OUTLINE
@; - interop, boundary terms, guards
@; - identity embedding, dyn soundness
@; - natural embedding, type soundness
@; - extension to generalized datatypes
@;   * recur into structured values
@;   * monitor for "higher-order" values, e.g. writable
@; - silent failures! use the Reynolds example
@; - performance cost! plot results for typed racket
@; - TR vs Racket
@; - 

@; TR is "full guarantees" aka perfectly type sound,
@; TS is "full performance" aka no penalty for interaction
@;  I think penalty is the right way --- though low-level --- way to think
@;  about performance because then there's no question of optimizations,
@;  that's a separate question more tied to the guarantees

@; -----------------------------------------------------------------------------

The purpose of a migratory typing system is to enable safe interaction between
 dynamically-typed and statically-typed code.
Existing migratory typing systems meet this goal by combining a static typing
 judgment with a run-time verification system.
Intuitively, the typing judgment establishes certain invariants about typed
 expressions and the run-time verification asserts that untyped expressions
 flowing into typed contexts do not violate these invariants.

The key challenge in designing a migratory typing system is choosing
 a good notion of safety.
On one hand, the static typing judgment should accept many programs and offer
 strong guarantees.
On the other hand, the run-time verification should impose minimal performance
 overhead.
@; Examples with base values, lists, streams, anonymous functions?
@; Can reject these at the boundary, 

This section presents two migratory typing systems for a lambda calculus,
 these systems are respectively based on the natural and identity embeddings
 for a multi-language system.
At a high level, these systems illustrate the (extreme opposite) approaches taken by Typed Racket
 and TypeScript.


@section{Two Base Languages}

@Figure-ref["fig:dyn-lang" "fig:sta-lang"] define two variations of a lambda calculus
 with integers and pairs.
One language is dynamically typed, the other is statically typed.
Both languages come with an operational semantics defined in terms of a partial
 function over expressions, and both have a static "typing" judgment that
 holds for all expressions with a well-defined semantics.

@include-figure["fig:dyn-lang.tex" @elem{Dynamically-typed @|L_D| (fragment)}]

@parag{Dynamic Typing}
The language @|L_D| presented in @figure-ref{fig:dyn-lang} is dynamically typed.
An @|L_D| expression is well-formed according to @|well_D| if it contains no free
 variables.
Any well-formed expression that is not a value can step via @|step_D| to either
 a well-formed expression, a type error, or a value error.
Type errors are caused by values with a bad shape,
 value errors are caused by partial primitive operations.
More formally, the language satisfies a safety theorem:

@theorem[@elem{@|L_D| safety}]{
  If @well-dyn{e_D} then either:}
  @itemlist[
  @item{
    @dyn*["e_D" "v_D"] and @well-dyn{v_D}
  }
  @item{
    @${e_D} diverges
  }
  @item{
    @dyn*["e_D" type-error]
  }
  @item{
    @dyn*["e_D" value-error]
  }
  ]

@proof-sketch{
  @|step_D| is defined for all closed terms, and satisfies subject reduction
   for @|well_D|.
}


@include-figure["fig:sta-lang.tex" @elem{Statically-typed @|L_S| (fragment)}]

@parag{Static Typing}
The language @|L_S| includes types @${\tau} and extends the syntax of function
 values to include type annotations.
The static typing judgment @|well_S| uses these annotations to prove that an
 expression will not reduce to a type error.
Likewise, the reduction relation @|step_S| does not perform any type checks.
The safety theorem for @|L_S| states that evaluation preserves types and
 cannot end in a type error:@note{Don't care that @|L_S| is strongly normalizing.}

@theorem[@elem{@|L_S| safety}]{
  If @well-sta["e_S" "\\tau"] then either:}
  @itemlist[
  @item{
    @sta*["e_S" "v_S"] and @well-sta["v_S" "\\tau"]
  }
  @item{
    @${e_S} diverges
  }
  @item{
    @sta*["e_S" value-error]
  }
  ]

@proof-sketch{
  Progress and preservation.
}


@section{Migratory Typing}

Before we can run programs that combine dynamically-typed and statically-typed
 expressions, we need a syntax for mixed expressions.

@; ... boundary terms ...

@$|{
  \begin{array}{l c l}
    e_D & = & \ldots \mid \esta{\tau}{e_S}
  \\
    e_S & = & \ldots \mid \edyn{\tau}{e_D}
  \end{array}
}|


The new @|L_D| expression @embed-sta["\\tau" "e_S"] embeds a statically-typed
 expression into a dynamically-typed context.
The new @|L_S| expression @embed-dyn["\\tau" "e_D"] similarly embeds a
 dynamically-typed expression into a statically typed context.

Static typing for these expressions is straightforward, mutually-recursive
 (for suitable definition of @${\Gamma}):

@exact|{
\begin{mathpar}
  \inferrule{
    \Gamma \wellsta e_S : \tau
  }{
    \Gamma \welldyn \edyn{\tau}{e_S}
  }

  \inferrule{
    \Gamma \welldyn e_D
  }{
    \Gamma \wellsta \esta{\tau}{e_D} : \tau
  }
\end{mathpar}
}|


The semantics of these boundary terms should find a balance between allowing
 "safe" values to cross the boundary and disallowing mixes that lead to
 undefined behavior.
In this spirit, one bad choice for the semantics would be to disallow all
 mixed terms --- safe or unsafe --- by reducing all boundary terms to a value error.
Another poor choice would be to let any value cross a boundary and use
 the @|step_S| reduction relation on statically-typed terms.
This can easily lead to a stuck expression, for instance
 @$|{((\edyn{(\tint \tarrow \tint)}{0})~0)}|
 would reduce to the stuck application @${(0~0)}.


@subsection{Identity Embedding}

One approach to migratory typing is to let any value cross a type boundary
 and ignore the conclusions of the static type checker.
Put another way, this approach treats @|well_S| as an optional static analysis
 that can rule out bad expressions and has no relation to the semantics.

The semantics is an extension of the @|step_D| relation.
Very important not to use @|step_S| anymore.

@exact|{ \begin{mathpar}
  \inferrule*{
  }{
    \edyn{\tau}{v} \dynstep v
  }

  \inferrule*{
  }{
    \esta{\tau}{v} \dynstep v
  }

  %\inferrule*{
  %  e' = \vsubst{e}{x}{v}
  %}{
  %  (\vlam{(x:\tau)}{e})~v \dynstep e'
  %}
\end{mathpar} }|

Safety for an identity-embedded migratory typing system guarantees that
 well-formed expressions have a well-defined semantics.

@theorem[@elem{identity embedding term safety}]{
  If @well-sta["e" "\tau"] then either:}
  @itemlist[
  @item{
    @dyn*["e" "v"] and @well-dyn{v}
  }
  @item{
    @${e} diverges
  }
  @item{
    @dyn*["e" type-error]
  }
  @item{
    @dyn*["e" value-error]
  }
  ]

No other extensions needed.

This is the approach taken by TypeScript.
Simple to implement and explain, performs as well as dynamic typing.
The downside is that types cannot be used to reason about the behavior of
 expressions; it is entirely possible to give a well-typed function ill-typed
 inputs and have it (erronously) return a value.
@; Reynolds example?


@subsection{Natural Embedding}

The natural embedding uses boundary type annotations to check values at run-time.
@Figure-ref{fig:natural-embedding} presents a limited kind of natural embedding.
This version checks integer values, recursively checks pair values, and
 prevents functions from crossing.
With this semantics for boundary terms, it is possible to prove a nearly-conventional
 type safety theorem:

@theorem[@elem{natural embedding type safety}]{
  If @well-sta["e" "\\tau"] then either:}
  @itemlist[
  @item{
    @sta*["e" "v"] and @well-sta["v" "\\tau"]
  }
  @item{
    @${e} diverges
  }
  @item{
    @sta*["e" "e'"] and @dynstep["e'" type-error]
  }
  @item{
    @sta*["e" value-error]
  }
  ]

@include-figure["fig:natural-embedding.tex" "Natural Embedding"]

In particular, this safety guarantees the absence of type errors in statically
 typed code, but makes no guarantee about dynamically typed sub-expressions.

The trouble with function values is two-fold.
First, an untyped function used in a typed context might return a "bad" value.
Second, a typed function used in an untyped context might receive a "bad" value.

Maybe possible to type-check dynamically-typed functions when they enter typed
 code.
But probably not practical to check the context that receives a typed function.
So need another approach.
At any rate, the "exhaustively check" approach is also impractical for
 large objects (e.g., databases) or infinite objects (e.g., streams).
If the MT system wants to share such values, cannot provide "immediate accountability".

To allow functions across boundaries, we extend the language with new values
 that represent "monitored functions".
The reduction relation for a monitor ensures that it matches its type.
See @figure-ref{fig:natural-monitors} for the details.

@include-figure["fig:natural-monitors.tex" "Function Monitors"]


@section{Performance}

@include-figure["fig:natural-cost.tex" "Approximate Cost of Boundaries"]

The natural embedding lets programmers use types to reason about the behavior
 of mixed programs.
Clearly this power comes at some cost to performance.

The cost is difficult to statically estimate for two reasons.
First, the cost comes from checks, allocations, and indirections.
All three have non-obvious performance implications.
Especially indirections, which affect JIT compilation.
Second, the number of checks, allocations, and indirections depends on the
 run-time behavior of the program.

@Figure-ref{fig:natural-cost} is a sketch of the costs in terms of three
 meta-variables: @sc{check}, @sc{alloc}, and @sc{\#apps}.
A @sc{check} represents the cost of one run-time type test,
 basically the cost of checking a few bits.
An @sc{alloc} represents the cost of allocating a new monitor
 (probably depends on the type, but not represented here).
Lastly @sc{\#apps} represents the number of destructors applied to the
 value after it crosses a boundary.


@subsection{Typed Racket Performance}

Typed Racket implements a natural embedding of Racket terms.
Uses Racket's contract system to guard boundaries,
 boundaries are module boundaries described by require and provides.
Can think of this as, require and provide forms guide compilation from
 syntax in @figure-ref["fig:dyn-lang" "fig:sta-lang"] to a "mixed" core language.
(Technically its all Racket, but the boundaries separate "terms that were originally
 Typed Racket terms.)

Performance question.
For a Racket program with @${N} modules, there are @${2^N} ways to convert
 some modules to Typed Racket; call these @${2^N} configurations.
How many mixed programs run faster than Racket?
How many run at most @${D}x slower than Racket?

The graphs in @figure-ref{fig:tr-performance} show data for @|NUM-TR| Racket
 programs (source: Takikawa).
The y-intercept is the percent of configurations that run as fast as Racket.
Most benchmarks have a small area under the curve, which means few configurations
 run within even a @${@~a[X-MAX]} overhead.

@figure*["fig:tr-performance" "Typed Racket v6.10.1 performance"
  (overhead-plot* TR-DATA*)]
