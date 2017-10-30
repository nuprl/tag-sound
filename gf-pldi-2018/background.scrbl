#lang gf-pldi-2018
@title[#:tag "sec:background"]{Migratory Typing through Language Interoperability}

@; TODO
@; - make sure Sec 1 lists all tradeoffs (???)
@;   also Sec 1, more guarantees = more optimization but apparently not much at stake
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


@section{Two Languages}

@include-figure["fig:dyn-lang.tex" @elem{Dynamically-typed @|L_D|}]
@include-figure["fig:sta-lang.tex" @elem{Statically-typed @|L_S|}]

@Figure-ref["fig:dyn-lang" "fig:sta-lang"] define two variations of a lambda calculus
 with integers and pairs.
Both languages come with an operational semantics defined in terms of a partial
 function over expressions, and both have a static "typing" judgment that
 holds for all expressions with a well-defined semantics.

@parag{Dynamic Typing}
The language @|L_D| is dynamically typed.
An @|L_D| expression is well-formed according to @|⊢_D| if it contains no free
 variables.
Any well-formed expression that is not a value can step via @|→_D| to either
 a well-formed expression, a type error, or a value error.
Type errors are caused by values with a bad shape,
 value errors are caused by partial primitive operations.
More formally, the language satisfies a safety theorem:

@theorem[@elem{@|L_D| safety}]{
  If @well-dyn{e} then either:}
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

@proof-sketch{
  @|→_D| is defined for all closed terms, and satisfies subject reduction
   for @|⊢_D|.
}


@parag{Static Typing}
The language @|L_S| includes types @${\tau} and extends the syntax of function
 values to include type annotations.
The static typing judgment @|⊢_S| uses these annotations to prove that an
 expression will not reduce to a type error.
Likewise, the reduction relation @|→_S| does not perform any type checks.
The safety theorem for @|L_S| states that evaluation preserves types and
 cannot end in a type error:@note{Don't care that @|L_S| is strongly normalizing.}

@theorem[@elem{@|L_D| safety}]{
  If @well-sta["e" "\tau"] then either:}
  @itemlist[
  @item{
    @sta*["e" "v"] and @well-sta["v" "\tau"]
  }
  @item{
    @${e} diverges
  }
  @item{
    @sta*["e" value-error]
  }
  ]

@proof-sketch{
  Progress and preservation.
}


@section{Multi-Language}

@section{Identity Embedding}

@section{Natural Embedding}

@section{Performance}

High-level comparison, I guess "low-level" compare FSM performance.

