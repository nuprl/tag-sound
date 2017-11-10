#lang gf-pldi-2018
@title[#:tag "sec:background"]{Migratory Typing via Language Embedding}

@; -----------------------------------------------------------------------------

The goal of migratory typing is to retrofit a static typing system to
 a dynamically-typed host language.
A well-designed migratory typing system provides some of the benefits of static
 typing at little cost to programmers.
Such benefits can include static detection of logical errors and guarantees
 about programs' run-time behavior.
The costs can include the human cost of writing type annotations
 and the performance overhead of enforcing static types at run-time.
@; I think this is in the ballpark

Existing migratory typing systems include
 @;StrongTalk,
 Typed Racket,
 TypeScript,
 and
 Reticulated.
@; ^^^ sorted by release date
These systems are diverse.
Each is tailored to a particular dynamically-typed host language
 and each offers different benefits to programmers.

There are, however, two unifying characteristics among existing migratory
 typing systems.
First, each system extends the syntax of the host language with support
 for type annotations.@note{In principle, migratory typing based on type
  inference does not require explicit annotations.
  Nevertheless, explicit annotations are a useful specification language
   and can help programmers debug type error messages.}
@; cite ML error
@; cite Wright's thesis
@; TODO say something better about "readability"
Second, each system is compatible with dynamically-typed code from the host
 language.
@; illustrate these?
A statically-typed TypeScript function, for example, may use JavaScript
 libraries to compute its result.

Consequently, a migratory typing system for a dynamically-typed host language @${\langD}
 consists of two parts:
 (1) a statically-typed language @${\langS},
 and (2) a typed foreign-function interface (FFI) between the languages.
The FFI must be able to import an @${\langD} value at a given type,
 and must be able to export a typed @${\langS} value to a dynamically-typed context.

In this paper we focus on the problem of designing an FFI for migratory typing.
Following Matthews and Findler, we refer to such FFIs as @emph{embeddings}.
We compare the type soundness guarantee of each
 embedding with the run-time cost of enforcing soundness.

@; @parag{Assumptions}
@; 1. boundaries are explicit in syntax
@; 2. no Dyn type, no type compatibility
@; 3. all values can cross boundary
@; 4. at least one infinite value
@; 5. type system makes finer distinctions than primops


@section{Multi-Language Syntax}




@; ABORT this is taking way too long, been like 5 hours with very little progress.
@; NOTES FOR LATER, the current plan is:
@; - describe goals/tradeoffs for an MT system (expressive, safe, performant)
@; - outline a mixed language
@;   * extra values (monitors)
@;   * extra expressions (embedding)
@;   * key design decisions
@; - natural embedding
@; - type-erased embedding
@; ....
@; PERHAPS want to move natural and type-erased to the next section,
@;  and put them all together in a "formal" section.
@; but get the technical stuff written first



The migratory typing problem is really a language interoperability problem.
Have two languages that want to safely share values.
The languages happen to be similar, but the essence
 is "how to share values" and "what does this mean for static reasoning".

@section{The Interoperability Problem}

The year is 200X.
Let D be a dynamically typed programming language
 that can express all kinds of values,
 ranging from integers to lists to first-class functions.
Programmers love the D and use it to build all kinds of applications.
They claim it is useful for rapid prototyping, testing poorly-specified ideas,
 and building flexible code.

Two years later, growing pains kick in.
Maintenance is a problem, difficult to edit existing code.
The unit test suite helps find breaking changes,
 but doesn't help with making changes or understanding how the codebase
 fits together.

Look, a formal specification is a good thing for any program.
A formal specification language is a good thing for any programming language
 --- to help programmers write "correct" formal specifications.

A group of designers builds S, a statically typed variant of D.
An S program is just a D program that contains type annotations.
The S compiler checks that these annotations are consistent with the program;
 the types are a lightweight checked specification language.

Although S makes it easy to retrofit static typing on D programs,
 developers want to re-use their existing D programs.
They want a DS foreign interface.
The two languages should interoperate.


@section{Expressiveness Safety Performance}

Three tradeoffs at play with the interoperability story.

Expressiveness : should be possible to share many kinds of values between
 D and S programs.

Safety : if D programs are safe and S programs are safe then
 DS mixed programs should be safe --- never reach an undefined state.
 Likewise if S has a type soundness theorem then analogous theorem
 should hold for the statically-typed parts of mixed programs.

Performance : mixed programs should suffer little overhead
 compared to pure-D programs and pure-S programs.

Hard to achieve all three.
Do we really need to illustrate here, how immediate accountability not
 possible in general.
Also, hey, all the uses of BIG data are from the outside world,
 so like there's an O(n) or a lazy step somewhere for S before even started
 on DS mixing.

@; -----------------------------------------------------------------------------

The key challenge in designing a migratory typing system is choosing
 a good notion of safety.
On one hand, the static typing judgment should accept many programs and offer
 strong guarantees.
On the other hand, the run-time verification should impose minimal performance
 overhead.

@; -----------------------------------------------------------------------------

The purpose of a migratory typing system is to enable safe interaction between
 dynamically-typed and statically-typed code.
Existing migratory typing systems meet this goal by combining a static typing
 judgment with a run-time verification system.
Intuitively, the typing judgment establishes certain invariants about typed
 expressions and the run-time verification asserts that untyped expressions
 flowing into typed contexts do not violate these invariants.

This section presents two migratory typing systems for a lambda calculus,
 these systems are respectively based on the natural and identity embeddings
 for a multi-language system.
At a high level, these systems illustrate the (extreme opposite) approaches taken by Typed Racket
 and TypeScript.


@section{Performance}

@;@include-figure["fig:natural-cost.tex" "Approximate Cost of Boundaries"]

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


@section{Summary, Glossary}

mixed
configuration
monitors
accountability

