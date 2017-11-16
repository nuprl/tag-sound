#lang gf-pldi-2018
@title[#:tag "sec:evaluation"]{Performance Evaluation}

@; TODO
@; - table with "MAX OVERHEAD" and "T/B RATIO"
@; -----------------------------------------------------------------------------

Based on the models, the natural, locally-defensive, and erased embeddings occupy
 three unique points on a spectrum between soundness and performance.
To measure how these embeddings stack up in a realistic setting,
 we have implemented a locally-defensive embedding as an extension of Typed Racket.
Since Typed Racket implements a natural embedding, this lets us compare the three approaches:
@itemlist[
@item{
  the natural embedding, via Typed Racket;
}
@item{
  the locally-defensive embedding, via the prototype;
}
@item{
  and the erasure embedding, via Racket.
}
]


@section{Implementation Overview}
@; TODO pick a name for minimal confusion

Our implementation of the locally-defensive embedding exists as a fork of Typed Racket v6.10.1
 called @|LD-Racket|.
Whereas Typed Racket programs start with the language declaration @tt{#lang typed/racket},
 @|LD-Racket| programs start with @tt{#lang tagged/racket}.
@|LD-Racket| inherits the syntax and static type checker of Typed Racket.
@|LD-Racket| extends Typed Racket with type-to-tag compiler and a completion
 function for type-annotated programs.

The type-to-tag function compiles a representation of a static
 type to a Racket predicate that checks whether a value matches the type.
This function is the straightforward realization of the @${\tagof{\cdot}}
 function described in @section-ref{sec:implementation}.

The completion function traverses a well-typed program and inserts two kinds
 of checks.
To any function definitions, it adds one ``assert'' statement to defend the
 function body against arguments outside its domain.
It wraps any destructor calls with a similar assert to confirm that the destructor
 returned a well-tagged result.
@; TODO its "correctly tagged" , not well-tagged

The implementation is designed to support a functional subset of Racket;
 it is limited to the types modeled in @section-ref{sec:design} and @section-ref{sec:implementation}.
In particular it does not support Racket's class and object system.


@section{Evaluation Method}

The promise of migratory typing is that programmers can freely mix statically-typed
 and dynamically-typed code.
A performance evaluation of a migratory typing system must therefore give
 programmers a sense of the performance they can expect as they add static
 typing to a program.

To meet this goal, we measure the performance of all configurations of
 statically-typed and dynamically-typed code in a suite of Racket programs.
Since Typed Racket (and our prototype) allows module-level type boundaries,
 this means that a Racket program with @${N} modules has @${2^N} configurations.

To turn this raw data into a more direct message, we use the notion
 of a @deliverable{D} configuration from Takikawa etal.
A configuration
 is @deliverable{D} if its performance overhead relative to a fixed baseline configuration
 is at most @${D}.
The baseline we use is the performance of Racket.
We refer to this as the untyped configuration.
Its performance corresponds to an erasure embedding.

@emph{Remark}: the premise of the @deliverable{D} measure is that programmers
 have a fixed performance requirement.
Certain applications may have strict performance requirements and can
 only tolerate a 10% overhead, corresponding to @${D = 1.1x}.
Others may accept overhead as high as @${D = 10x}.
No matter the requirement, any programmer can instantiate @${D}, check whether
 the proportion of @deliverable{D} configurations is high enough to inspire
 confidence, and then decide whether to experiment with migratory typing.
@emph{End Remark}

The programs we use are adapted from the earlier work by Takikawa etal.
@; cite POPL JFP
Specifically, the programs we use are all those that do not use object-oriented
 features.
See the appendix for details and origins of each benchmark.

To measure performance, we ran each configuration @~a[NUM-ITERS] times on an
 unloaded Linux machine with two physical AMD Opteron 6376 processors@note{The Opteron is a NUMA architecture.}
 and 128GB RAM.
The CPU cores on each processor were all configured to run at
 2.30 GHz using the performance CPU governor.
We did not collect measurements in parallel.

We collected data using Racket v6.10.1.
An experimental setup and our collection scripts are available in our artifact.


@section{Results: Performance Overhead}
@figure*["fig:locally-defensive-performance"
         @elem{@|LD-Racket| (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample| )}
  (overhead-plot* (map list TR-DATA* TAG-DATA*))]

The plots in @figure-ref{fig:locally-defensive-performance} report the performance
 of Typed Racket (the natural embedding)
 and of @|LD-Racket| (the locally-defensive embedding)
 as two histograms.
In the plot for a benchmark @sc{b}, the data for Typed Racket is a blue line
 and the data for @|LD-Racket| is an orange line.
A point @${(X, Y)} on the line for Typed Racket says that @${Y}% of all Typed Racket configurations
 for the benchmark @sc{b} run at most @${X} times slower than Racket running
 the same code with all types erased.
The line for @|LD-Racket| is analogous.
Note that the @|x-axis| is log scaled; vertical tick marks appear at
 @${1.2}x, @${1.4}x, @${1.6}x, @${1.8}x, @${4}x, @${6}x, and @${8}x overhead.

The data for most benchmarks confirms that @|LD-Racket| is significantly more
 performant than @|TR|.
These benchmarks are @bm{sieve}, @bm{fsm}, @bm{suffixtree}, @bm{kcfa},
 @bm{snake}, @bm{tetris}, and @bm{synth}.
The improvement is most dramatic for @bm{synth}, in which the worst-case
 performance ovehead drops from @render-max-overhead['typed 'synth] to @render-max-overhead['tagged 'synth].
This happens because Typed Racket @bm{synth} spends a large amount of time
 eagerly traversing data structures and monitoring their components.
@; FSM also dramatic, removes huge indirection cost

The @bm{zombie} benchmark shows only a modest improvement.
In fact, @|LD-Racket| @bm{zombie} is a huge improvement over Typed Racket;
 the worst-case overhead in @|LD-Racket| is @render-max-overhead['tagged 'zombie]
 compared to @render-max-overhead['typed 'zombie] in @|TR|.
This improvement, however, is unlikely to convince a programmer than migratory
 typing is ready for production use.

The @bm{morsecode} benchmark is an anomaly.
Using @|LD-Racket| doubles the overhead of the slowest configuration;
 its overhead increases from @render-max-overhead['typed 'morsecode] to @render-max-overhead['tagged 'morsecode].
This degredation reveals a pitfall of the locally-defensive embedding, which
 we discuss in the following section.


@section{Results: Linear Degredation}

@note-to-self{
Need to mention the "more types, more slow" property.
No space here for a figure, but point to the appendix.
}


@section{Threats to Validity}

The performance of our @|LD-Racket| prototype is an order-of-magnitude improvement
 over @|TR|.
We believe this high-level conclusion is valid; however, the exact performance of a full
 implementation is likely to vary from our implementation.

@; === things that make prototype too fast
On one hand, the prototype is likely to be faster than a complete implementation
 because it makes little effort to provide useful error messages.
When a tag check fails, the prototype simply directs programmers to the
 source code associated with the tag check using information available to the
 completion function.
Improving these error messages with information about the source of an ill-tagged
 value is likely to degrade performance.

Similarly, the prototype avoids using Racket's contract system to implement
 type-tag checks.
Contracts are a useful tool for defining predicates that give well-structured
 error messages, but we found they added prohibitive overheads.
Perhaps the implementation of contracts could be improved; perhaps they
 are just the wrong tool for implementing frequently-executed assert statements.

@; === things that make prototype too slow
On the other hand, the performance of the prototype could be improved in two
 obvious ways.
First, @|LD-Racket| does not take advantage of the @|TR| optimizer
 to remove type-tag checks from primitive operations.
Second, the prototype could use type-based static analysis
 to detect redundant type-tag checks.
See occurrence typing and the unification-based ideas in soft typing.

@; === things that make prototype non-representative
Three other threats are worth noting.
First, @|LD-Racket| does not support Racket's object-oriented features;
 programs using such features might not improve as drastically as the functional
 benchmarks we measure.
Second, our benchmarks are relatively small; the largest is 10 modules and 800 lines (see appendix for full details).
@; TODO auto-compute
Third, ascribing different types to the same program can affect its performance;
 for example the tag check for an integer is less expensive than the tag check for
 a natural number or some other union type.
Nevertheless we consider our results representative.


@;@section{Experience}
@;
@;Type-tag error messages suck.
@;More generally, forgetful-embedding error messages suck.

