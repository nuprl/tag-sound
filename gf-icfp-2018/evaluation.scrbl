#lang gf-icfp-2018
@title[#:tag "sec:evaluation"]{Performance}

@; thesis: soundness matters for performance

@; TODO
@; - sec:implementation:tag-check
@;    julia extreme tag checks

@; -----------------------------------------------------------------------------

To compare the performance of the three approaches to migratory typing,
 we use three distinct compilers for the Typed Racket syntax and typing system
 on @integer->word[NUM-TR] functional benchmark programs.
The data suggests that the @|folong| embedding is mostly an
 improvement over the @|holong| embedding for mixed-typed programs.
For fully-typed programs (and configurations with many typed modules@~cite[gf-tr-2018]),
 however, the @|holong| embedding offers the best performance of all three
 thanks to the Typed Racket optimizer@~cite[stff-padl-2012].


@; -----------------------------------------------------------------------------
@section{Implementation Overview}

Typed Racket@~cite[tf-popl-2008] is a migratory typing system for Racket that
 implements the @|holong| embedding.
As a full-fledged implementation, Typed Racket handles many more types than the
 language of @figure-ref{fig:multi-syntax} and supports (higher-order) casts
 so that developers can easily migrate a module even if the type system cannot
 cope with the programming idioms.
Its run-time system guarantees that every boundary
 error attributes the fault to exactly one syntactic type
 boundary@~cite[tfffgksst-snapl-2017].

Removing the type annotations and casts
 from a Typed Racket program yields a valid Racket program.
We use this transformation to compare the @|holong| embedding
 to @|eolong|.

To compare with the @|folong| approach, we modified the Typed Racket
 compiler to rewrite typed code and compile types to predicates
 that enforce type constructors@~cite[gf-tr-2018].
Like the model, this implementation makes no claim about the quality of boundary error messages.

The three approaches outlined above define three ways to compile a
 Typed Racket program to Racket: @|holong| @|TR_N|,
 @|eolong| @|TR_E|, and
 @|folong| @|TR_LD|.
In the rest of this section, we reserve the name ``Typed Racket'' for the
 the source language.


@section[#:tag "sec:evaluation:method"]{Method}

To evaluate performance,
 we use the exhaustive method for module-level
 migratory typing@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
Starting from a multi-module program, we migrate the whole program---ignoring
 any libraries outside the control of the normal user---to Typed Racket.
From this fully-typed program, we generate all typed/untyped configurations
 by removing types from a subset of the modules.
A program with @${N} modules thus leads to @${2^N} configurations, a set that
 represents all the ways a developer might apply migratory typing to the untyped program
 for a fixed set of type annotations.

Since the promise of migratory typing is that a developer may choose to run any
 mixed-typed configuration, the main goal of the evaluation is to classify all
 configurations by their overhead relative to the completely-untyped configuration.
The key measure is the number of @deliverable{D} configurations.
A configuration is @deliverable{D} if it runs no more than @${D}x slower than
 the untyped configuation@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
If an implementation of migratory typing adds little overhead to mixed-typed
 programs, then a large percentage of its configurations are @deliverable{D}
 for a low value of @${D}.


@figure*["fig:overheads"
         @elem{@|TR_N| (@|tr-color-text| @|tr-color-sample|) and @|TR_LD| (@|tag-color-text| @|tag-color-sample|), each relative to @|eolong| (@|TR_E|).
               The @|x-axis| is log-scaled. The unlabeled vertical ticks appear at:
               @${1.2}x, @${1.4}x, @${1.6}x, @${1.8}x, @${4}x, @${6}x, and @${8}x overhead.
               A larger area under the curve is better.}
         (overhead-plot* (map list TR-DATA* TAG-DATA*))]

@(define MT (make-max-table TR-DATA* TAG-DATA*))
@(define (maxo kind bm-name #:precision [psc #false])
   (render-max-overhead kind bm-name #:tbl MT #:precision psc))
@(define TITLE* (list TR_N TR_LD))

@figure["fig:max-overhead"
        @elem{Worst-case overhead for @|holong| (@|TR_N|) and @|folong| (@|TR_LD|), each relative to @|eolong|.}
        @render-max-table[MT TITLE*]]

@;@figure["fig:typed-baseline-ratios"
@;        @elem{Typed/untyped ratios for @|TR_N| and @|TR_LD|}
@;        @(let ((RT (make-ratios-table TR-DATA* TAG-DATA*)))
@;           (render-ratios-table RT TITLE*))]

@section[#:tag "sec:evaluation:protocol"]{Protocol}

The evaluation measures the performance of the @|holong| (@|TR_N|),
 @|eolong| (@|TR_E|), and @|folong| (@|TR_LD|) approaches
 on @integer->word[NUM-TR] Typed Racket programs.
Nine programs are the functional benchmarks from prior work on
 Typed Racket@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
The tenth is adapted from a JPEG library.@note{@url{https://docs.racket-lang.org/gtp-benchmarks}}

For each configuration of each benchmark, and for both @|TR_N| and @|TR_LD|,
 we collected a sequence of @integer->word[NUM-ITERS] running times
 by running the program once to account for JIT warmup and
 then an additional @integer->word[NUM-ITERS] times for the actual measurement.
For @|TR_E| we measured one sequence of running times
 because all configurations erase to the same program.

All measurements were collected sequentially using Racket v@|RKT-VERSION| on an
 unloaded Linux machine with two physical AMD Opteron 6376 processors (a NUMA architecture) and
 128GB RAM.
The CPU cores on each processor ran at 2.30 GHz using the ``performance'' CPU governor.


@section{Evaluation I: Mixed-Typed Programs}

@Figure-ref{fig:overheads} plots
 the overhead of @|TR_N| relative to @|eolong| (@|tr-color-text| @|tr-color-sample|)
 and the overhead of @|TR_LD| relative to @|eolong| (@|tag-color-text| @|tag-color-sample|)
 for the @integer->word[NUM-TR] functional programs.
The lines on each plot give the percent of @deliverable{D} configurations
 for values of @${D} between @${1} to @${@~a[X-MAX]}.
In other words, a point @${(X, Y)} on a line for @|TR_N| says that @${Y}% of all @|TR_N| configurations
 in this program run at most @${X} times slower than the same program with all types erased.

@;The lines for @|TR_LD| are frequently higher than the lines for @|TR_N|.
@;The difference is most dramatic for @bm{synth}.
@;The @bm{morsecode} benchmark, however, shows no improvement; the cost of
@; checking constructors throughout typed code always out-weighs the cost of fully
@; enforcing types.

Since seven of the @integer->word[NUM-TR] benchmarks have at least one @|TR_N|
 configuration that falls ``off the charts'' with an overhead above @~a[X-MAX]x,
 @figure-ref{fig:max-overhead} tabulates the worst-case overhead in each benchmark.
According to the table, the @|holong| embedding
 may slow a working program by three orders of magnitude.
The largest slowdowns, in @bm{fsm} and @bm{zombie}, occur because higher-order
 values repeatedly cross type boundaries and accumulate monitors.
By contrast, the worst-case performance of @|TR_LD|
 is always within two orders of magnitude.


@section{Evaluation II: Fully-Typed Programs}

@figure["fig:typed-speedup"
        @elem{Speedup of fully-typed
              @|TR_N| (@|tr-color-sample|)
              and @|TR_LD| (@|tag-color-sample|),
              relative to @|TR_E| (the 1x line).
              Taller bars are better.}
        @(parameterize ([*bar-chart-height* 100]
                        [*bar-chart-max* 3.5])
           (let ((TBL (make-typed-table TR-DATA* TAG-DATA*)))
             (render-speedup-barchart TBL)))]

The table in @figure-ref{fig:typed-speedup} compares the performance
 of fully-typed programs.
The @|tr-color-text| bars plot the overhead of @|TR_N| relative to the @|eolong| embedding
 on each benchmark.
The @|tag-color-text| bars plot analogous data for @|TR_LD|
 relative to the @|eolong| embedding.

The @bm{jpeg} and @bm{zombie} benchmarks demonstrate exceptional performance.
In @bm{jpeg}, the speedup of @|TR_N| over @|eolong| is high because
 the user program depends on a typed library; the library protects itself
 against @|TR_E| code.
In @bm{zombie}, typed code is slower than @|eolong|.
The typed version of @bm{zombie} performs a type cast in the inner loop.
The untyped version replaces this cast with a rudimentary predicate check.
This simple change noticeably affects the performance of the fully-typed configuration
 (the overhead of monitors, however, dominates the mixed-typed configurations).


@section[#:tag "sec:evaluation:threats"]{Threats to Validity}

@;The performance of the @|TR_LD| prototype demonstrates an
@; order-of-magnitude improvement over @|TR_N| on mixed-typed programs.
@;The performance of a full-fledged implementation, however, may
@; have slightly different performance characteristics.

The performance of a full-fledged @|TR_LD| implementation may differ from that
 of our prototype.

@; === things that make prototype too fast
On one hand, the prototype is likely to be faster than a full implementation
 because it makes no effort to provide useful error messages.
When a constructor check fails, the prototype simply directs programmers to the
 source location of the check.
Improving these error messages with information about the source of the
 incompatible value is likely to degrade performance in a significant manner.

@; === things that make prototype too slow
On the other hand, the performance of a full implementation could improve over
 the prototype in two ways.
First, @|TR_LD| does not take advantage of the @|TR_N| optimizer
 to remove checks for tag errors.
Integrating the safe parts of the optimizer may offset some cost of the constructor checks.
Second, the completion judgment for the prototype
 may introduce redundant checks.
For example, consecutive reads from a list suffer the same check
 on the extracted element.

@; === things that make prototype non-representative
Three other threats are worth noting.
First, @|TR_LD| does not support Racket's object-oriented features@~cite[tfdfftf-ecoop-2015].
We expect that scaling the implementation to the full language would not affect the functional benchmarks.
@; ... though we expect OO to improve even more
Second, our benchmarks are relatively small; the largest is @bm{jpeg} with
 approximately 1,500 lines of code.
@; ; though in our experience and the experience
@; of Typed Racket users, our results are likely to reflect the reality of large-scale
@; programs.
@; TODO auto-compute
Third, the evaluation considers only one fully-typed version of each benchmark.
Ascribing different types to the same program can affect its performance;
 for example, the check for an integer may run faster than the
 check for a natural number.
