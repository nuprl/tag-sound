#lang gf-icfp-2018
@title[#:tag "sec:evaluation"]{Performance}

@; thesis: soundness matters for performance

@; TODO
@; - sec:implementation:tag-check
@;    julia extreme tag checks

@; -----------------------------------------------------------------------------

To compare the performance of the three approaches,
 we use three distinct compilers for the Typed Racket syntax and typing system
 on @integer->word[NUM-TR] functional benchmark programs.
The data suggests that the locally-defensive embedding is a large
 improvement over the natural embedding for mixed-typed programs but slightly
 worse for fully-typed programs.
The erasure embedding offers the best performance, except for typed programs
 that happen to benefit from the Typed Racket optimizer@~cite[stff-padl-2012].


@; -----------------------------------------------------------------------------
@section{Implementation Overview}

Typed Racket@~cite[tf-popl-2008] is a migratory typing system for Racket and faithfully
 implements the natural embedding by compiling types to (higher-order) contracts@~cite[ff-icfp-2002].
Its soundness guarantee is that of the natural embedding.
As a full-fledged implementation, Typed Racket handles many more types than the
 language of @figure-ref{fig:multi-syntax} and guarantees that every boundary
 error blames exactly one of the static
 boundaries between typed and untyped code@~cite[tfffgksst-snapl-2017].

Removing the type annotations and casts
 from a Typed Racket program yields a valid Racket program.
For any mixed-typed program, we can therefore compare the natural embedding
 to the erasure embedding by removing types, converting casts to Racket-level
 assertions, and measuring the underlying Racket program.

To compare against the locally-defensive approach, we modified the Typed Racket
 compiler to rewrite typed code and to compile types to (flat) predicates
 that check first-order properties of values.
The soundness guarantee of this implementation is that evaluation preserves the
 first-order properties.
Like the model, it makes no claim about the quality of boundary error messages.

The three approaches outlined above define three ways to compile a well-typed
 Typed Racket program down to Racket.
Let the names @|TR_N|, @|TR_E|, and @|TR_LD| refer to the
 ``natural'' compiler, the type-erasure compiler, and the locally-defensive compiler,
 respectively.
The name ``Typed Racket'' henceforth refers to the syntax and typing system
 (in the sense of @figure-ref["fig:multi-syntax" "fig:multi-preservation"]),
 and Racket is the target language for all three compilers.


@section[#:tag "sec:evaluation:method"]{Method}

To evaluate the performance of these three implementations, we use the exhaustive method for module-level
 migratory typing@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
Starting from one multi-module program, we migrate the whole program (ignoring
 any libraries beyond our control) to Typed Racket.
From this fully-typed program, we generate all typed/untyped configurations
 by removing types from a subset of its modules.
A program with @${N} modules thus leads to @${2^N} configurations,
 which represent all the variations of one program that a developer might
 construct through migratory typing.

Since the promise of migratory typing is that a developer may choose to run any
 mixed-typed configuration, the main goal of such an evaluation is to classify all
 configurations by their overhead relative to the completely-untyped configuration.
The key measure is the number of @deliverable{D} configurations.
A configuration is @deliverable{D} if it runs no more than @${D}x slower than
 the untyped configuation@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
If an implementation of migratory typing adds little overhead to mixed-typed
 programs, then a large percentage of its configurations will be @deliverable{D}
 for a low value of @${D}.

For this paper, we present the percent of @deliverable{D} configurations
 for @${D} between 1x and @~a[X-MAX]x.
The supplementary material contains the uninterpreted data.


@section[#:tag "sec:evaluation:protocol"]{Protocol}

The evaluation measured the performance of the natural semantics (@|TR_N|),
 erasure semantics (@|TR_E|), and locally-defensive semantics (@|TR_LD|)
 on @integer->word[NUM-TR] Typed Racket programs.
Nine programs are the functional benchmarks from prior work on
 Typed Racket@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
The tenth program is adapted from a JPEG library; the original author of this
 application noticed poor performance due to untyped code interacting with
 a Typed Racket array library.
The appendix provides further details on the size, origin, and purpose of each benchmark.

For each configuration of each benchmark @emph{except @bm{jpeg}},
 we collected data using both @|TR_N| and @|TR_LD|.
The data for each semantics is a sequence of @~a[NUM-ITERS] running times,
 which we obtained by running the program once to account for JIT warmup and
 then an additional @~a[NUM-ITERS] times to collect data.
The data for @|TR_E| on these benchmarks is one sequence of running times
 as all typed/untyped configurations erase to the same Racket program.

The @bm{jpeg} benchmark depends on a typed library.
To measure its @|TR_N| performance, we compile the library using @|TR_N|,
 measure the performance of all typed/untyped configurations, and report
 their overhead relative to the untyped configuration (which interacts with
 the compiled, typed library).
To measure its @|TR_LD| performance, we compile the library using @|TR_LD|
 and report the performance of all configurations relative to the untyped
 configuration using the @|TR_LD| library.
This protocol accurately reports the overhead in two parallel implementations
 of the Typed Racket surface language, but it does not yield a true symmetric
 comparison (see @section-ref{sec:evaluation:threats}).@note{We noticed this
 breach too late. For a published version of this submission, we intend to
 re-do the evaluation of this benchmark in an apples-to-apples manner.}

All measurements were collected sequentially using Racket v@|RKT-VERSION| on an
 unloaded Linux machine with two physical AMD Opteron 6376 processors (a NUMA architecture) and
 128GB RAM.
The CPU cores on each processor ran at 2.30 GHz using the ``performance'' CPU governor.


@section{Evaluation I: Mixed-Typed Programs}

@figure*["fig:locally-defensive-performance"
         @elem{@|TR_N| (blue @|tr-color-sample|) and @|TR_LD| (orange @|tag-color-sample|), each relative to erasure (@|TR_E|).
               The @|x-axis| is log-scaled. The unlabeled vertical ticks appear at:
               @${1.2}x, @${1.4}x, @${1.6}x, @${1.8}x, @${4}x, @${6}x, and @${8}x overhead.
               A larger area under the curve is better.}
         (overhead-plot* (map list TR-DATA* TAG-DATA*))]

@(define MT (make-max-table TR-DATA* TAG-DATA*))
@(define (maxo kind bm-name #:precision [psc #false])
   (render-max-overhead kind bm-name #:tbl MT #:precision psc))
@(define TITLE* (list TR_N TR_LD))

@figure["fig:max-overhead"
        @elem{Worst-case overhead for the natural embedding (@|TR_N|) and the locally-defensive embedding (@|TR_LD|) relative to erasure.}
        @render-max-table[MT TITLE*]]

@;@figure["fig:typed-baseline-ratios"
@;        @elem{Typed/untyped ratios for @|TR_N| and @|TR_LD|}
@;        @(let ((RT (make-ratios-table TR-DATA* TAG-DATA*)))
@;           (render-ratios-table RT TITLE*))]

@figure["fig:typed-speedup"
        @elem{Speedup of fully-typed
              @|TR_N| (@|tr-color-sample|)
              and @|TR_LD| (@|tag-color-sample|),
              relative to @|TR_E| (the 1x line).
              Taller bars are better.}
        @(let ((TBL (make-typed-table TR-DATA* TAG-DATA*)))
           (render-speedup-barchart TBL))]


@Figure-ref{fig:locally-defensive-performance} plots
 the overhead of @|TR_N| relative to erasure (@|tr-color-text| color)
 and the overhead of @|TR_LD| relative to erasure (@|tag-color-text| color)
 for the @integer->word[NUM-TR] functional programs.
The lines on each plot give the percent of @deliverable{D} configurations
 for values of @${D} between @${1} to @${@~a[X-MAX]}.
In other words, a point @${(X, Y)} on the line for @|TR_N| says that @${Y}% of all @|TR_N| configurations
 run at most @${X} times slower than the same program with all types erased.

The lines for @|TR_LD| are frequently higher than the lines for @|TR_N|; see
 the plots for @bm{sieve}, @bm{fsm}, @bm{suffixtree}, @bm{kcfa},
 @bm{snake}, @bm{tetris}, and @bm{synth}.
The difference is most dramatic for @bm{synth}.
The @bm{morsecode} and @bm{zombie} benchmarks, however, show no difference
 in the @${1}x to @${@~a[X-MAX]}x range.

Since seven of the @integer->word[NUM-TR] benchmarks have at least one @|TR_N|
 configuration that falls ``off the charts'' with an overhead above @~a[X-MAX]x,
 @figure-ref{fig:max-overhead} tabulates the worst-case overhead in each benchmark.
This table demonstrates that for pathological examples the natural embedding
 may slow down a working program by over two orders of magnitude.
By contrast, the worst-case performance of the locally-defensive embedding
 is always within two orders of magnitude.


@section{Evaluation II: Fully-Typed Programs}

The table in @figure-ref{fig:typed-speedup} compares the performance
 of fully-typed programs.
The blue bars plot the overhead of @|TR_N| relative to the erasure embedding
 on each benchmark.
The orange bars present analogous data for @|TR_LD|
 relative to the erasure embedding.

On fully-typed programs, @|TR_N| may run faster than the erasure approach.
This speed-up is due to type-driven optimizations@~cite[stff-padl-2012] and, in the case
 of @bm{jpeg}, the removal of a boundary between the user program and a typed library.
By contrast, @|TR_LD| is the slowest on every benchmark.


@section[#:tag "sec:evaluation:threats"]{Threats to Validity}

@;The performance of the @|TR_LD| prototype demonstrates an
@; order-of-magnitude improvement over @|TR_N| on mixed-typed programs.
@;The performance of a full-fledged implementation, however, may
@; have slightly different performance characteristics.

The performance of a full-fledged @|TR_LD| implementation may differ from that
 of our prototype.

@; === things that make prototype too fast
On one hand, the prototype is likely to be faster than a full implementation
 for two reasons.
First, it makes no effort to provide useful error messages.
When a constructor check fails, the prototype simply directs programmers to the
 source location of the check.
Improving these error messages with information about the source of the
 incompatible value is likely to degrade performance in a significant manner.
Second, the prototype avoids using contract combinators to implement
 type-constructor checks because our initial experiments suggested a high
 overhead for doing so.
Instead of using a contract combinator to encode a test for, e.g., positive
 real numbers, the prototype uses a function.

@; === things that make prototype too slow
On the other hand, the performance of a full implementation could improve over
 the prototype in two ways.
First, @|TR_LD| does not take advantage of the @|TR_N| optimizer
 to remove checks for tag errors;
 integrating the optimizer may offset some cost of the defensive checks.
Second, like Reticulated, the completion judgment for the prototype
 may introduce redundant checks.

@; === things that make prototype non-representative
Three other threats are worth noting.
First, @|TR_LD| does not support Racket's object-oriented features@~cite[tfdfftf-ecoop-2015];
 we do not expect that scaling it up would affect the functional benchmarks.
@; ... though we expect OO to improve even more
Second, our benchmarks are relatively small; the largest is @bm{jpeg} with
 approximately 1,500 lines of code.
@; ; though in our experience and the experience
@; of Typed Racket users, our results are likely to reflect the reality of large-scale
@; programs.
@; TODO auto-compute (this is a big effort, the paper repo doesn't know where the benchmarks live)
Third, the evaluation considers one fully-typed version of each benchmark,
 but ascribing different types to the same program can affect its performance.
For example, the constructor check for an integer may be less expensive than the
 check for a natural number.
Fourth, the choice to measure two versions of @bm{jpeg} is somewhat unrealistic;
 a developer is more likely to avoid a typed library than to recompile it under
 a different semantics.
@; TODO in order for typed/tagged jpeg to share ....
@; - LD needs to accept TR type definitions
@; - or LD needs require/typed for polymorphic structs (definitely possible)
