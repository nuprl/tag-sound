#lang gf-icfp-2018
@title[#:tag "sec:evaluation"]{Performance}

@; thesis: soundness matters for performance

@; TODO
@; - sec:implementation:tag-check
@;    julia extreme tag checks

@; -----------------------------------------------------------------------------

To compare the performance of the three approaches as practical implementations
 for one surface language, we use Typed Racket and a suite of @integer->word[NUM-TR]
 functional programs.
The data suggests that the locally-defensive embedding is a large
 improvement over the natural embedding for mixed-typed programs, and slightly
 worse for fully-typed programs.
The erasure embedding offers the best performance, except in typed programs
 that happen to benefit from the Typed Racket optimizer@~cite[stff-padl-2012].


@; -----------------------------------------------------------------------------
@section{Implementation Overview}

@|TR|@~cite[tf-popl-2008] is a migratory typing system for Racket and faithfully
 implements the natural embedding by compiling types to (higher-order) contracts@~cite[ff-icfp-2002].
Its soundness guarantee is essentially that of the natural embedding,
 but @|TR| handles additional types and guarantees that every boundary error
 blames one of the static boundaries between typed and untyped code@~cite[tfffgksst-snapl-2017].

Removing the type annotations from a @|TR| program yields a valid Racket
 program.
For any mixed-typed program, we can therefore compare the natural embedding
 to the erasure embedding by removing types and measuring the underlying Racket
 program.

To compare against the locally-defensive approach, we modified the @|TR|
 compiler to rewrite typed code and to compile types to (flat) contracts
 that check first-order properties of values.
The soundness guarantee of this implementation is that evaluation preserves the
 first-order properties; it makes no claim about the quality of boundary error messages.


@section[#:tag "sec:evaluation:method"]{Method}

To evaluate performance, we use the exhaustive method for module-level
 migratory typing@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
Starting from one mixed-typed program, we migrate the whole program (ignoring
 any libraries) to @|TR|.
From this fully-typed program, we generate all typed/untyped configurations
 by converting a subset of modules back to (untyped) Racket.
A program with @${N} modules thus leads to @${2^N} configurations,
 which represent all the variations of one program that a developer might
 construct through migratory typing.

Since the promise of migratory typing is that a developer may choose to run any
 mixed-typed configuration, the main goal of our evaluation is to classify all
 configurations by their overhead relative to the completely-untyped configuration.
If many configurations are @deliverable{D}, in the sense that they run no
 more than @${D}x slower than the untyped configuration@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017],
 then a developer willing to accept a @${D}x slowdown can fearlessly apply migratory typing.
Otherwise, that developer may prefer the erasure approach (remove all types)
 over natural or locally-defensive migratory typing.

For this paper, we present the number of @deliverable{D} configurations
 for @${D} between 1x and @~a[X-MAX]x.
The supplementary material contains the uninterpreted data.


@section[#:tag "sec:evaluation:experiment"]{Experiment}

The evaluation measured the performance of @|TR| and our
 @|LD-Racket| on @integer->word[NUM-TR] programs.
Nine programs are the functional benchmarks from prior work on
 Typed Racket@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017].
The tenth program is adapted from a JPEG library; the original author of this
 application noticed poor performance due to untyped code interacting with
 a @|TR| array library.
Further details on the size, origin, and purpose of each benchmark are in the
 appendix.

For each configuration of each benchmark, we collected data using both @|TR|
 and @|LD-Racket|.
The data for each semantics is a sequence of @~a[NUM-ITERS] running times,
 which we obtained by running the program once to account for JIT warmup and
 then an additional @~a[NUM-ITERS] times to collect data.

This protocol yields two potentially-different sets of measurements
 corresponding to the erasure embedding:
 one for the fully-untyped configuration running via @|TR|
 and one for the untyped configuration via @|LD-Racket|.
These measurements differ if the program depends on any typed libraries,
 as the semantics of typed code depend on the implementation of migratory typing.
It is therefore essential that we use the two sets to provide a fair baseline
 for discussing overhead.
Only the @bm{jpeg} benchmark is affected by this technicality.

All measurements were collected sequentially using Racket v@|RKT-VERSION| on an
 unloaded Linux machine with two physical AMD Opteron 6376 processors (a NUMA architecture) and
 128GB RAM.
The CPU cores on each processor ran at 2.30 GHz using the @emph{performance} CPU governor.


@section{Evaluation I: Mixed-Typed Programs}

@figure*["fig:locally-defensive-performance"
         @elem{@|LD-Racket| (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample|).
               The @|x-axis| is log-scaled. The unlabeled vertical ticks appear at:
               @${1.2}x, @${1.4}x, @${1.6}x, @${1.8}x, @${4}x, @${6}x, and @${8}x overhead.}
         (overhead-plot* (map list TR-DATA* TAG-DATA*))]

@(define MT (make-max-table TR-DATA* TAG-DATA*))
@(define (maxo kind bm-name #:precision [psc #false])
   (render-max-overhead kind bm-name #:tbl MT #:precision psc))

@figure["fig:max-overhead"
        @elem{Worst-case overhead for @|TR| (TR) and @|LD-Racket| (LD)}
        @render-max-table[MT]]


@Figure-ref{fig:locally-defensive-performance} plots
 the overhead of @|TR| relative to its untyped configuration (@|tr-color-text| color)
 and the overhead of @|LD-Racket| relative to its untyped configuration (@|tag-color-text| color)
 for the @integer->word[NUM-TR] functional programs.
The lines on each plot give the percent of @deliverable{D} configurations
 for values of @${D} between @${1} to @${@~a[X-MAX]}.
In other words, a point @${(X, Y)} on the line for @|TR| says that @${Y}% of all @|TR| configurations
 run at most @${X} times slower than the same program with all types erased.

The data confirms that @|LD-Racket| yields better performance on mixed-typed
 programs than @|TR|; see the plots for
 @bm{sieve}, @bm{fsm}, @bm{suffixtree}, @bm{kcfa},
 @bm{snake}, @bm{tetris}, and @bm{synth}.
The improvement is most dramatic for @bm{synth}
 because Typed Racket @bm{synth} spends a large amount of time
 eagerly traversing data structures and monitoring their components.
The @bm{morsecode} and @bm{zombie} benchmarks, however, show no improvement
 in the @${1}x to @${@~a[X-MAX]}x range.

Since seven of the @integer->word[NUM-TR] benchmarks have at least one @|TR|
 configuration with over @~a[X-MAX]x overhead, @figure-ref{fig:max-overhead}
 tabulates the worst-case overhead in each benchmark.
This table demonstrates that for pathological examples, the natural embedding
 may slow a working program by over two orders of magnitude.
By contrast, the worst-case performance of the locally-defensive embedding
 always within two orders of magnitude, and often under 10x.


@section{Evaluation II: Fully-Typed Programs}

@(define RT (make-ratios-table TR-DATA* TAG-DATA*))

@figure["fig:typed-baseline-ratios"
        @elem{Typed/untyped ratios for @|TR| (TR) and @|LD-Racket| (LD)}
        @render-ratios-table[RT]
        @;@ratios-plot[TR-DATA* TAG-DATA*]
        ]

@; TODO maybe should be a bar graph, with error lines

The locally-defensive approach rewrites typed code.
In the worst case, when all code is typed, all code is defended with checks.
A question is how this hypothetical worst-case compares to the natural
 embedding, which adds no overhead to typed code.

@Figure-ref{fig:typed-baseline-ratios} addresses this question by presenting
 typed/untyped ratios for each benchmark.
The first row lists abbreviated benchmark names.
The second row lists the ratio of @|TR| on the fully-typed configuration
 relative to its untyped configuration.
The final row lists the ratio of @|LD-Racket| on the fully-typed
 configuration relative to its untyped configuration.

@|LD-Racket| is the slowest on every benchmark.
@|TR| is the fastest on @integer->word[(for/sum ([n (in-list (ratios-table->typed RT))]) (if (< n 1) 1 0))]
 of the @integer->word[(length TR-DATA*)] benchmarks.
The high overhead in the @bm{zombie} benchmark is due to type casts
 it performs to validate its input data.


@section{Threats to Validity}

The performance of the @|LD-Racket| prototype demonstrates an
 order-of-magnitude improvement over @|TR| on mixed-typed programs.
The performance of a full-fledged implementation, however, may
 have slightly different performance characteristics.

@; === things that make prototype too fast
On one hand, the prototype is likely to be faster than a full implementation
 for two reasons.
First, it makes little effort to provide useful error messages.
When a constructor check fails, the prototype simply directs programmers to the
 source location of the check.
Improving these error messages with information about the source of the
 incompatible value is likely to degrade performance in a significant manner.

Second, the prototype avoids using the Racket contract library to implement
 type-constructor checks because our initial experiments suggested a high
 overhead for doing so.
Instead of using a contract combinator to encode a test for, e.g., positive
 real numbers, the prototype uses a function.

@; === things that make prototype too slow
On the other hand, the performance of a full implementation could improve over
 the prototype in two ways.
First, @|LD-Racket| does not take advantage of the @|TR| optimizer
 to remove checks for tag errors;
 integrating the optimizer may offset some cost of the defensive checks.
Second, the prototype is based on a completion judgment that introduces
 redundant checks.

@; === things that make prototype non-representative
Four other threats are worth noting.
First, @|LD-Racket| does not support Racket's object-oriented features@~cite[tfdfftf-ecoop-2015].
@; ... though we expect OO to improve even more
Second, our benchmarks are relatively small; the largest is @bm{jpeg} with
 approximately 1500 lines of code.
@; TODO auto-compute (this is a big effort, the paper repo doesn't know where the benchmarks live)
Third, ascribing different types to the same program can affect its performance;
 for example the constructor check for an integer is less expensive than the check for
 a natural number or a union type.
Fourth, the @|LD-Racket| version of the @bm{jpeg} benchmark depends on an
 locally-defensive version of a @|TR| library because @|LD-Racket| and @|TR|
 cannot share type definitions.
 @; consequences: (1) slower math library, (2) no chaperones to protect TR from LD
