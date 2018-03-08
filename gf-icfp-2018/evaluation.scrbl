#lang gf-icfp-2018
@title[#:tag "sec:evaluation"]{Apples-to-Apples Performance}

@; thesis: soundness matters for performance

@; TODO
@; - sec:implementation:tag-check
@;    julia extreme tag checks

@; -----------------------------------------------------------------------------

The models support two general hypotheses about the relative performance
 of the embeddings:
@itemlist[#:style 'ordered
@item{
  For mixed-typed programs, the erasure embedding adds less overhead
   than the locally-defensive embedding, and both add significantly less
   overhead than the natural embedding.
}
@item{
  For fully-typed programs, the natural embedding may out-perform the erasure
   embedding, and both add significantly less overhead than the locally-defensive
   embedding.
}
]
It remains to be seen whether these hypotheses hold for a practical implementation.

This section presents the results of a comparative evaluation of the natural,
 erasure, and locally-defensive embeddings in the context of Typed Racket.
The data suggests that the locally-defensive embedding is a large
 improvement over the natural embedding for mixed-typed programs, and slightly
 worse for fully-typed programs.
The erasure embedding offers the best performance, except in the case of
 mostly-typed programs that benefit from the Typed Racket optimizer@~cite[stff-padl-2012].


@; -----------------------------------------------------------------------------
@section{Implementation Overview}

@; TODO compiled

@|TR|@~cite[tf-popl-2008] is a migratory typing system for Racket that
 implements the natural embedding.
Whereas a Racket program starts with the line @tt|{#lang racket}| a
 @|TR| program starts with the line @tt|{#lang typed/racket}| and
 must type check before the compiler will generate bytecode.

As a convenience for developers, the implementation of @|TR| comes
 with a third language, @tt|{#lang typed/racket/no-check}|, that treats type
 annotations as comments.
This third language provides an easy way to compare the performance of the
 natural embedding (standard @|TR|) against the erasure embedding (no-check)
 for the same source code.

To measure the performance of the locally-defensive embedding, we implemented
 this embedding in a fork of @|TR|.
The implementation re-uses the static type checker,
 defines a new semantics for boundary terms,
 and replaces the type-directed optimizer with a type-directed completion pass.
The fork is based on Racket version 6.10, released in July 2017.
All code is made available in the artifact for this paper.

Re-using the type checker is difficult; this is why our implementation is a
 fork instead of a package.

@subsection[#:tag "sec:implementation:checks"]{Constructor Checks}

How to implement constructor checks?
The checks in the model are just type-tag checks,
 the kind that come built-in in any safe dynamic language.

The implementation uses more checks.
For types of the form @${F(\tau)} that represent mutable data, for example
 @${\tarray{\tau}}, check the constructor --- mutability makes no difference.
For (true) union types of the form @${\tau_0 \cup \tau_1}, values that match
 @${\tagof{\tau_0}} and @${\tagof{\tau_1}} are correct, so check the disjunction.
For a universal type @${\tall{\alpha}{\tau}} or recursive type @${\mu{\alpha}{\tau}},
 use the constructor @${\tagof{\tau}}.
For a type variable @${\alpha}, define @${\tagof{\alpha} = \kany}; intuitively,
 a typed context cannot make any assumptions about the constructor of a value
 with type @${\alpha}, so there is no need to insert a check.

In principle there is one check per type in the program, so a sophisticated
 compiler can generate efficient code for these.
We do not do this.
Open question.

We implement checks with procedures; basically as contracts.
Use TR type to contract compiler, then insert a check.
@; (if ((begin-encourage-inline ctc) v) v (error ....))


@subsection{Completion}

The completion pass rewrites functions and function applications.
Every typed function @racket[(lambda ([x : T] ....) e)] is rewritten to a checked
 function @racket[(lambda ([x : T] ....) (check T x) .... e)].
Every application @racket[(_f _x ....)] is rewritten to
 @racket[(check _K (_f _x ....))], where @racket[_K] comes from the static type
 of the expression.
One more thing: we whitelist functions such as @racket[list]
 that are trusted to give results with the expected constructor.


@subsection{Compiling to a Host Language}

The models employ a small-step operational semantics for an expression language.
The natural and locally-defensive have two reduction relations.
In practice, though, a migratory typing system compiles statically-typed code
 to the host language, which raises two questions.

The first question is how to represent the static types that the models use
 in monitor values and function applications.
We compile to contracts.

The second question is whether it is sound to use the host language reduction
 relation on statically-typed terms.
Theorems in the previous section show that this is sound.


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

@(define RT (make-ratios-table TR-DATA* TAG-DATA*))

@figure["fig:typed-baseline-ratios"
        @elem{Typed/untyped ratios for @|TR| (TR) and @|LD-Racket| (LD)}
        @render-ratios-table[RT]]


@Figure-ref{fig:locally-defensive-performance} plots
 the overhead of @|TR| relative to Racket (@|tr-color-text| color)
 and the overhead of @|LD-Racket| relative to Racket (@|tag-color-text| color)
 for @|NUM-TR| functional programs.
In summary, the area under the curve for @|LD-Racket| is larger so we conclude that
 the locally-defensive embedding has better performance than the natural embedding
 on mixed-typed programs.

The data for the plots comes from applying the Takikawa method@~cite[tfgnvf-popl-2016 gtnffvf-jfp-2017]
 to their functional benchmark programs.
For a program with @${N} modules, the data is an average running time based
 on @~a[NUM-ITERS] iterations for each of the @${2^N} configurations of the program.
The value of @${2^N} is reported at the top-right of each plot in @figure-ref{fig:locally-defensive-performance}.

All measurements were collected sequentially using Racket v6.10.1 on an unloaded Linux
 machine with two physical AMD Opteron 6376 processors (a NUMA architecture) and
 128GB RAM.
The CPU cores on each processor ran at 2.30 GHz using the @emph{performance} CPU governor.

The lines on each plot show the percent of @deliverable{D} configurations as
 the value of @${D} increases from @${1} to @${@~a[X-MAX]}.
A configuration is @deliverable{D} if its running time is at most @${D} times
 slower than the running time of the corresponding (untyped) Racket program.
A point @${(X, Y)} on the line for Typed Racket says that @${Y}% of all Typed Racket configurations
 for the benchmark @sc{b} run at most @${X} times slower than Racket running
 the same code with all types erased.

Ideally, the percent of @deliverable{D} configurations would be high for
 @${D=1} and reach @${100\%} at a low value, perhaps @${D=1.8}.
A @deliverable{1} configuration runs at least as fast as the untyped program.
The worst case is that only a small percent of configurations are @deliverable[X-MAX],
 meaning that many mixed-typed programs suffer a huge performance overhead.

@;@emph{Remark} The premise of the @deliverable{D} measure is that programmers
@; have a fixed performance requirement.
@;Certain applications may have strict performance requirements and can
@; only tolerate a 10% overhead, corresponding to @${D\,=\,1.1x}.
@;Others may accept overhead as high as @${D\,=\,10x}.
@;No matter the requirement, any programmer can instantiate @${D} and check whether
@; the proportion of @deliverable{D} configurations is high enough to enable
@; an incremental transition to a typed codebase.
@;@emph{End}

The data confirms that @|LD-Racket| is significantly more
 performant than @|TR|; see the plots for
 @bm{sieve}, @bm{fsm}, @bm{suffixtree}, @bm{kcfa},
 @bm{snake}, @bm{tetris}, and @bm{synth}.
The improvement is most dramatic for @bm{synth}
 because Typed Racket @bm{synth} spends a large amount of time
 eagerly traversing data structures and monitoring their components.
@; FSM also dramatic, removes huge indirection cost

Two bad things.
The @bm{zombie} benchmark shows only a minor improvement;
 few configurations are @deliverable{10} in either Typed Racket or @|LD-Racket|.
The @bm{morsecode} benchmark is often a slow-down; using @|LD-Racket|
 increases its worst-case overhead from @maxo['typed 'morsecode #:precision '(= 1)]
 to @maxo['tagged 'morsecode #:precision '(= 1)].
This degredation occurs because the many constructor checks inserted by @|LD-Racket|
 introduce more overhead than the boundary checks inserted by Typed Racket.

@Figure-ref{fig:max-overhead} presents a sky view of the benchmarks.
@|LD-Racket| has much better worst-case performance.


@section{Evaluation II: Fully-Typed Programs}

The second hypothesis concerns the performance of fully-typed programs.
@|TR| is expected to be fastest, because the static types enable some
 optimization@~cite[stff-padl-2012].
@|LD-Racket| is expected to be slowest because it rewrites all typed code to include
 checks.
For example, the simple expressions @${\efst{\vpair{0}{1}}} reduces to a value
 in one step in the natural embedding and in two steps in the locally-defensive
 embedding:

@$$|{
  \wellM \efst{\vpair{0}{1}} : \tint \carrow \echk{\kint}{(\efst{\vpair{0}{1}})} \rrKSstar \echk{\kint}{0} \rrKSstar 0
}|

So much for the theory.
How do the implementations stack up?

@; TODO maybe should be a bar graph, with error lines
@Figure-ref{fig:typed-baseline-ratios} lists peformance ratios for each of the
 benchmarks.
The first row lists abbreviated benchmark names.
The second row lists the ratio of @|TR| on the fully-typed configuration
 relative to Racket on the untyped configuration.
The third and final row lists the ratio of @|LD-Racket| on the fully-typed
 configuration relative to Racket on the untyped configuration.

@|LD-Racket| is the slowest on every benchmark.
@|TR| is the fastest on @integer->word[(for/sum ([n (in-list (ratios-table->typed RT))]) (if (< n 1) 1 0))]
 of the @integer->word[(length TR-DATA*)] benchmarks.
The @bm{zombie} benchmark is a surprising exception.
Its fully-typed performance is very slow; this is because
 it performs many type casts.
Maybe we should equalize typed and untyped for these.

This observation raises questions about optimizing the locally-defensive
 embedding.
We discuss these and other directions for future work in @secref{sec:conclusion}.


@section{Threats to Validity}

The performance of our @|LD-Racket| prototype is an order-of-magnitude improvement
 over @|TR|.
We believe this high-level conclusion is valid; however, the exact performance of a full
 implementation is likely to vary from our prototype implementation.

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
 error messages, but they add a constant-factor overhead that wound up
 being prohibitive.
Some of these tag checks happen many times.
@; TODO count number of checks
Perhaps the implementation of contracts could be improved;
 perhaps the JIT needs to improve.

@; === things that make prototype too slow
On the other hand, the performance of the prototype could be improved in two
 obvious ways.
First, @|LD-Racket| does not take advantage of the @|TR| optimizer
 to remove type-tag checks from primitive operations.
Second, the prototype is based on a model that introduces redundant checks;
 a better model will improve the prototype.

@; === things that make prototype non-representative
Three other threats are worth noting.
First, @|LD-Racket| does not support Racket's object-oriented features@~cite[tfdfftf-ecoop-2015];
 programs using such features might not improve as drastically as the functional
 benchmarks we measure.
Second, our benchmarks are relatively small; the largest is 10 modules and 800 lines (see appendix for full details).
@; TODO auto-compute
Third, ascribing different types to the same program can affect its performance;
 for example the tag check for an integer is less expensive than the tag check for
 a natural number or some other union type.
Nevertheless we consider our results representative.

