#lang gf-icfp-2018
@title[#:tag "sec:evaluation"]{Apples-to-Apples Performance}

@; TODO
@; - implementation (how measured all 3 embeddings)
@; - overhead plots
@; - typed/untyped ratios

@; - sec:implementation:tag-check
@;    julia extreme tag checks

@; -----------------------------------------------------------------------------


The models of the natural, erasure, and locally-defensive embeddings
 have different performance characteristics.
The apparent difference suggest two hypotheses about the relative performance
 of these embeddings as three runtime systems for the same migratory typing
 front-end:
@itemlist[#:style 'ordered
@item{
  for mixed-typed programs, erasure @${<} locally-defensive @${\ll} natural
}
@item{
  for fully-typed programs, natural @${<} erasure @${<} locally-defensive
}
]

This section presents the results of a performance evaluation of the embeddings
 for Typed Racket.
The findings support the hypotheses.


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

The new semantics for boundary terms replaces the ``natural embedding'' type
 checks with constructor checks.
Actually replacing the checks is straightforward, but it is potentially unclear
 how to check the constructor for certain types.
For types of the form @${F(\tau)} that represent mutable data, for example
 @${\tarray{\tau}}, check the constructor --- mutability makes no difference.
For (true) union types of the form @${\tau_0 \cup \tau_1}, values that match
 @${\tagof{\tau_0}} and @${\tagof{\tau_1}} are correct, so check the disjunction.
For a universal type @${\tall{\alpha}{\tau}} or recursive type @${\mu{\alpha}{\tau}},
 use the constructor @${\tagof{\tau}}.
For a type variable @${\alpha}, define @${\tagof{\alpha} = \kany}; intuitively,
 a typed context cannot make any assumptions about the constructor of a value
 with type @${\alpha}, so there is no need to insert a check.

The completion pass rewrites functions and function applications.
Every typed function @racket[(lambda ([x : T] ....) e)] is rewritten to a checked
 function @racket[(lambda ([x : T] ....) (check T x) .... e)].
Every application @racket[(_f _x ....)] is rewritten to
 @racket[(check _K (_f _x ....))], where @racket[_K] comes from the static type
 of the expression.
That is all; the only novelty is that we whitelist functions such as @racket[list]
 that are trusted to give results with the expected constructor.

The implementation is designed to support a functional subset of Racket.
It does not support Typed Racket's class and object system@~cite[tfdfftf-ecoop-2015].


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
 the overhead of @|TR| relative to Racket (TODO color)
 and the overhead of @|LD-Racket| relative to Racket (TODO color)
 for TODO functional programs.
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
 the value of @${D} increases from @${1} to TODO.
A configuration is @deliverable{D} if its running time is at most @${D} times
 slower than the running time of the corresponding (untyped) Racket program.
A point @${(X, Y)} on the line for Typed Racket says that @${Y}% of all Typed Racket configurations
 for the benchmark @sc{b} run at most @${X} times slower than Racket running
 the same code with all types erased.

Ideally, the percent of @deliverable{D} configurations would be high for
 @${D=1} and reach @${100\%} at a low value, perhaps @${D=1.8}.
A @deliverable{1} configuration runs at least as fast as the untyped program.
The worst case is that only a small percent of configurations are @deliverable{TODO},
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
The improvement is most dramatic for @bm{synth}, in which the worst-case
 performance ovehead drops from @maxo['typed 'synth] to @maxo['tagged 'synth],
 mostly because Typed Racket @bm{synth} spends a large amount of time
 eagerly traversing data structures and monitoring their components.
@; FSM also dramatic, removes huge indirection cost

The @bm{zombie} benchmark shows only a minor improvement;
 few configurations are @deliverable{10} in either Typed Racket or @|LD-Racket|.
We remark, however, that the worst-case overhead in Typed Racket for @bm{zombie}
 is @maxo['typed 'zombie] whereas the worst-case for @|LD-Racket|
 is far lower, at @maxo['tagged 'zombie].

The @bm{morsecode} benchmark is an anomaly.
Using @|LD-Racket|
 increases its worst-case overhead from @maxo['typed 'morsecode #:precision '(= 1)]
 to @maxo['tagged 'morsecode #:precision '(= 1)].
This degredation occurs because the pervasive type-tag checks of @|LD-Racket|
 introduce more overhead than the boundary checks inserted by Typed Racket.


@section{Evaluation II: Fully-Typed Programs}

TBA


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
 error messages, but they can add prohibitive overheads.
Perhaps the implementation of contracts could be improved; perhaps they
 are just the wrong tool for implementing frequently-executed assert statements.

@; === things that make prototype too slow
On the other hand, the performance of the prototype could be improved in two
 obvious ways.
First, @|LD-Racket| does not take advantage of the @|TR| optimizer
 to remove type-tag checks from primitive operations.
Second, the prototype could use type-based static analysis
 to detect redundant type-tag checks.

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


@;@section{Compiling to a Host Language}
@;
@;The models employ a small-step operational semantics for an expression
@; language.  Indeed, the type-sound ones (natural, co-natural, forgetful,
@; and locally-defensive) use two mutually-recursive reduction relations.  In
@; practice, though, a migratory typing system for a language @${\langD}
@; compiles statically-typed code to this host language, which raises two
@; questions.
@;
@;The first question is how to represent the static types that the models use
@; in monitor values and function applications. A suitable compiled
@; representation for @${(\vmonfun{\tarr{\tau_d}{\tau_c}}{v})} is
@; @${(\vmonfun{\vpair{e_d}{e_c}}{v})} where @${e_d} is a host-language
@; function that checks whether a value matches the domain type.  In the
@; forgetful variant, the domain of @${(\vlam{\tann{x}{\tau}}{e})} can
@; replace the domain type in its enclosing monitor. In the locally-defensive
@; variant, @${(\vlam{\tann{x}{\tau}}{e})} compiles to a function that checks
@; the actual value of @${x} against the type @${\tau} before executing the
@; function body. @;{ @~cite[vss-popl-2017].}
@;
@;The second question is whether it is sound to use the @${\langD} reduction
@; relation on statically-typed terms. Indeed, all of our models do not need
@; separate reduction relations other than for the soundness proofs in the
@; preceding section.  The reductions differ in two minor aspects: how they
@; interpose boundary terms and how many run-time checks they perform.  As
@; for the boundaries, they become irrelevant in an implementation because
@; the set of values are the same. As for the run-time checks, the static
@; reduction can skip checks that the dynamic reduction must perform, i.e., 
@; it is safe to use the more conservative, dynamically-typed reduction
@; relation.
@;
