#lang gf-icfp-2018
@require{techreport.rkt}
@appendix-title{Performance vs. Number of Typed Modules}

@figure*["fig:locally-defensive-linear"
         @elem{@|TR_LD| (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample| )}
  (exact-plot* (map list TR-DATA* TAG-DATA*))]

@Figure-ref{fig:locally-defensive-linear} plots the number of typed modules (@|x-axis|)
 in a configuration against its running time in milliseconds (@|y-axis|).
To reduce visual overlap, the points representing configurations with @${N}
 modules are evenly spaced along the @|x-axis| along the interval @${N\pm 0.4}.

The figures support three main conclusions.
First, the orange points for @|TR_LD| are in general significantly lower
 (i.e., show better performance) than the points for @|TR_N|.
Second, the performance of @|TR_LD| tends to degrade linearly as the number
 of typed modules increases.
This slowdown levels off at the right-most end because the implementation
 skips the codomain check on calls to statically-typed functions.
Third, the performance of @|TR_N| has an umbrella shape.
The worst performance is in the middle, but the fully-typed performance is
 better than @|TR_LD|.

