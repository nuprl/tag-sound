#lang gf-pldi-2018

@title{Performance vs. Number of Typed Modules}

@figure*["fig:locally-defensive-linear"
         @elem{@|LD-Racket| (orange @|tag-color-sample| ) vs. Typed Racket (blue @|tr-color-sample| )}
  (exact-plot* (map list TR-DATA* TAG-DATA*))]

@Figure-ref{fig:locally-defensive-linear} plots the number of typed modules (@|x-axis|)
 in a configuration against its running time in milliseconds (@|y-axis|).
To reduce visual overlap, the points representing configurations with @${N}
 modules are evenly spaced along the @|x-axis| along the interval @${N\pm 0.4}.

Three results stand out.
First, the orange points for @|LD-Racket| significantly out-perform the points
 for Typed Racket.
Second, the performance of @|LD-Racket| tends to increase linearly as the number
 of typed modules increases.
This increase levels off a bit at the right-most end because the implementation
 skips the codomain check on calls to statically-typed functions.
Third, the performance of Typed Racket has an umbrella shape.
The worst performance is in the middle, but the fully-typed performance is
 better than @|LD-Racket|.

