#lang gf-icfp-2018 @sigplan @10pt @anonymous @review

@title{The Spectrum of Soundness and Performance}
@subtitle{Supplementary Material}

This appendix contains:
@itemlist[
@item{
  brief descriptions of the benchmark programs;
}
@item{
  a set of figures comparing the running time of a configuration to the number
   of type annotations;
}
@item{
  a comparison between the implementations of Typed Racket and Tag-Sound Racket;
}
@item{
  complete definitions for the embeddings discussed in the paper; and
}
@item{
  complete traces of the expression @${\erelprime} in each embedding.
}
]

@;Supplementary materials include:
@; a PLT Redex development,
@; code for the benchmarks,
@; scripts to collect data,
@; the source code for Tag-Sound Racket,
@; a diff between Typed Racket and Tag-Sound Racket.


@include-section{supplement-descriptions.scrbl}
@include-section{supplement-linear.scrbl}
@include-section{supplement-implementation.scrbl}
@include-section{supplement-model.scrbl}
@include-section{supplement-reduction.scrbl}
