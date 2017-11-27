#lang gf-pldi-2018

@section{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-embedding.tex" "Tagged Embedding"]
@include-figure*["fig:locally-defensive-completion.tex" "Tagged Completion"]

@|K-SAFETY|
@proof{
  TODO
}


@lemma[@elem{@${K \subt K} finite}]{
  All chains @${K_0 \subt \cdots \subt K_n} are finite.
}
@proof{
  By definition. The longest chain is @${\knat \subt \kint \subt \kany}.
}
