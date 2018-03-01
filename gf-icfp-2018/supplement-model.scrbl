#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Models}

This section contains full definitions of the languages
 and full proofs of our claims about each language.

Aside from the common notions in @section-ref{appendix:preliminaries},
 the definition and proofs of each model are independent.

@;@Figure-ref{fig:model-roadmap} presents an outline.


@; -----------------------------------------------------------------------------

@include-section{supplement-model-background.scrbl}

@;@figure["fig:model-roadmap" "Models Roadmap"
@;  @models-roadmap[
@;    #:D "I) Dynamic"
@;    #:S "II) Static"
@;    #:M "III) Multi-Language"
@;    #:E "IV) Erasure Embedding"
@;    #:N "V) Natural Embedding"
@;    #:L "VI) Co-Natural Embedding"
@;    #:F "VII) Forgetful Embedding"
@;    #:K "VIII) Tagged Embedding"]]

@; -----------------------------------------------------------------------------

@;@include-section{supplement-model-d.scrbl}
@;@include-section{supplement-model-s.scrbl}
@;@include-section{supplement-model-m.scrbl}

@include-section{supplement-model-e.scrbl}
@include-section{supplement-model-n.scrbl}
@include-section{supplement-model-c.scrbl}
@include-section{supplement-model-f.scrbl}
@include-section{supplement-model-k.scrbl}

@include-section{supplement-model-bridge.scrbl}
