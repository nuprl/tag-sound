#lang gf-pldi-2018
@require{techreport.rkt}

@appendix-title{Models}

This section contains full definitions of the languages
 and full proofs of our claims about each language.

Aside from the common notions in @section-ref{appendix:preliminaries},
 the definition and proofs of each model are independent.

@Figure-ref{fig:model-roadmap} presents an outline.


@; -----------------------------------------------------------------------------

@include-section{appendix-model-background.scrbl}

@figure["fig:model-roadmap" "Models Roadmap"
  @models-roadmap[
    #:D "I) Dynamic"
    #:S "II) Static"
    #:M "III) Multi-Language"
    #:E "IV) Erasure Embedding"
    #:N "V) Natural Embedding"
    #:L "VI) Co-Natural Embedding"
    #:F "VII) Forgetful Embedding"
    #:K "VIII) Tagged Embedding"]]

@; -----------------------------------------------------------------------------

@;@include-section{appendix-model-d.scrbl}
@;@include-section{appendix-model-s.scrbl}

@;@include-section{appendix-model-m.scrbl}

@;@include-section{appendix-model-e.scrbl}
@;@include-section{appendix-model-n.scrbl}
@;@include-section{appendix-model-c.scrbl}
@;@include-section{appendix-model-f.scrbl}

@;@include-section{appendix-model-k.scrbl}
