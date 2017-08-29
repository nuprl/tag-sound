#lang gf-pldi-2018 @sigplan @anonymous

@title{Between Soundness and Unsoundness and What it Means for Performance}

@(define NEU
   @affiliation[
     #:institution "Northeastern University"
     @;#:city "Boston"
     @;#:state "Massachusetts"
     @;#:postcode "02115"
     @;#:country "USA"
   ])

@author["Ben Greenman"
        #:email "benjaminlgreenman@gmail.com"
        #:orcid "0000-0001-7078-9287"
        #:affiliation NEU]

@; -----------------------------------------------------------------------------

@abstract{
  Typed Racket implements a generalized form type soundness.
  The run-time cost of enforcing this type soundness is high.

  Reticulated Python implements tag soundness; a term with the static type
   @${\tlist(\tint)} can evaluate to any kind of list.
  The run-time cost of enforcing this type soundness appears significantly
   lower than the cost of enforcing generalized soundness.

  This paper measures the cost of generalized soundness compared to tag
   soundness in the context of Typed Racket.
}

@include-section{introduction.scrbl}
@include-section{background.scrbl}
@include-section{design.scrbl}
@include-section{evaluation.scrbl}
@include-section{conclusion.scrbl}

@generate-bibliography[]

@include-section{appendix.scrbl}
