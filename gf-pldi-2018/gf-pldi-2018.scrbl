#lang gf-pldi-2018 @sigplan

@title{Between Soundness and Unsoundness and What it Means for Performance}
@; k but this title is no longer accurate, it's no longer about soundness
@; its about "Call-by-Name, Call-by-Value" except its types and there's no names
@; I guess see CBPV for terms

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
  TODO
}

@include-section{introduction.scrbl}
@include-section{related-work.scrbl}

@generate-bibliography[]

@include-section{appendix.scrbl}
