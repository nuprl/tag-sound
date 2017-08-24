#lang gf-pldi-2018 @sigplan @anonymous

@title{Modes of Migratory Typing}
@;@title{Between Soundness and Unsoundness and What it Means for Performance}
@; k but this title is no longer accurate, it's no longer about soundness
@; its about "Call-by-Name, Call-by-Value" except its types and there's no names

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
  Different implementations of gradual typing implement different notions
   of type soundness.
  The choice of type soundness affects the performance
   of gradually typed programs.

  This paper introduces a modal migratory typing system, @|MMT|, with a generalized
   notion of type soundness that subsumes the soundnesses of
   Typed Racket, Reticulated, and TypeScript.
  Using @|MMT|, a language designer can precisely measure the cost of type
   soundness in a suite of programs.
  Furthermore, a programmer can use @|MMT| to trade
   dynamic type safety for performance.
  We validate these claims by extending Typed Racket with @|MMT| modalities.
}

@include-section{introduction.scrbl}
@include-section{related-work.scrbl}

@generate-bibliography[]

@include-section{appendix.scrbl}
