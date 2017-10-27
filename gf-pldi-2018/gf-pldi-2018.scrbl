#lang gf-pldi-2018 @sigplan @anonymous

@; TODO fix the title
@title{Forgetful, First-Order Embedding}
@;@subtitle{with applications to gradual typing}
@;@title{Between Soundness and Unsoundness and What it Means for Performance}
@;@title{An Unexpectedly Negative Result}

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

@; TODO fix the abstract
@abstract{
  We present a techinque for embedding statically typed code in dynamically-typed
   code, and vice-versa.
  This technique is called the forgetful, first-order embedding.
  It strikes a balance between the natural embedding (formalized by Matthews/Findler
   and implemented in Typed Racket) and the identity embedding (implemented
   in TypeScript).
  The balance comes in two senses.
  First, N-embedded programs run slower than F-embedded program run slower
   than I-embedded programs.
  Second, I-embedded programs have weaker static guarantees than F-embedded
   programs have weaker guarantees than N-embedded programs.
  We prove these claims for a model, and demonstrate them in an implementation.
}

@include-section{introduction.scrbl}
@include-section{background.scrbl}
@include-section{design.scrbl}
@include-section{evaluation.scrbl}
@include-section{reduce-checks-improve-errors.scrbl}
@include-section{conclusion.scrbl}

@generate-bibliography[]

@include-section{appendix.scrbl}
