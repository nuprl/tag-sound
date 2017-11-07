#lang gf-pldi-2018 @sigplan @anonymous

@title{The Spectrum of Soundness and Performance}
@; one small tag for gradual typing
@; 

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

@author["Matthias Felleisen"
        #:email "matthias@ccs.neu.edu"
        #:affiliation NEU]

@; -----------------------------------------------------------------------------

@abstract{Gradual typing provides software developers with the means to
 re-factor an untyped code base into a typed one. As this re-factoring
 proceeds, the code base becomes a mixture of typed and untyped code.  In
 this mixed-typed world, developers may wish to rely on the soundness of
 the type system. Industrial variants of gradual typing, however, guarantee
 only an extremely limited form of soundness, and as recently shown, the
 soundness of academic implementations poses a serious performance
 bottleneck, which limits the deployability of mixed-typed software.

@;{NOTE remove 'novel' when paper is accepted}

In this paper, we develop the novel idea of a spectrum of type soundness and
 demonstrate that a form of whole-program, non-compositional form of
 soundness vastly improves the performance of Typed Racket, the most mature
 implementation of sound gradual typing. Specifically, we develop a series
 of theoretical models of gradual typing, starting with a classically sound
 gradual core language. Furthermore, we explain how to modify Typed Racket's
 implementation and present the results of measuring this revised
 implementation on the Takikawa-Greenman benchmarks.}

@include-section{introduction.scrbl}
@include-section{background.scrbl}
@include-section{design.scrbl}
@include-section{implementation.scrbl}
@;@include-section{reduce-checks-improve-errors.scrbl}
@include-section{evaluation.scrbl}
@include-section{related-work.scrbl}
@include-section{conclusion.scrbl}

@generate-bibliography[]

@include-section{appendix.scrbl}
