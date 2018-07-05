#lang gf-icfp-2018 @acmsmall @10pt @screen

@; "Writing is nature's way of letting you know how sloppy your thinking is" -Dick Guindon
@; :)))

@title{A Spectrum of Type Soundness and Performance}

@(define NEU
   @affiliation[
     #:institution "PLT @ Northeastern University"
     @;#:city "Boston"
     @;#:state "Massachusetts"
     @;#:postcode "02115"
     #:country "USA"
   ])

@author["Ben Greenman"
        #:email "benjaminlgreenman@gmail.com"
        #:orcid "0000-0001-7078-9287"
        #:affiliation NEU]

@author["Matthias Felleisen"
        #:email "matthias@ccs.neu.edu"
        #:affiliation NEU]

@; -----------------------------------------------------------------------------

@abstract{
The literature on gradual typing presents three fundamentally
different ways of thinking about the integrity of programs that combine 
statically typed and dynamically typed code.
This paper presents a uniform semantic framework that explains all three approaches,
 illustrates how each approach affects a developer's work, and
 adds a systematic performance comparison for a single implementation platform.
}

@include-section{introduction.scrbl}
@include-section{design.scrbl}
@include-section{evaluation.scrbl}
@include-section{implications.scrbl}
@include-section{existing-systems.scrbl}
@include-section{related-work.scrbl}
@include-section{conclusion.scrbl}

@include-section{appendix.scrbl}

@generate-bibliography[]

