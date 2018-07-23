#lang gf-icfp-2018 @sigplan @10pt @review
@require[scriblib/autobib]

@title{A Spectrum of Type Soundness and Performance}
@subtitle{Supplementary Material}

@(define NEU
   @affiliation[
     #:institution "PLT @ Northeastern University"
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
        @;#:email "matthias@ccs.neu.edu"
        #:affiliation NEU]

@acmPrice{}
@acmDOI{}
@acmYear{2018}
@acmConference["NU-CCIS-2018-002" "2018" "Northeastern University"]
@;@acmJournal{PACMPL}
@;@acmVolume{2}
@;@acmNumber{ICFP}
@;@acmArticle{5}
@;@acmMonth{9}

@table-of-contents[]

@;Supplementary materials include:
@; a PLT Redex development,
@; code for the benchmarks,
@; scripts to collect data,
@; the source code for Tag-Sound Racket,
@; a diff between Typed Racket and Tag-Sound Racket.


@include-section{supplement-descriptions.scrbl}
@include-section{supplement-linear.scrbl}
@include-section{supplement-implementation.scrbl}
@include-section{supplement-existing.scrbl}
@include-section{supplement-model.scrbl}

