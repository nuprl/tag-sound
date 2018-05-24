#lang gf-icfp-2018
@title[#:tag "sec:existing-systems"]{Existing Systems}

@; columns ...
@; - overlap with D
@; - new vs. migratory
@; - 

@figure["fig:existing-systems" "Existing migratory typing systems, URLs accessed in March 2018."
  @tabular[
    #:sep (hspace 2)
    #:style 'block
    #:row-properties '(left left left bottom-border left left left bottom-border bottom-border bottom-border bottom-border)
    #:column-properties '(left center center center left)
    (list
      (list @bold{System}
            @bold{Migratory?}
            @bold{Untyped}
            @bold{Implicit}
            @bold{Soundness})
      (list ""
            ""
            @bold{Values?}
            @bold{Casts?}
            "")
      (list @elem{Gradualtalk@~cite[acftd-scp-2013], TPD@~cite[wmwz-ecoop-2017]}
            "" "" "" "")
      (list @elem{Typed Racket@~cite[tf-popl-2008]}
            "X" "X" "X" "preserves types")

      (list @elem{mypy, Flow, Hack, Pyre,}
            "" "" "" "")
      (list @elem{Pytype, rtc@~cite[rtsf-sac-2013], Strongtalk@~cite[bg-oopsla-1993],}
            "" "" "" "")
      (list @elem{TypeScript@~cite[bat-ecoop-2014], Typed Clojure@~cite[bdt-esop-2016]}
            "" "" "" "")
      (list @elem{Typed Lua@~cite[mmi-dls-2015]}
            "X" "X" "X" "erasure")

      (list @elem{Reticulated@~cite[vss-popl-2017]}
            "X" "X" "X" "preserves constructors")

      (list @elem{Pyret}
            "-" "X" "X" "checks constructors")

      (list @elem{Dart 2.0, Safe TypeScript@~cite[rsfbv-popl-2015]}
            "-" "-" "X" "preserves heap")

      (list @elem{StrongScript@~cite[rzv-ecoop-2015] Thorn@~cite[wnlov-popl-2010]}
            "-"  "-"  "-"  "preserves typability"))
  @;ActionScript@~cite[rch-popl-2012]
  @;Shen grace
  ]
]

Evaluate using criteria above, important because ...

@; Existing languages that combine static and dynamic typing use diverse strategies.


The table in @figure-ref{fig:existing-systems} summarizes existing languages
 that combine static and dynamic typing.
Three languages, in the first row, use the natural embedding;
 these languages eagerly enforce types on dynamically-typed values and
 attribute every boundary error to a syntactic boundary term.
Nine languages (second row) use the erasure embedding.
In these @emph{optionally typed} languages, the presence or absence of type
 annotations does not affect the behavior of a program.
Reticulated is the only existing system that implements the locally-defensive
 approach and preserves type constructors.
Pyret, however, is similar in that it compiles every type annotation to
 a type-constructor check.
If every expression in a Pyret program comes with a type annotation, then
 the evaluation of that program is likely to satisfy locally-defensive soundness
@; (theorem @tech[#:key "K-static-soundness"]{???}).
Dart (version 2.0) and Safe TypeScript are typed languages that include a
 dynamic type.
Every value in these languages comes with an intrinsic, static type but may
 flow in and out of a context expecting a value of the dynamic type.
StrongScript and Thorn allow only statically-typed values, but such values
 may be explicitly cast to and from a dynamic type.

@; Soundness key?
