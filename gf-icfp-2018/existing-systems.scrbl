#lang gf-icfp-2018
@title[#:tag "sec:existing-systems"]{Existing Systems}

@figure["fig:existing-systems" "Existing migratory typing systems"
  @list[
    @tabular[
      #:sep (hspace 2)
      #:style 'block
      #:row-properties '(left right)
      #:column-properties '(right)
      (list
        (list @bold{System}
              @bold{Types Optional?} @bold{Implicit Casts} @${\vfromdyn} @${\vfromsta} @${\carrow} @bold{Soundness})
        (list "Gradualtalk, Typed Racket"
              "" "" "" "" "" "")
        (list "TPD"
              "X" "X" "X" "X" "-"  "N")
        (list "TypeScript, StrongTalk, Hack"
              "" "" "" "" "" "")
        (list "Flow, mypy, Typed Clojure"
              "" "" "" "" "" "")
        (list "Typed Lua, Pyre, Pytype"
              "X" "X" "X" "X" "-"  "E")
        (list "Reticulated"
              "X" "X" "X" "X" "X" "LD")
        (list "Pyret"
              "X" "X" "X" "X" "X" "LD*")
        (list "Dart 2.0, Safe TypeScript"
              "-"  "X" "-"  "X" "-"  "H")
        (list "StrongScript, Thorn"
              "-"  "-"  "-"  "X" "-"  "H"))
      @; shen grace
    ]
    @tabular[
      #:sep (hspace 2)
      #:style 'block
      #:row-properties '(left)
      #:column-properties '(left)
      (list
        (list @bold{Soundness} @bold{Description})
        (list "N" "Preserves types")
        (list "E" "Avoids undefined behavior")
        (list "LD" "Preserves type constructors")
        (list "H" "Preserves heap value types"))
    ]
  ]
]

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


