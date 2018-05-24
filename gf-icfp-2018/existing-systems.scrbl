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
        (list "Dart 2.0"
              "-"  "X" "-"  "X" "-"  "H")
        (list "StrongScript, Thorn"
              "-"  "-"  "-"  "X" "-"  "H"))
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

@Figure-ref{fig:existing-systems} catalogs existing systems.
