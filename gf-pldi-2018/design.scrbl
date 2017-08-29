#lang gf-pldi-2018

@title[#:tag "sec:design"]{Tag-Sound Gradual Typing}

@; TODO express as section

Primary design goals:
@itemlist[
@item{
  re-use Typed Racket type checker,
}
@item{
  type-tag soundness,
}
@item{
  separate compilation,
}
@item{
  dynamic type-checks run in @${O(1)} time and space,
}
@item{
  minimize the number of dynamic checks.
}
]

@;Secondary design goals:
@;@itemlist[
@;@item{
@;  no @tt{Dyn} type,
@;}
@;@item{
@;  sound for all of Racket (state, first-class classes),
@;}
@;]


@section{Model, Theorems}

TBA
