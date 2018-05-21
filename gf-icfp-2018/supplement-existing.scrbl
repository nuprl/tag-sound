#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Existing Systems}

Technical summary of existing systems, both from academia and industry.

The summaries are vaguely similar to the semantic framework in the paper.
For each system:

@itemlist[
@item{
  types
}
@item{
  values
}
@item{
  static boundaries
}
@item{
  boundary functions
}
]


@; -----------------------------------------------------------------------------

@; -----------------------------------------------------------------------------
@section[#:tag "existing-thorn"]{Thorn}

@include-figure["fig:existing-thorn.tex" @elem{Thorn types, values, and boundary functions. The @${\vfromdyn} boundary function is undefined for all inputs.}]

@Figure-ref{fig:existing-thorn} summarizes Thorn.

The actual paper uses a heap. We do not.

Thorn lets values pass from static to dynamic at runtime.
Thorn does not let values cross from dynamic to static without an explicit type
 cast; all Thorn programs must pass the static type checker, and the static type
 checker rejects programs that send a more dynamic variable into a less dynamic context.

Values are pointers to objects.
A pointer may be wrapped in at most one cast.

@tr-lemma[#:key "thorn-canonical" @elem{Thorn canonical forms}]{
  @itemlist[
    @item{
      If @${\Gamma \vdash v : C} then @${v \valeq C'(f = v_f, \ldots)} and @${C' \subteq C}.
    }
    @item{
      If @${\vdash v : \thornlike{C}} then @${v \valeq \thorncast{\thornlike{C}}{p}}
    }
    @item{
      If @${\vdash v : \thorndyn} then @${v \valeq \thorncast{\thorndyn}{p}}
    }
  ]
}

