#lang gf-pldi-2018

@appendix-title{Multi-Language}
@include-figure*["fig:mixed-lang.tex" @elem{Static/Dynamic Multi-language}]

@; NOTE need this because tagged depends on it

@lemma[@elem{@${\langM} inversion} #:key "lemma:LM-inversion"]{
}
  @itemlist[
    @item{
      If @${\Delta(\vfst, \tau) = \tau'} then @${\tau = \tpair{\tau_0}{\tau_1}} and @${\tau' = \tau_0}
    }
    @item{
      If @${\Delta(\vsnd, \tau) = \tau'} then @${\tau = \tpair{\tau_0}{\tau_1}} and @${\tau' = \tau_1}
    }
  ]

@proof{
  Immediate
}
