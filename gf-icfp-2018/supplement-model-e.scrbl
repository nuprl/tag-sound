#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Erasure Embedding}

@section{@${\langE} Definitions}
@exact{\input{fig:erasure-embedding.tex}}

@|clearpage|
@section{@${\langE} Properties}

@(begin
   (define E-progress @tr-ref[#:key "E-progress"]{progress})
   (define E-preservation @tr-ref[#:key "E-preservation"]{preservation})

   (define E-S-implies @tr-ref[#:key "E-S-implies"]{static implies})
   (define E-D-implies @tr-ref[#:key "E-D-implies"]{dynamic implies})

   (define E-uec @tr-ref[#:key "E-uec"]{unique evaluation contexts})
   (define E-hole-typing @tr-ref[#:key "E-hole-typing"]{hole typing})
   (define E-hole-subst @tr-ref[#:key "E-hole-subst"]{hole substitution})
   (define E-inversion @tr-ref[#:key "E-inversion"]{inversion})
   (define E-subst @tr-ref[#:key "E-subst"]{substitution})
   (define E-delta-preservation @tr-ref[#:key "E-delta-preservation"]{@${\delta} preservation})
   (define E-weakening @tr-ref[#:key "E-weakening"]{weakening})

   (define M-S-canonical @tr-ref[#:key "M-S-canonical"]{static canonical forms})

   (define M-uec @tr-ref[#:key "M-uec"]{@${\langM} unique static evaluation contexts})
)

@tr-theorem[#:key "E-soundness" @elem{@${\langE} soundness}]{
  If @${\wellM e : \tau}
   then @${\wellEE e} and either:
  @itemlist[
    @item{ @${e \rrEEstar v} and @${\wellEE v} }
    @item{ @${e \rrEEstar \tagerror} }
    @item{ @${e \rrEEstar \boundaryerror} }
    @item{ @${e} diverges }
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step[
      @${\wellEE e}
      @|E-S-implies|]}
    @item{@tr-qed{
      by @|E-progress| and @|E-preservation|
    }}
  ]
}

@tr-theorem[#:key "E-pure-static" @elem{@${\langE} static soundness}]{
  If @${\wellM e : \tau} and @${e} is purely static then either:
  @itemlist[
    @item{ @${e \rrEEstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrEEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  By @tr-ref[#:key "E-pure-static-progress"]{progress}
  and @tr-ref[#:key "E-pure-static-preservation"]{preservation} lemmas for
  @${\rrEEstar} and @${\wellM}.
}

@tr-lemma[#:key "E-S-implies" @elem{typing implies well-formedness}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellEE e}.
}@tr-proof{
  By structural induction on the typing relation.

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @${\tann{x}{\tau} \in \Gamma}
    @tr-step{
      @${\Gamma \wellEE x}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tau_d \tarrow \tau_c
              }}]{
    @tr-step[
      @${\tann{x}{\tau_d},\Gamma \wellEE e}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vlam{\tann{x}{\tau_d}}{e}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                i \in \naturals
              }{
                \Gamma \wellM i : \tnat
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellEE i : \tint
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\
                \Gamma \wellM e_1 : \tau_1
              }{
                \Gamma \wellM \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vpair{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_d \tarrow \tau_c
                \\
                \Gamma \wellM e_1 : \tau_d
              }{
                \Gamma \wellM e_0~e_1 : \tau_c
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vapp{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\
                \Delta(\vunop, \tau_0) = \tau
              }{
                \Gamma \wellM \vunop~e_0 : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \eunop{e_0}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\
                \Gamma \wellM e_1 : \tau_1
                \\
                \Delta(\vbinop, \tau_0, \tau_1) = \tau
              }{
                \Gamma \wellM \ebinop{e_0}{e_1} : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \ebinop{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau'
                \\
                \tau' \subt \tau
              }{
                \Gamma \wellM e : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellEE e}
      @tr-IH]
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \edyn{\tau}{e} : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellEE e}
      @|E-D-implies|]
    @tr-step{
      @${\Gamma \wellEE \edyn{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-D-implies" @elem{dynamic implies}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellEE e}.
}@tr-proof{
  By structural induction on the @${\wellM} relation.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @${x \in \Gamma}
    @tr-step{
      @${\Gamma \wellEE x}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e
              }{
                \Gamma \wellM \vlam{x}{e}
              }}]{
    @tr-step[
      @${x,\Gamma \wellEE e}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vlam{x}{e}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0
                \\
                \Gamma \wellM e_1
              }{
                \Gamma \wellM \vpair{e_0}{e_1}
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vpair{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0
                \\
                \Gamma \wellM e_1
              }{
                \Gamma \wellM e_0~e_1
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \vapp{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \vunop~e
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \eunop{e_0}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0
                \\
                \Gamma \wellM e_1
              }{
                \Gamma \wellM \ebinop{e_0}{e_1}
              }}]{
    @tr-step[
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellEE \ebinop{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau
              }{
                \Gamma \wellM \esta{\tau}{e}
              }}]{
    @tr-step[
      @${\Gamma \wellEE e}
      @|E-S-implies|]
    @tr-step{
      @${\Gamma \wellEE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-progress" @elem{@${\langE} progress}]{
  If @${\wellEE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccEE e'} }
    @item{ @${e \ccEE \tagerror} }
    @item{ @${e \ccEE \boundaryerror} }
  ]
}@tr-proof{
  By the @|E-uec| lemma, there are six possible cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step[
        @${e \ccEE \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrEE \vsubst{e'}{x}{v_1}}]
      @tr-qed[]
    }
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau}}{e'}}]{
      @tr-step[
        @${e \ccEE \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrEE \vsubst{e'}{x}{v_1}}]
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step[
        @${e \ccEE \tagerror}
        @${\vapp{v_0}{v_1} \rrEE \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-if[@${\delta(\vunop, v) = v'}]{
      @tr-step[
        @${e \ccEE \ctxE{v'}}
        @${(\eunop{v}) \rrEE v'}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step[
        @${e \ccEE \tagerror}
        @${(\eunop{v}) \rrEE \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = v'}]{
      @tr-step[
        @${e \ccEE \ctxE{v'}}
        @${(\ebinop{v_0}{v_1}) \rrEE v'}]
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step[
        @${e \ccEE \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrEE \boundaryerror}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step[
        @${e \ccEE \tagerror}
        @${(\ebinop{v_0}{v_1}) \rrEE \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{v}}}]{
    @tr-step[
      @${e \ccEE \ctxE{v}}
      @${\edyn{\tau}{v} \rrEE v}]
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\esta{\tau}{v}}}]{
    @tr-step[
      @${e \ccEE \ctxE{v}}
      @${\esta{\tau}{v} \rrEE v}]
    @tr-qed[]
  }

}

@tr-lemma[#:key "E-preservation" @elem{@${\langE} preservation}]{
  If @${\wellEE e} and @${e \ccEE e'} then @${\wellEE e'}.
}@tr-proof{
  By @|E-uec| there are five cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${v_0 = \vlam{x}{e'} \mbox{ or } v_0 = \vlam{\tann{x}{\tau}}{e'}
         @tr-and[]
         \ctxE{v_0~v_1} \ccEE \ctxE{\vsubst{e'}{x}{v_1}}}
    }
    @tr-step[
      @${\wellEE \vapp{v_0}{v_1}}
      @|E-hole-typing|
    ]
    @tr-step[
      @${\wellEE v_0
         @tr-and[]
         \wellEE v_1}
      @elem{@|E-inversion| (2)}
    ]
    @tr-step[
      @${x \wellEE e'}
      @elem{@|E-inversion| (3)}
    ]
    @tr-step[
      @${\wellEE \vsubst{e'}{x}{v_1}}
      @elem{@|E-subst| (3, 4)}
    ]
    @tr-qed{
      by @|E-hole-subst| (5)}
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step[
      @${\ctxE{\eunop{v}} \ccEE \ctxE{v'}
         @tr-and[]
         \delta(\vunop, v) = v'}]
    @tr-step[
      @${\wellEE \eunop{v}}
      @|E-hole-typing|]
    @tr-step[
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    ]
    @tr-step[
      @${\wellEE v'}
      @elem{@|E-delta-preservation| (1,3)}
    ]
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step[
      @${\ctxE{\ebinop{v_0}{v_1}} \ccEE \ctxE{v'}
         @tr-and[]
         \delta(\vbinop, v_0, v_1) = v'}]
    @tr-step[
      @${\wellEE \ebinop{v_0}{v_1}}
      @|E-hole-typing|]
    @tr-step[
      @${\wellEE v_0 @tr-and[] \wellEE v_1}
      @elem{@|E-inversion| (2)}
    ]
    @tr-step[
      @${\wellEE v'}
      @elem{@|E-delta-preservation| (3)}
    ]
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{v}}}]{
    @tr-step[
      @${\ctxE{\edyn{\tau}{v}} \ccEE v}]
    @tr-step[
      @${\wellEE \edyn{\tau}{v}}
      @|E-hole-typing|]
    @tr-step[
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    ]
    @tr-qed{
      by @|E-hole-subst| (3)}
  }

  @tr-case[@${e = \ctxE{\esta{\tau}{v}}}]{
    @tr-step[
      @${\ctxE{\esta{\tau}{v}} \ccEE v}]
    @tr-step[
      @${\wellEE \esta{\tau}{v}}
      @|E-hole-typing|]
    @tr-step[
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    ]
    @tr-qed{
      by @|E-hole-subst| (3)}
  }
}

@tr-lemma[#:key "E-pure-static-progress" @elem{@${\langE} pure static progress}]{
  If @${\wellM e : \tau} and @${e} is purely static, then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccEE e'} }
    @item{ @${e \ccEE \boundaryerror} }
  ]
}@tr-proof{
  By the @|E-uec| lemma, there are six cases to consider:

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau'}}{e'}}]{
      @tr-step[
        @${e \ccEE \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrEE \vsubst{e'}{x}{v_1}}]
      @tr-qed[]
    }
    @tr-else[@${v_0 = \vlam{x}{e'}
                @tr-or[4]
                v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-if[@${\delta(\vunop, v) = v'}]{
      @tr-step[
        @${e \ccEE \ctxE{v'}}
        @${(\eunop{v}) \rrEE v'}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = v'}]{
      @tr-step[
        @${e \ccEE \ctxE{v'}}
        @${(\ebinop{v_0}{v_1}) \rrEE v'}]
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step[
        @${e \ccEE \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrEE \boundaryerror}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\edyn{\tau'}{v}}}]{
    @tr-contradiction{@${e} is purely static}
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{v}}}]{
    @tr-contradiction{@${\wellM e : \tau}}
  }

}

@tr-lemma[#:key "E-pure-static-preservation" @elem{@${\langE} pure static preservation}]{
  If @${\wellM e : \tau} and @${e} is purely static and @${e \ccEE e'}
  then @${\wellM e' : \tau} and @${e'} is purely static.
}@tr-proof{
  By the @|M-uec| lemma, there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_d}}{e'}}]{
      @tr-step[
        @${\ctxE{v_0~v_1} \ccEE \ctxE{\vsubst{e'}{x}{v_1}}}]
      @tr-step[
        @${\wellM \eapp{v_0}{v_1} : \tau_c}]
      @tr-step{
        @${\wellM v_0 : \tarr{\tau_d}{\tau_c} @tr-and[] \wellM v_1 : \tau_d}
        (2)}
      @tr-step{
        @${\tann{x}{\tau_d} \wellM e' : \tau_c}
        (3)}
      @tr-step{
        @${\wellM \vsubst{e'}{x}{v_1} : \tau_c}
        (3, 4)}
      @tr-step[
        @elem{@${\vsubst{e'}{x}{v_1}} is purely static}
        @elem{@${e'} and @${v_1} are purely static}]
      @tr-qed[]
    }
    @tr-else[]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step[
      @${\ctxE{\eunop{v}} \ccEE \ctxE{v'}
         @tr-and[]
         \delta(\vunop, v) = v'}]
    @tr-step[
      @${\wellM \eunop{v} : \tau'}]
    @tr-step[
      @${\wellM v : \tau_0}]
    @tr-step[
      @${\wellM v' : \tau'}]
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step[
      @${\ctxE{\ebinop{v_0}{v_1}} \ccEE \ctxE{v'}
         @tr-and[]
         \delta(\vbinop, v_0, v_1) = v'}]
    @tr-step[
      @${\wellM \ebinop{v_0}{v_1} : \tau'}]
    @tr-step[
      @${\wellM v_0 : \tau_0 @tr-and[] \wellM v_1 : \tau_1}
    ]
    @tr-step[
      @${\wellM v' : \tau'}
    ]
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{v}}}]{
    @tr-contradiction{@${e} is purely static}
  }

}

@tr-lemma[#:key "E-uec" @elem{@${\langE} unique evaluation contexts}]{
  If @${\wellEE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{v}}} }
    @item{ @${e = \ctxE{\esta{\tau}{v}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction[@${\wellEE e}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ES_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${E = \vpair{\ES_0}{e_1}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${\wellEE e_1}
        @|E-inversion|}
      @tr-step{
        @${e_1 = \ES_1[e_1']}
        @tr-IH
      }
      @tr-step{
        @${E = \vpair{e_0}{\ES_1}}
      }
      @tr-qed{
        @${e = \ctxE{e_1'}}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @tr-qed[]
    }
  }

  @tr-case[@${e = e_0~e_1} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \ED_0~e_1}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${\wellEE e_1}
        @|E-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH
      }
      @tr-step{
        @${\ED = e_0~\ED_1}
      }
      @tr-qed{
        @${e = \ctxE{e_1'}}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed[]
    }
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \eunop{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${E = \ehole}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \ebinop{\ED_0}{e_1}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${\wellEE e_1}
        @|E-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \ebinop{e_0}{\ED_1}}
      }
      @tr-qed{
        @${e = \ctxE{e_1'}}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{ }
    }
  }

  @tr-case[@${e = \edyn{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \edyn{\tau}{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
      }
    }
  }

  @tr-case[@${e = \esta{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellEE e_0}
        @|E-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \esta{\tau}{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{ }
    }
  }
}

@tr-lemma[#:key "E-hole-typing" @elem{@${\langE} hole typing}]{
  If @${\wellEE \ctxE{e}} then the derivation contains a sub-term @${\wellEE e}
}@tr-proof{
  By induction on the structure of @${\ED}.

  @tr-case[@${\ED = \ehole}]{
    @tr-qed{@${\ctxE{e} = e}}
  }

  @tr-case[@${\ED = \ED_0~e_1}]{
    @tr-step{
      @${\ctxE{e} = \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = v_0~\ED_1}]{
    @tr-step{
      @${\ctxE{e} = v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vpair{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vpair{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \eunop{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \edyn{\tau}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \esta{\tau}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

}

@tr-lemma[#:key "E-hole-subst" @elem{@${\langE} hole substitution}]{
  If @${\wellEE \ctxE{e}} and @${\wellEE e'} then @${\wellEE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\ED}.

  @tr-case[@${\ED = \ehole}]{
    @tr-qed{
      @${\ctxE{e'} = e'}
    }
  }

  @tr-case[@${\ED = \vpair{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}
        @tr-and[]
        \ctxE{e'} = \vpair{\ED_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellEE \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]
         @tr-and[]
         \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \vpair{\ED_0[e']}{e_1}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \vpair{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{v_0}{\ED_1[e]}
         @tr-and[]
         \ctxE{e'} = \vpair{v_0}{\ED_1[e']}}
    }
    @tr-step{
      @${\wellEE \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellEE v_0
         @tr-and[]
         \wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \vpair{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \ED_0~e_1}]{
    @tr-step{
      @${\ctxE{e} = \ED_0[e]~e_1
        @tr-and[]
        \ctxE{e'} = \ED_0[e']~e_1}
    }
    @tr-step{
      @${\wellEE \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellEE \ED_0[e]
         @tr-and[]
         \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \ED_0[e']~e_1}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = v_0~\ED_1}]{
    @tr-step{
      @${\ctxE{e} = v_0~\ED_1[e]
         @tr-and[]
         \ctxE{e'} = v_0~\ED_1[e']}
    }
    @tr-step{
      @${\wellEE v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellEE v_0
         @tr-and[]
         \wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE v_0~\ED_1[e']}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \eunop{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \eunop{\ED_0[e]}
        @tr-and[]
        \ctxE{e'} = \eunop{\ED_0[e']}}
    }
    @tr-step{
      @${\wellEE \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \eunop{\ED_0[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}
        @tr-and[]
        \ctxE{e'} = \ebinop{\ED_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellEE \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]
         @tr-and[]
         \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \ebinop{\ED_0[e']}{e_1}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}
         @tr-and[]
         \ctxE{e'} = \ebinop{v_0}{\ED_1[e']}}
    }
    @tr-step{
      @${\wellEE \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellEE v_0
         @tr-and[]
         \wellEE \ED_1[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \ebinop{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \edyn{\tau}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau}{\ED_0[e]}
        @tr-and[]
        \ctxE{e'} = \edyn{\tau}{\ED_0[e']}}
    }
    @tr-step{
      @${\wellEE \edyn{\tau}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \edyn{\tau}{\ED_0[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \esta{\tau}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau}{\ED_0[e]}
        @tr-and[]
        \ctxE{e'} = \esta{\tau}{\ED_0[e']}}
    }
    @tr-step{
      @${\wellEE \esta{\tau}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellEE \ED_0[e]}
      @|E-inversion|
    }
    @tr-step{
      @${\wellEE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellEE \esta{\tau}{\ED_0[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@tr-lemma[#:key "E-inversion" @elem{@${\wellEE} inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellEE \vapp{e_0}{e_1}} then @${\Gamma \wellEE e_0} and @${\Gamma \wellEE e_1}
    }
    @item{
      If @${\Gamma \wellEE \vlam{x}{e}} then @${x,\Gamma \wellEE e}
    }
    @item{
      If @${\Gamma \wellEE \vlam{\tann{x}{\tau}}{e}} then @${\tann{x}{\tau},\Gamma \wellEE e}
    }
    @item{
      If @${\Gamma \wellEE \eunop{e}} then @${\Gamma \wellEE e}
    }
    @item{
      If @${\Gamma \wellEE \ebinop{e_0}{e_1}} then @${\Gamma \wellEE e_0} and @${\Gamma \wellEE e_1}
    }
    @item{
      If @${\Gamma \wellEE \edyn{\tau}{e}} then @${\Gamma \wellEE e}
    }
    @item{
      If @${\Gamma \wellEE \esta{\tau}{e}} then @${\Gamma \wellEE e}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\wellEE e}.
  }
}

@tr-lemma[#:key "E-subst" @elem{@${\langE} substitution}]{
  If @${x,\Gamma \wellEE e} or @${\tann{x}{\tau},\Gamma \wellEE e},
  and @${\wellEE v}
  then @${\Gamma \wellEE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\Gamma \wellEE v}
      @elem{@|E-weakening|}
    }
    @tr-qed[]
  }

  @tr-case[@${e = x'}]{
    @tr-qed{
      by @${\vsubst{x'}{x}{v} = x'}
    }
  }

  @tr-case[@${e = i}]{
    @tr-qed{
      by @${\vsubst{i}{x}{v} = i}
    }
  }

  @tr-case[@${e = \vlam{x}{e'}}]{
    @tr-qed{
      by @${\vsubst{(\vlam{x}{e'})}{x}{v} = \vlam{x}{e'}}
    }
  }

  @tr-case[@${e = \vlam{\tann{x}{\tau'}}{e'}}]{
    @tr-qed{
      by @${\vsubst{(\vlam{\tann{x}{\tau'}}{e'})}{x}{v} = \vlam{\tann{x}{\tau'}}{e'}}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{x'}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${x',x,\Gamma \wellEE e'}
      @|E-inversion|
    }
    @tr-step{
      @${x',\Gamma \wellEE \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \vlam{x'}{\vsubst{e'}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellEE e'}
      @|E-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellEE \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e_0
         @tr-and[]
         x,\Gamma \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellEE \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e_0
         @tr-and[]
         x,\Gamma \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellEE \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e_0}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e_0}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e_0
         @tr-and[]
         x,\Gamma \wellEE e_1}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellEE \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e'}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \edyn{\tau'}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellEE e'}
      @|E-inversion|
    }
    @tr-step{
      @${\Gamma \wellEE \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellEE \esta{\tau'}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

}

@tr-lemma[#:key "E-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellEE v} and @${\delta(\vunop, v) = v'} then @${\wellEE v'}
    }
    @item{
      If @${\wellEE v_0} and @${\wellEE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellEE v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellEE v_0}
      @|E-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellEE v_1}
      @|E-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsum, v_0, v_1) = v_0 + v_1}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \floorof{v_0 / v_1}}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellEE e} then @${x,\Gamma \wellEE e}
    }
    @item{
      If @${\Gamma \wellEE e} then @${\tann{x}{\tau},\Gamma \wellEE e}
    }
  ]
}

@tr-lemma[#:key "E-Delta-type-soundness" @elem{@${\Delta} type soundness}]{
  If @${\wellM v_0 : \tau_0 \mbox{ and }
        \wellM v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then either:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellM v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on the definition of @${\Delta}.

  @tr-case[@${\Delta(\vsum, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|M-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 \in \naturals}
    }
    @tr-qed{ }
  }

  @tr-case[@${\Delta(\vsum, \tint, \tint) = \tint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|M-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 \in i}
    }
    @tr-qed{ }
  }

  @tr-case[@${\Delta(\vquotient, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|M-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1} \in \naturals}
        }
        @tr-qed{}
      }
    ]
  }

  @tr-case[@${\Delta(\vquotient, \tint, \tint) = \tint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|M-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror} }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1} \in i }}
        @tr-qed{}
      }
    ]
  }
}

@tr-lemma[#:key "M-uec" @elem{@${\langM} unique static evaluation contexts}]{
  If @${\wellM e : \tau} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{e'}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @tr-qed{@${e} is a value}
  }

  @tr-case[@${e = \esta{\tau}{e'}}]{
    @tr-contradiction[@${\wellKE e : K}]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ES_0[e_0']}
        @|tr-IH|
      }
      @${E = \vpair{\ES_0}{e_1}}
      @tr-qed{
        by @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ES_1[e_1']}
        @|tr-IH|
      }
      @tr-step{
        @${E = \vpair{e_0}{\ES_1}}
      }
      @tr-qed{
        by @${e = \ctxE{e_1'}}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @tr-step{@${\ED = \ehole}}
      @tr-qed{@${e = \ctxE{\vpair{e_0}{e_1}}}}
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|tr-IH|
      }
      @tr-step{
        @${\ED = \vapp{\ED_0}{e_1}}
      }
      @tr-qed{
        by @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @|tr-IH|
      }
      @tr-step{
        @${\ED = \vapp{e_0}{\ED_1}}
      }
      @tr-qed{
        by @${e = \ctxE{e_1'}}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{@${e = \ctxE{\vapp{e_0}{e_1}}}}
    }
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \eunop{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${E = \ehole}
      @tr-qed{@${e = \ctxE{\eunop{e_0}}}}
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \ebinop{\ED_0}{e_1}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \ebinop{e_0}{\ED_1}}
      }
      @tr-qed{@${e = \ctxE{e_1'}}}
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{@${e = \ctxE{\ebinop{e_0}{e_1}}}}
    }
  }

  @tr-case[@${e = \edyn{\tau}{e_0}}]{
    @${\ED = \ehole}
    @tr-qed{
      @${e = \ctxE{\edyn{\tau}{e_0}}}
    }
  }

}

@tr-lemma[#:key "M-S-canonical" @elem{@${\langM} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellM v : \tpair{\tau_0}{\tau_1}}
      then @${v \eeq \vpair{v_0}{v_1}}
    }
    @item{
      If @${\wellM v : \tarr{\tau_d}{\tau_c}}
      then @${v \eeq \vlam{\tann{x}{\tau_x}}{e'} @tr-and[] \tau_d \subteq \tau_x}
    }
    @item{
      If @${\wellM v : \tint} then @${v \eeq i}
    }
    @item{
      If @${\wellM v : \tnat}
      then @${v \eeq i} and @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellM e : \tau}
  }
}
