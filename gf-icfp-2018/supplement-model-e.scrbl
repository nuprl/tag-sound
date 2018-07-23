#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{(@${\langE}) @|EOlong| Embedding}

@section{@|EOlong| Definitions}
@exact{\input{fig:erasure-embedding.tex}}

@|clearpage|
@section{@|EOlong| Theorems}

@(begin
   (define E-S-soundness @tr-ref[#:key "E-S-soundness"]{static @${\langE} soundness})

   (define E-progress @tr-ref[#:key "E-progress"]{@${\langE} progress})
   (define E-preservation @tr-ref[#:key "E-preservation"]{@${\langE} preservation})

   (define E-bf-progress @tr-ref[#:key "E-bf-progress"]{boundary-free progress})
   (define E-bf-preservation @tr-ref[#:key "E-bf-preservation"]{broundary-free preservation})

   (define E-S-implies @tr-ref[#:key "E-S-implies"]{static subset})
   (define E-D-implies @tr-ref[#:key "E-D-implies"]{dynamic subset})

   (define E-uec @tr-ref[#:key "E-uec"]{unique evaluation contexts})
   (define E-hole-typing @tr-ref[#:key "E-hole-typing"]{hole typing})
   (define E-hole-subst @tr-ref[#:key "E-hole-subst"]{hole substitution})
   (define E-inversion @tr-ref[#:key "E-inversion"]{@${\langE} inversion})
   (define E-subst @tr-ref[#:key "E-subst"]{substitution})
   (define E-delta-preservation @tr-ref[#:key "E-delta-preservation"]{@${\delta} preservation})
   (define E-weakening @tr-ref[#:key "E-weakening"]{weakening})

   (define E-fromdyn-soundness @tr-ref[#:key "E-fromdyn-soundness"]{@${\vfromdynE} soundness})
   (define E-fromsta-soundness @tr-ref[#:key "E-fromsta-soundness"]{@${\vfromstaE} soundness})

   (define M-uec @tr-ref[#:key "M-uec"]{unique static evaluation contexts})
   (define M-subst @tr-ref[#:key "M-subst"]{substitution})
   (define M-delta-preservation @tr-ref[#:key "M-delta-preservation"]{@${\delta} preservation})
   (define M-weakening @tr-ref[#:key "M-weakening"]{weakening})
   (define M-S-canonical @tr-ref[#:key "M-S-canonical"]{static canonical forms})
   (define M-S-inversion @tr-ref[#:key "M-S-inversion"]{static inversion forms})

)

@; -----------------------------------------------------------------------------

@tr-theorem[#:key "E-S-soundness" @elem{static @${\langE}-soundness}]{
  If @${\wellM e : \tau}
   then @${\wellEE e} and one of the following holds:
  @itemlist[
    @item{ @${e \rrESstar v} and @${\wellEE v} }
    @item{ @${e \rrESstar \tagerror} }
    @item{ @${e \rrESstar \boundaryerror} }
    @item{ @${e} diverges }
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellEE e}
      @|E-S-implies|}}
    @item{@tr-qed{
      by @|E-progress| and @|E-preservation|
    }}
  ]
}

@tr-theorem[#:key "E-D-soundness" @elem{dynamic @${\langE}-soundness}]{
  If @${\wellM e}
   then @${\wellEE e} and one of the following holds:
  @itemlist[
    @item{ @${e \rrEDstar v} and @${\wellEE v} }
    @item{ @${e \rrEDstar \tagerror} }
    @item{ @${e \rrEDstar \boundaryerror} }
    @item{ @${e} diverges }
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\rrEDstar = \rrESstar}
      definition
    }}
    @item{@tr-qed{
      by @|E-S-soundness|
    }}
  ]
}

@tr-remark[#:key "E-compilation" @elem{@${\langE}-compilation}]{
  The @${\rrESstar} and @${\rrEDstar} relations are identical.
  In practice, uses of @${\rrESstar} may be replaced with @${\rrEDstar}.
}
@linebreak[]

@tr-theorem[#:key "E-bf-soundness" @elem{boundary-free @${\langE}-soundness}]{
  If @${\wellM e : \tau} and @${e} is boundary-free then one of the following holds:
  @itemlist[
    @item{ @${e \rrESstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrESstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @tr-qed{
    by @|E-bf-progress| and @|E-bf-preservation|.
  }
}

@; -----------------------------------------------------------------------------
@|clearpage|
@section{@|EOlong| Lemmas}

@tr-lemma[#:key "E-fromdyn-soundness" @elem{@${\vfromdynE} soundness}]{
  If @${\wellEE v} then @${\wellEE \efromdynE{\tau}{v}}.
}@tr-proof{
  @tr-case[@${\efromdynE{\tau}{v} = v}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-fromsta-soundness" @elem{@${\vfromstaE} soundness}]{
  If @${\wellEE v} then @${\wellEE \efromstaE{\tau}{v}}.
}@tr-proof{
  @tr-case[@${\efromstaE{\tau}{v} = v}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-S-implies" @elem{static subset}]{
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
    @tr-step{
      @${\tann{x}{\tau_d},\Gamma \wellEE e}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e}
      @tr-IH}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr : \tau
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \edyn{\tau}{e} : \tau
              }}]{
    @tr-step{
      @${\Gamma \wellEE e}
      @|E-D-implies|}
    @tr-step{
      @${\Gamma \wellEE \edyn{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-D-implies" @elem{dynamic subset}]{
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
    @tr-step{
      @${x,\Gamma \wellEE e}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellEE e_0 @tr-and[] \Gamma \wellEE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellEE \ebinop{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau
              }{
                \Gamma \wellM \esta{\tau}{e}
              }}]{
    @tr-step{
      @${\Gamma \wellEE e}
      @|E-S-implies|}
    @tr-step{
      @${\Gamma \wellEE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "E-progress" @elem{@${\langE} progress}]{
  If @${\wellEE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccES e'} }
    @item{ @${e \ccES \tagerror} }
    @item{ @${e \ccES \boundaryerror} }
  ]
}@tr-proof{
  By the @|E-uec| lemma, there are seven possible cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccES \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrES \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau}}{e'}}]{
      @tr-step{
        @${e \ccES \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrES \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step{
        @${e \ccES \tagerror}
        @${\vapp{v_0}{v_1} \rrES \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #false]{
    @tr-if[@${\delta(\vunop, v) = e''}]{
      @tr-step{
        @${e \ccES \ctxE{e''}}
        @${(\eunop{v}) \rrES e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccES \tagerror}
        @${(\eunop{v}) \rrES \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${e \ccES \ctxE{e''}}
        @${(\ebinop{v_0}{v_1}) \rrES e''}}
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step{
        @${e \ccES \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrES \boundaryerror}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccES \tagerror}
        @${(\ebinop{v_0}{v_1}) \rrES \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{v}}}]{
    @tr-step{
      @${e \ccES \ctxE{\efromdynE{\tau}{v}}}
    }
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\esta{\tau}{v}}}]{
    @tr-step{
      @${e \ccES \ctxE{\efromstaE{\tau}{v}}}}
    @tr-qed{}
  }

  @tr-case[@${e \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccES \eerr}}
    @tr-qed[]
  }

}

@tr-lemma[#:key "E-preservation" @elem{@${\langE} preservation}]{
  If @${\wellEE e} and @${e \ccES e'} then @${\wellEE e'}.
}@tr-proof{
  By @|E-uec| there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccES e'}}
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${v_0 = \vlam{x}{e'} \mbox{ or } v_0 = \vlam{\tann{x}{\tau}}{e'}
         @tr-and[]
         \ctxE{v_0~v_1} \ccES \ctxE{\vsubst{e'}{x}{v_1}}}
    }
    @tr-step{
      @${\wellEE \vapp{v_0}{v_1}}
      @|E-hole-typing|
    }
    @tr-step{
      @${\wellEE v_0
         @tr-and[]
         \wellEE v_1}
      @elem{@|E-inversion| (2)}
    }
    @tr-step{
      @${x \wellEE e'}
      @elem{@|E-inversion| (3)}
    }
    @tr-step{
      @${\wellEE \vsubst{e'}{x}{v_1}}
      @elem{@|E-subst| (3, 4)}
    }
    @tr-qed{
      by @|E-hole-subst| (5)}
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step{
      @${\ctxE{\eunop{v}} \ccES \ctxE{v'}
         @tr-and[]
         \delta(\vunop, v) = e''}}
    @tr-step{
      @${\wellEE \eunop{v}}
      @|E-hole-typing|}
    @tr-step{
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    }
    @tr-step{
      @${\wellEE e''}
      @elem{@|E-delta-preservation| (1,3)}
    }
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step{
      @${\ctxE{\ebinop{v_0}{v_1}} \ccES \ctxE{v'}
         @tr-and[]
         \delta(\vbinop, v_0, v_1) = e''}}
    @tr-step{
      @${\wellEE \ebinop{v_0}{v_1}}
      @|E-hole-typing|}
    @tr-step{
      @${\wellEE v_0 @tr-and[] \wellEE v_1}
      @elem{@|E-inversion| (2)}
    }
    @tr-step{
      @${\wellEE e''}
      @elem{@|E-delta-preservation| (3)}
    }
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{v}}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{v}} \ccES \ctxE{\efromdynE{\tau}{v}}}}
    @tr-step{
      @${\wellEE \edyn{\tau}{v}}
      @|E-hole-typing|}
    @tr-step{
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    }
    @tr-step{
      @${\wellEE \efromdynE{\tau}{v}}
      @|E-fromdyn-soundness| (3)
    }
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\esta{\tau}{v}}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{v}} \ccES \efromstaE{\tau}{v}}}
    @tr-step{
      @${\wellEE \esta{\tau}{v}}
      @|E-hole-typing|}
    @tr-step{
      @${\wellEE v}
      @elem{@|E-inversion| (2)}
    }
    @tr-step{
      @${\wellEE \efromstaE{\tau}{v}}
      @|E-fromsta-soundness| (3) }
    @tr-qed{
      by @|E-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${\ctxE{\eerr} \ccES \eerr}}
    @tr-qed{}
  }
}

@tr-lemma[#:key "E-bf-progress" @elem{@${\langE} boundary-free progress}]{
  If @${\wellM e : \tau} and @${e} is boundary-free, then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccES e'} }
    @item{ @${e \ccES \boundaryerror} }
  ]
}@tr-proof{
  By the @|M-uec| lemma, there are five cases:

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau'}}{e'}}]{
      @tr-step{
        @${e \ccES \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrES \vsubst{e'}{x}{v_1}}}
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

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #false]{
    @tr-if[@${\delta(\vunop, v) = e''}]{
      @tr-step{
        @${e \ccES \ctxE{e''}}
        @${(\eunop{v}) \rrES e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${e \ccES \ctxE{e''}}
        @${(\ebinop{v_0}{v_1}) \rrES e''}}
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step{
        @${e \ccES \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrES \boundaryerror}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${\ctxE{\eerr} \ccES \eerr}}
    @tr-qed[]
  }

}

@tr-lemma[#:key "E-bf-preservation" @elem{@${\langE} boundary-free preservation}]{
  If @${\wellM e : \tau} and @${e} is boundary-free and @${e \ccES e'}
  then @${\wellM e' : \tau} and @${e'} is boundary-free.
}@tr-proof{
  By the @|M-uec| lemma, there are five cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{ @${e \ccES e'} }
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_d}}{e'}}]{
      @tr-step{
        @${\ctxE{v_0~v_1} \ccES \ctxE{\vsubst{e'}{x}{v_1}}}}
      @tr-step{
        @${\wellM \eapp{v_0}{v_1} : \tau_c}}
      @tr-step{
        @${\wellM v_0 : \tarr{\tau_d}{\tau_c} @tr-and[] \wellM v_1 : \tau_d}
        (2)}
      @tr-step{
        @${\tann{x}{\tau_d} \wellM e' : \tau_c}
        (3)}
      @tr-step{
        @${\wellM \vsubst{e'}{x}{v_1} : \tau_c}
        @|M-subst| (3, 4)}
      @tr-step{
        @elem{@${\vsubst{e'}{x}{v_1}} is boundary-free}
        @elem{@${e'} and @${v_1} are boundary-free}}
      @tr-qed[]
    }
    @tr-else[""]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step{
      @${\ctxE{\eunop{v}} \ccES \ctxE{v'}
         @tr-and[]
         \delta(\vunop, v) = e''}}
    @tr-step{
      @${\wellM \eunop{v} : \tau'}}
    @tr-step{
      @${\wellM v : \tau_0}}
    @tr-step{
      @${\wellM e'' : \tau'}
      @|M-delta-preservation| (3)}
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step{
      @${\ctxE{\ebinop{v_0}{v_1}} \ccES \ctxE{v'}
         @tr-and[]
         \delta(\vbinop, v_0, v_1) = e''}}
    @tr-step{
      @${\wellM \ebinop{v_0}{v_1} : \tau'}}
    @tr-step{
      @${\wellM v_0 : \tau_0 @tr-and[] \wellM v_1 : \tau_1}
    }
    @tr-step{
      @${\wellM e'' : \tau'}
      @|M-delta-preservation| (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${\ctxE{\eerr} \ccES \eerr}}
    @tr-qed{
      by @${\wellM \eerr : \tau} }
  }

}

@tr-lemma[#:key "E-uec" @elem{@${\langE} unique evaluation contexts}]{
  If @${\wellEE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{v}}} }
    @item{ @${e = \ctxE{\esta{\tau}{v}}} }
    @item{ @${e = \ctxE{\eerr}} }
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

  @tr-case[@${e = \eunop{e_0}} #:itemize? #false]{
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

  @tr-case[@${e = \eerr}]{
    @tr-step{
      @${\ED = \ehole}}
    @tr-qed[]
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

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      by @${\vsubst{\eerr}{x}{v} = \eerr}
    }
  }

}

@tr-lemma[#:key "E-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellEE v} and @${\delta(\vunop, v) = e'} then @${\wellEE e'}
    }
    @item{
      If @${\wellEE v_0} and @${\wellEE v_1} and @${\delta(\vbinop, v_0, v_1) = e'}
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

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \boundaryerror}]{
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
}@tr-proof{
  @tr-qed{because @${e} is closed under @${\Gamma}}
}

@tr-lemma[#:key "M-uec" @elem{unique static evaluation contexts}]{
  If @${\wellM e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\eerr}} }
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

  @tr-case[@${e = \eunop{e_0}} #:itemize? #false]{
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
    @tr-contradiction{
      @${e} is boundary-free
    }
  }

  @tr-case[@${e = \esta{\tau}{e_0}}]{
    @tr-contradiction{
      @${\wellM e : \tau}
    }
  }

  @tr-case[@${e = \eerr}]{
    @${\ED = \ehole}
    @tr-qed{
      @${e = \ctxE{\eerr}}}
  }

}

@tr-lemma[#:key "M-S-inversion" @elem{@${\wellM} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellM x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellM e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \vpair{e_0}{e_1} : \tau}
      then @${\Gamma \wellM e_0 : \tau_0}
      and @${\Gamma \wellM e_1 : \tau_1}
      and @${\tpair{\tau_0}{\tau_1} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \eapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellM e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellM e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellM \efst{e} : \tau}
      then @${\Gamma \wellM e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \esnd{e} : \tau}
      then @${\Gamma \wellM e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellM e_0 : \tau_0}
      and @${\Gamma \wellM e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellM e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellM e : \tau}
  }
}

@tr-lemma[#:key "M-S-canonical" @elem{canonical forms}]{
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

@tr-lemma[#:key "M-subst" @elem{substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellM e : \tau},
  and @${e} is boundary-free
  and @${\wellM v : \tau_x}
  then @${\Gamma \wellM \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\tau_x = \tau}
    }
    @tr-step{
      @${\Gamma \wellM v : \tau}
      @elem{@|M-weakening|}
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
    @tr-contradiction{
      @${\tann{x}{\tau_x},\Gamma \wellM e : \tau}
    }
  }

  @tr-case[@${e = \vlam{\tann{x}{\tau'}}{e'}}]{
    @tr-qed{
      by @${\vsubst{(\vlam{\tann{x}{\tau'}}{e'})}{x}{v} = \vlam{\tann{x}{\tau'}}{e'}}
    }
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellM e'}
      @|M-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellM \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-contradiction{ @${e} is boundary-free }
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-contradiction{ @${e} is boundary-free }
  }

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      @${\vsubst{\eerr}{x}{v} = \eerr}
    }
  }

}


@tr-lemma[#:key "M-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellM v} and @${\delta(\vunop, v) = v'} then @${\wellM e'}
    }
    @item{
      If @${\wellM v_0} and @${\wellM v_1} and @${\delta(\vbinop, v_0, v_1) = e'}
       then @${\wellM v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellM v_0}
      @|M-S-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellM v_1}
      @|M-S-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsum, v_0, v_1) = v_0 + v_1}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \floorof{v_0 / v_1}}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \boundaryerror}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "M-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellM e} then @${x,\Gamma \wellM e}
    }
    @item{
      If @${\Gamma \wellM e} then @${\tann{x}{\tau},\Gamma \wellM e}
    }
  ]
}@tr-proof{
  @tr-qed{because @${e} is closed under @${\Gamma}}
}
