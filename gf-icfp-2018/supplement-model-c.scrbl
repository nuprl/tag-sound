#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Co-Natural Embedding}

@section{@${\langC} Definitions}
@exact{\input{fig:conatural-embedding.tex}}

@|clearpage|
@section{@${\langC} Properties}

@(begin
   (define C-S-progress @tr-ref[#:key "C-S-progress"]{static progress})
   (define C-D-progress @tr-ref[#:key "C-D-progress"]{dynamic progress})
   (define C-S-preservation @tr-ref[#:key "C-S-preservation"]{static preservation})
   (define C-D-preservation @tr-ref[#:key "C-D-preservation"]{dynamic preservation})

   (define C-S-implies @tr-ref[#:key "C-S-implies"]{static implies})
   (define C-D-implies @tr-ref[#:key "C-D-implies"]{dynamic implies})

   (define C-S-uec @tr-ref[#:key "C-S-uec"]{unique evaluation contexts})
   (define C-D-uec @tr-ref[#:key "C-D-uec"]{unique evaluation contexts})

   (define C-S-hole-typing @tr-ref[#:key "C-S-hole-typing"]{static hole typing})
   (define C-D-hole-typing @tr-ref[#:key "C-D-hole-typing"]{dynamic hole typing})

   (define C-S-hole-subst @tr-ref[#:key "C-S-hole-subst"]{static hole substitution})
   (define C-D-hole-subst @tr-ref[#:key "C-D-hole-subst"]{dynamic hole substitution})

   (define C-S-inversion @tr-ref[#:key "C-S-inversion"]{inversion})
   (define C-D-inversion @tr-ref[#:key "C-D-inversion"]{inversion})

   (define C-S-canonical @tr-ref[#:key "C-S-canonical"]{canonical forms})

   (define C-Delta-soundness @tr-ref[#:key "C-Delta-type-soundness"]{@${\Delta} type soundness})
   (define C-delta-preservation @tr-ref[#:key "C-delta-preservation"]{@${\delta} preservation})

   (define C-SS-subst @tr-ref[#:key "C-SS-subst"]{substitution})
   (define C-DS-subst @tr-ref[#:key "C-DS-subst"]{substitution})
   (define C-SD-subst @tr-ref[#:key "C-SD-subst"]{substitution})
   (define C-DD-subst @tr-ref[#:key "C-DD-subst"]{substitution})

   (define C-finite-subtyping @tr-ref[#:key "C-finite-subtyping"]{finite subtyping})
   (define C-finite-supertyping @tr-ref[#:key "C-finite-supertyping"]{finite supertyping})
   (define C-weakening @tr-ref[#:key "C-weakening"]{weakening})

)

@tr-theorem[#:key "C-soundness" @elem{@${\langC} type soundness}]{
  If @${\wellM e : \tau} then @${\wellCE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
    @item{ @${e \rrCSstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccCD \tagerror} }
    @item{ @${e \rrCSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step[
      @${\wellCE e : \tau}
      @|C-S-implies|
    ]}
    @item{@tr-qed{
      by @|C-S-progress| and @|C-S-preservation|.
    }}
  ]
}

@tr-corollary[#:key "C-pure-static" @elem{@${\langC} static soundness}]{
  If @${\wellM e : \tau} and @${e} is purely static, then either:
  @itemlist[
    @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
    @item{ @${e \rrCSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{(sketch)
  Purely-static terms cannot step to a @${\tagerror} and are preserved by the
   @${\ccCS} reduction relation.
}

@tr-lemma[#:key "C-S-implies" @elem{@${\langC} static implies}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellCE e : \tau}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e : \tau}

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellCE x : \tau}
      @${\tann{x}{\tau} \in \Gamma}]
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tau_d \tarrow \tau_c
              }}]{
    @tr-step[
      @${\tann{x}{\tau_d},\Gamma \wellCE e : \tau_c}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c}} }
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
                \Gamma \wellM i : \tint
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
      @${\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellCE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}} }
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
      @${\Gamma \wellCE e_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \Gamma \wellCE e_1 : \tau_d}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \vapp{e_0}{e_1} : \tau_c} }
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
      @${\Gamma \wellCE e_0 : \tau_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \eunop{e_0} : \tau} }
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
                \Gamma \wellM \vbinop~e_0~e_1 : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellCE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \ebinop{e_0}{e_1} : \tau} }
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
      @${\Gamma \wellCE e : \tau'}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE e : \tau}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \edyn{\tau}{e} : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellCE e}
      @|C-D-implies|]
    @tr-step{
      @${\Gamma \wellCE \edyn{\tau}{e} : \tau}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "C-D-implies" @elem{@${\langC} dynamic implies}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellCE e}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e}.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @tr-step[
      @${\Gamma \wellCE x}
      @${x \in \Gamma}]
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e
              }{
                \Gamma \wellM \vlam{x}{e}
              }}]{
    @tr-step[
      @${x,\Gamma \wellCE e}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellCE \vlam{x}{e}}
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
      @${\Gamma \wellCE e_0
         @tr-and[]
         \Gamma \wellCE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellCE \vpair{e_0}{e_1}}
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
      @${\Gamma \wellCE e_0
         @tr-and[]
         \Gamma \wellCE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellCE \vapp{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \eunop{e}
              }}]{
    @tr-step{
      @${\Gamma \wellCE e}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellCE \eunop{e}}
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
      @${\Gamma \wellCE e_0
         @tr-and[]
         \Gamma \wellCE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellCE \ebinop{e_0}{e_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau
              }{
                \Gamma \wellM \esta{\tau}{e}
              }}]{
    @tr-step{
      @${\Gamma \wellCE e : \tau}
      @|C-S-implies|}
    @tr-step{
      @${\Gamma \wellCE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "C-S-progress" @elem{@${\langC} static progress}]{
  If @${\wellCE e : \tau} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccCS e'} }
    @item{ @${e \ccCS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccCD \tagerror} }
  ]
}@tr-proof{
  By the @|C-S-uec| lemma, there are five possible cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${\wellCE \vapp{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \wellCE v_1 : \tau_d}
      @|C-S-inversion|}
    @tr-step{
      @${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}
      @|C-S-canonical| (2)}
    @list[
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}}]{
        @tr-step[
          @${e \ccCS \ctxE{\vsubst{e'}{x}{v_1}}}
          @${\vapp{v_0}{v_1} \rrCS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}]{
        @tr-step{
          @${e \ccCS \ctxE{\edyn{\tau_c'}{(\vapp{v_f}{\esta{\tau_d'}{v_1}})}}}
          @${\vapp{v_0}{v_1} \rrCS \edyn{\tau_c'}{(\vapp{v_f}{\esta{\tau_d'}{v_1}})}}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step[
      @${\wellCE \eunop{v} : \tau'}
      @|C-S-hole-typing|]
    @tr-step[
      @${\wellCE v : \tpair{\tau_0}{\tau_1}}
      @|C-S-inversion|]
    @tr-step[
      @${v = \vpair{v_0}{v_1}
         @tr-or[]
         v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
      @|C-S-canonical|]
    @list[
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vfst}]{
        @${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}
        @tr-step{
          @${e \ccCS \ctxE{v_0}}
          @${\eunop{v} \rrCS v_0}}
        @tr-qed[]
      }
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vsnd}]{
        @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}
        @tr-step[
          @${e \ccCS \ctxE{v_1}}
          @${\eunop{v} \rrCS v_1}]
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
                @tr-and[2]
                \vunop = \vfst}]{
        @tr-step{
          @${e \ccCS \ctxE{\edyn{\tau_0}{(\efst{v'})}}}
          @${\efst{v} \rrCS \edyn{\tau_0}{(\efst{v'})}}}
        @tr-qed[]
      }
      @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
                @tr-and[4]
                \vunop = \vsnd}]{
        @tr-step{
          @${e \ccCS \ctxE{\edyn{\tau_1}{(\esnd{v'})}}}
          @${\esnd{v} \rrCS \edyn{\tau_1}{(\esnd{v'})}}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step[
      @${\wellCE \ebinop{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|]
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|C-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = A}
      @elem{@|C-Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrCS A}
      (3)}
    @tr-qed{
      by @${e \ccCS \ctxE{A}} if @${A \in e}
      @linebreak[]
      and by @${e \ccCS A} otherwise}
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\tau'}{e'}}} #:itemize? #false]{
    @tr-if[@${e' \in v} #:itemize? #false]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}
                @tr-and[2]
                e' = \vlam{x}{e''} \mbox{ or } e' = \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v}}]{
        @tr-step{
          @${e \ccCS \ctxE{\vmonfun{\tarr{\tau_d}{\tau_c}}{e'}}}
          @${\edyn{\tau'}{e'} \rrCS \vmonfun{\tarr{\tau_d}{\tau_c}}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tpair{\tau_0}{\tau_1}
                @tr-and[2]
                e' = \vpair{v_0}{v_1} \mbox{ or } e' = \vmonpair{\tpair{\tau_0'}{\tau_1'}}{v'}}]{
        @tr-step{
          @${e \ccCS \ctxE{\vmonpair{\tpair{\tau_0}{\tau_1}}{e'}}}
          @${\edyn{\tau'}{e'} \rrCS \vmonpair{\tpair{\tau_0}{\tau_1}}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tint
                @tr-and[2]
                e' \in i}]{
        @tr-step{
          @${e \ccCS \ctxE{e'}}
          @${\edyn{\tau'}{e'} \rrCS e'}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tnat
                @tr-and[2]
                e' \in \naturals}]{
        @tr-step{
          @${e \ccCS \ctxE{e'}}
          @${\edyn{\tau'}{e'} \rrCS e'}}
        @tr-qed[]
      }
      @tr-else[""]{
        @tr-qed{
          @${e \ccCS \boundaryerror}}
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccCD A}
        @|C-D-progress|
      ]
      @tr-qed{
        by @${e \ccCS \ctxE{\edyn{\tau}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccCS A} otherwise}
    }
  }

}

@tr-lemma[#:key "C-D-progress" @elem{@${\langC} dynamic progress}]{
  If @${\wellCE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccCD e'} }
    @item{ @${e \ccCD \boundaryerror} }
    @item{ @${e \ccCD \tagerror} }
  ]
}@tr-proof{
  By the @|C-D-uec| lemma, there are five cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccCD \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrCD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}}]{
      @tr-step{
        @${e \ccCD \ctxE{\esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
        @${\vapp{v_0}{v_1}
           \rrCD \esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}
                @tr-or[4]
                v_0 \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{v'} }]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${(\vapp{v_0}{v_1}) \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}
              @tr-and[2]
              \vunop \eeq \vfst}]{
      @tr-step{
        @${e \ccCD \ctxE{\esta{\tau_0}{\efst{v'}}}}
        @${\eunop{v} \rrCD \esta{\tau_0}{\efst{v'}}}}
      @tr-qed[]
    }
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}
              @tr-and[2]
              \vunop \eeq \vsnd}]{
      @tr-step{
        @${e \ccCD \ctxE{\esta{\tau_1}{\esnd{v'}}}}
        @${\eunop{v} \rrCD \esta{\tau_1}{\esnd{v'}}}}
      @tr-qed[]
    }
    @tr-if[@${\delta(\vunop, v) = A}]{
      @tr-step{
        @${(\eunop{v}) \rrCD A}}
      @tr-qed{
        by @${e \ccCD \ctxE{A}} if @${A \in e}
        @linebreak[]
        and by @${e \ccCD A} otherwise}
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${(\eunop{v}) \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = A}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrCD A}}
      @tr-qed{
        by @${e \ccCD \ctxE{A}} if @${A \in e}
        @linebreak[]
        and by @${e \ccCD A} otherwise}
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${\ebinop{v_0}{v_1} \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}}]{
        @tr-step{
          @${e \ccCS \ctxE{\vmonfun{\tau'}{e'}}}
          @${\esta{\tau'}{e'} \rrCS \vmonfun{\tau'}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau' = \tpair{\tau_0}{\tau_1}}]{
        @tr-step{
          @${e \ccCS \ctxE{\vmonpair{\tau'}{e'}}}
          @${\esta{\tau'}{e'} \rrCS \vmonfun{\tau'}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau' = \tint}]{
        @tr-step{
          @${e \ccCS \ctxE{e'}}
          @${\esta{\tau'}{e'} = e'}}
        @tr-qed[]
      }
      @tr-else[@${\tau' = \tnat}]{
        @tr-step{
          @${e \ccCS \ctxE{e'}}
          @${\esta{\tau'}{e'} = e'}}
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion|}
      @tr-step{
        @${e' \ccCS A}
        @|C-S-progress| (2)}
      @tr-qed{
        by @${e \ccCD \ctxE{\esta{\tau'}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccCD A} otherwise}
    }
  }
}

@tr-lemma[#:key "C-S-preservation" @elem{@${\langC} static preservation}]{
  If @${\wellCE e : \tau} and @${e \ccCS e'} then @${\wellCE e' : \tau}
}@tr-proof{
  By the @|C-S-uec| lemma there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_x}}{e'}
              @tr-and[2]
              e \ccCS \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step[
        @${\wellCE \vapp{v_0}{v_1} : \tau'}
        @|C-S-hole-typing|]
      @tr-step{
        @${\wellCE v_0 : \tarr{\tau_d}{\tau_c}
           @tr-and[]
           \wellCE v_1 : \tau_d
           @tr-and[]
           \tau_c \subteq \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\tau_d \subteq \tau_x}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tann{x}{\tau_x} \wellCE e' : \tau_c}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\wellCE v_1 : \tau_x}
        (2, 3)}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1} : \tau_c}
        @|C-SS-subst| (4, 5)}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-else[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{v_f}
              @tr-and[4]
              e \ccCS \ctxE{\edyn{\tau_c}{(\vapp{v_f}{(\esta{\tau_d}{v_1})})}}}]{
      @tr-step{
        @${\wellCE \vapp{v_0}{v_1} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v_0 : \tarr{\tau_d'}{\tau_c'}
           @tr-and[]
           \wellCE v_1 : \tau_d'
           @tr-and[]
           \tau_c' \subteq \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v_f}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tarr{\tau_d}{\tau_c} \subteq \tarr{\tau_d'}{\tau_c'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_d' \subteq \tau_d
           @tr-and[]
           \tau_c \subteq \tau_c'}
        (4)}
      @tr-step{
        @${\wellCE v_1 : \tau_d}
        (2, 5)}
      @tr-step{
        @${\wellCE \esta{\tau_d}{v_1}}
        (6)}
      @tr-step{
        @${\wellCE \vapp{v_f}{(\esta{\tau_d}{v_1})}}
        (3, 7)}
      @tr-step{
        @${\wellCE \edyn{\tau_c}{\vapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau_c}
        (8)}
      @tr-step{
        @${\wellCE \edyn{\tau_c}{\vapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCS \ctxE{v_0}}]{
      @tr-step{
        @${\wellCE \efst{\vpair{v_0}{v_1}} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_0 \subteq \tau'}
        @elem{@|C-S-inversion|}}
      @tr-step{
        @${\wellCE v_0 : \tau_0}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v_0 : \tau'}
        (2)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccCS \ctxE{v_1}}]{
      @tr-step{
        @${\wellCE \esnd{\vpair{v_0}{v_1}} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_1 \subteq \tau'}
        @elem{@|C-S-inversion|}}
      @tr-step{
        @${\wellCE v_1 : \tau_1}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v_1 : \tau'}
        (2)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCS \ctxE{\edyn{\tau_0}{(\efst{v'})}}}]{
      @tr-step{
        @${\wellCE \efst{v} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_0' \subt \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v'}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tpair{\tau_0}{\tau_1} \subteq \tpair{\tau_0'}{\tau_1'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_0 \subteq \tau_0'}}
      @tr-step{
        @${\wellCE \efst{v'}}
        (3)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\efst{v'})} : \tau_0}
        (6)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\efst{v'})} : \tau'}
        (2, 5, 7)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccCS \ctxE{\edyn{\tau_0}{(\esnd{v'})}}}]{
      @tr-step{
        @${\wellCE \esnd{v} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_1' \subt \tau'}
        @|C-S-inversion| @bold{v1 well formed}}
      @tr-step{
        @${\wellCE v'}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tpair{\tau_0}{\tau_1} \subteq \tpair{\tau_0'}{\tau_1'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_1 \subteq \tau_1'}}
      @tr-step{
        @${\wellCE \esnd{v'}}
        (3)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\esnd{v'})} : \tau_0}
        (5)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\esnd{v'})} : \tau'}
        (2, 5, 7)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccCS \ctxE{v}}]{
    @tr-step{
      @${\wellCE \ebinop{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''
         @tr-and[]
         \tau'' \subteq \tau'}
      @|C-S-inversion| (1)}
    @tr-step{
      @${\wellCE v : \tau''}
      @elem{@|C-Delta-soundness| (2)}}
    @tr-step{
      @${\wellCE v : \tau'}
      (2, 3)}
    @tr-qed{
      by @|C-S-hole-subst| (5)}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \eeq \vlam{x}{e'}
              @tr-and[2]
              \tau' = \tarr{\tau_d}{\tau_c}
              @tr-and[2]
              e \ccCS \ctxE{\vmonfun{\tau'}{e'}}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE \vmonfun{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellCE \vmonfun{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${e' \eeq \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v'}
              @tr-and[2]
              \tau' = \tarr{\tau_d}{\tau_c}
              @tr-and[2]
              e \ccCS \ctxE{\vmonfun{\tau'}{e'}}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE \vmonfun{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellCE \vmonfun{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${e' \eeq \vpair{v_0}{v_1}
              @tr-and[2]
              \tau' = \tpair{\tau_0}{\tau_1}
              @tr-and[2]
              e \ccCS \ctxE{\vmonpair{\tau'}{e'}}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE \vmonpair{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellCE \vmonpair{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${e' \eeq \vmonpair{\tpair{\tau_0'}{\tau_1'}}{v'}
              @tr-and[2]
              \tau' = \tpair{\tau_0}{\tau_1}
              @tr-and[2]
              e \ccCS \ctxE{\vmonpair{\tau'}{e'}}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE \vmonpair{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellCE \vmonpair{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${e' \in i
              @tr-and[2]
              \tau' = \tint
              @tr-and[2]
              e \ccCS \ctxE{e'}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE e' : \tau'}
        @${\tau' = \tint}}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-if[@${e' \in \naturals
              @tr-and[2]
              \tau' = \tnat
              @tr-and[2]
              e \ccCS \ctxE{e'}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\tau' \subteq \tau''}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE e' : \tau'}
        @${\tau' = \tnat}}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccCD e''
                @tr-and[4]
                e \ccCS \ctxE{\edyn{\tau'}{e''}}}]{
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau''}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE e''}
        @|C-D-preservation| (2)}
      @tr-step{
        @${\wellCE \edyn{\tau'}{e''} : \tau'}
        (3)}
      @tr-step{
        @${\wellCE \edyn{\tau'}{e''} : \tau''}
        (2, 4)}
      @tr-qed{
        by @|C-S-hole-subst|}
    }
  }
}

@tr-lemma[#:key "C-D-preservation" @elem{@${\langC} dynamic preservation}]{
  If @${\wellCE e} and @${e \ccCD e'} then @${\wellCE e'}
}@tr-proof{
  By the @|C-D-uec| lemma, there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccCD \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step{
        @${\wellCE \vapp{v_0}{v_1}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v_0
           @tr-and[]
           \wellCE v_1}
        @|C-D-inversion| (1)}
      @tr-step{
        @${x \wellCE e'}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1}}
        @|C-DD-subst| (2, 3)}
      @tr-qed{
        @|C-D-hole-subst| (1, 4)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}
                @tr-and[4]
                e \ccCD \ctxE{\esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}]{
      @tr-step{
        @${\wellCE \vapp{v_0}{v_1}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v_0
           @tr-and[]
           \wellCE v_1}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_f : \tarr{\tau_d}{\tau_c}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \edyn{\tau_d}{v_1} : \tau_d}
        (2)}
      @tr-step{
        @${\wellCE \vapp{v_f}{(\edyn{\tau_d}{v_1})} : \tau_c}
        (3, 4)}
      @tr-step{
        @${\wellCE \esta{\tau_c}{\vapp{v_f}{(\edyn{\tau_d}{v_1})}}}
        (5)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCD \ctxE{v_0}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_0}
        @|C-D-inversion| (2)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccCD \ctxE{v_1}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_1}
        @|C-D-inversion| (2)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCD \ctxE{\esta{\tau_0}{(\efst{v'})}}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v' : \tpair{\tau_0}{\tau_1}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \efst{v'} : \tau_0}
        (3)}
      @tr-step{
        @${\wellCE \esta{\tau_0}{(\efst{v'})}}
        (4)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccCD \ctxE{\esta{\tau_0}{(\esnd{v'})}}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v' : \tpair{\tau_0}{\tau_1}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \esnd{v'} : \tau_1}
        (3)}
      @tr-step{
        @${\wellCE \esta{\tau_1}{(\esnd{v'})}}
        (4)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccCD \ctxE{v}}]{
    @tr-step{
      @${\wellCE \ebinop{v_0}{v_1}}
      @|C-D-hole-typing|}
    @tr-step{
      @${\wellCE v_0
         @tr-and[]
         \wellCE v_1}
      @|C-D-inversion| (1)}
    @tr-step{
      @${\wellCE v}
      @|C-delta-preservation| (2)}
    @tr-qed{
      by @|C-D-hole-subst| (3)}
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}
                @tr-and[2]
                e \ccCD \ctxE{\vmonfun{\tau'}{e'}}}]{
        @tr-step{
          @${\wellCE \esta{\tau'}{e'}}
          @|C-D-hole-typing|}
        @tr-step{
          @${\wellCE e' : \tau'}
          @|C-D-inversion|}
        @tr-step{
          @${\wellCE \vmonfun{\tau'}{e'}}
          (2)}
        @tr-qed{
          by @|C-D-hole-subst|}
      }
      @tr-if[@${\tau' = \tpair{\tau_0}{\tau_1}
                @tr-and[2]
                e \ccCD \ctxE{\vmonpair{\tau'}{e'}}}]{
        @tr-step{
          @${\wellCE \esta{\tau'}{e'}}
          @|C-D-hole-typing|}
        @tr-step{
          @${\wellCE e' : \tau'}
          @|C-D-inversion|}
        @tr-step{
          @${\wellCE \vmonpair{\tau'}{e'}}
          (2)}
        @tr-qed{
          by @|C-D-hole-subst| (3)}
      }
      @tr-if[@${\tau' = \tint
                @tr-and[2]
                e \ccCD \ctxE{e'}}]{
        @tr-step{
          @${\wellCE \esta{\tau'}{e'}}
          @|C-D-hole-typing|}
        @tr-step{
          @${\wellCE e' : \tau'}
          @|C-D-inversion|}
        @tr-step{
          @${e' \in i}
          @|C-S-canonical| (2)}
        @tr-step{
          @${\wellCE e'}
          (3)}
        @tr-qed{
          by @|C-D-hole-subst|}
      }
      @tr-else[@${\tau' = \tnat
                  @tr-and[4]
                  e \ccCD \ctxE{e'}}]{
        @tr-step{
          @${\wellCE \esta{\tau'}{e'}}
          @|C-D-hole-typing|}
        @tr-step{
          @${\wellCE e' : \tau'}
          @|C-D-inversion|}
        @tr-step{
          @${e' \in \naturals}
          @|C-S-canonical| (2)}
        @tr-step{
          @${\wellCE e'}
          (3)}
        @tr-qed{
          by @|C-D-hole-subst|}
      }
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccCS e''
                @tr-and[4]
                e \ccCD \ctxE{\esta{\tau'}{e''}}}]{
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE e'' : \tau'}
        @|C-S-preservation| (2)}
      @tr-step{
        @${\wellCE \esta{\tau'}{e''}}
        (3)}
      @tr-qed{
        by @|C-D-hole-subst|}
    }
  }
}

@tr-lemma[#:key "C-S-uec" @elem{@${\langC} unique static evaluation contexts}]{
  If @${\wellCE e : \tau} then either:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ctxE{\vapp{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{e'}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \esta{\tau}{e'}}]{
    @tr-contradiction[@${\wellCE e : \tau}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}
              @tr-or[4]
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}
              @tr-or[4]
              e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellCE e_0 : \tau_0}
        @|C-S-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)
      }
      @tr-step[
        @${\ED = \vpair{\ED_0}{e_1}}
      ]
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellCE e_1 : \tau_1}
        @|C-S-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step[
        @${\ED = \vpair{e_0}{\ED_1}}
      ]
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e} is a value
      }
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellCE e_0 : \tau_0}
        @|C-S-inversion|}
      @tr-step[
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vapp{\ED_0}{e_1}}
      ]
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellCE e_1 : \tau_1}
        @|C-S-inversion|}
      @tr-step[
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vapp{e_0}{\ED_1}}
      ]
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\vapp{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellCE e_0 : \tau_0}
        @|C-S-inversion|
      ]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \eunop{\ED_0}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\eunop{e_0}}}
      }
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellCE e_0 : \tau_0}
        @|C-S-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)}
      @tr-step[
        @${\ED = \ebinop{\ED_0}{e_1}}
      ]
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellCE e_1 : \tau_1}
        @|C-S-inversion|}
      @tr-step[
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \ebinop{e_0}{\ED_1}}
      ]
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\ebinop{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \edyn{\tau}{e_0}}]{
    @${\ED = \ehole}
    @tr-qed{
      @${e = \ctxE{\edyn{\tau}{e_0}}}
    }
  }

}

@tr-lemma[#:key "C-D-uec" @elem{@${\langC} unique dynamic evaluation contexts}]{
  If @${\wellCE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${\ctxE{\vapp{v_0}{v_1}}} }
    @item{ @${\ctxE{\eunop{v}}} }
    @item{ @${\ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${\ctxE{\esta{\tau}{e'}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x
              @tr-or[4]
              e = \vlam{\tann{x}{\tau}}{e'}
              @tr-or[4]
              e = \edyn{\tau}{e'}}]{
    @tr-contradiction{@${\wellCE e}}
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}
              @tr-or[4]
              e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellCE e_0}
        @|C-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \vpair{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step[
        @${\wellCE e_1}
        @|C-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \vpair{e_0}{\ED_1}}}
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v @tr-and[4] e_1 \in v}]{
      @tr-step[
        @${\ED = \ehole}
      ]
      @tr-qed{
        @${e} is a value
      }
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellCE e_0}
        @|C-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
      @tr-step{
        @${\ED = \vapp{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step[
        @${\wellCE e_1}
        @|C-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \vapp{e_0}{\ED_1}}}
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v @tr-and[4] e_1 \in v}]{
      @tr-step[
        @${\ED = \ehole}
      ]
      @tr-qed{
        @${e = \ctxE{\vapp{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellCE e_0}
        @|C-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \eunop{\ED_0}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @tr-step[
        @${\ED = \ehole}
      ]
      @tr-qed{
        @${e = \ctxE{\eunop{e_0}}}
      }
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellCE e_0}
        @|C-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \ebinop{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step[
        @${\wellCE e_1}
        @|C-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \ebinop{e_0}{\ED_1}}}
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v @tr-and[4] e_1 \in v}]{
      @tr-step[
        @${\ED = \ehole}
      ]
      @tr-qed{
        @${e = \ctxE{\ebinop{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \esta{\tau}{e'}}]{
    @${\ED = \ehole}
    @tr-qed{
      @${e = \ctxE{\esta{\tau}{e'}}}
    }
  }
}

@tr-lemma[#:key "C-S-hole-typing" @elem{@${\langC} hole typing}]{
  If @${\wellCE \ctxE{e} : \tau} then the derivation
   contains a sub-term @${\wellCE e : \tau'}
}@tr-proof{
  By induction on the structure of @${\ED}.

  @tr-case[@${\ED = \ehole}]{
    @tr-qed{
      @${\ctxE{e} = e}
    }
  }

  @tr-case[@${\ED = \vapp{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vapp{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellCE \ED_0[e] : \tarr{\tau_d}{\tau_c}}
      @|C-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vapp{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \vapp{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellCE \ED_1[e] : \tau_d}
      @|C-S-inversion|
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
      @${\wellCE \ED_0[e] : \tau_0}
      @|C-S-inversion|
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
      @${\wellCE \ED_1[e] : \tau_1}
      @|C-S-inversion|
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
      @${\wellCE \ED_0[e] : \tau_0}
      @|C-S-inversion|
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
      @${\wellCE \ED_0[e] : \tau_0}
      @|C-S-inversion|
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
      @${\wellCE \ED_1[e] : \tau_1}
      @|C-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "C-D-hole-typing" @elem{@${\langC} hole typing}]{
  If @${\wellCE \ctxE{e}} then the derivation contains a sub-term @${\wellCE e}
}@tr-proof{
  By induction on the structure of @${\ED}.

  @tr-case[@${\ED = \ehole}]{
    @tr-qed{
      @${\ctxE{e} = e}
    }
  }

  @tr-case[@${\ED = \vapp{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vapp{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellCE \ED_0[e]}
      @|C-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vapp{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \vapp{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellCE \ED_1[e]}
      @|C-D-inversion|
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
      @${\wellCE \ED_0[e]}
      @|C-D-inversion|
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
      @${\wellCE \ED_1[e]}
      @|C-D-inversion|
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
      @${\wellCE \ED_0[e]}
      @|C-D-inversion|
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
      @${\wellCE \ED_0[e]}
      @|C-D-inversion|
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
      @${\wellCE \ED_1[e]}
      @|C-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "C-S-hole-subst" @elem{@${\langC} static hole substitution}]{
  If @${\wellCE \ctxE{e} : \tau}
   and contains @${\wellCE e : \tau'},
   and furthermore @${\wellCE e' : \tau'},
   then @${\wellCE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\ED}

  @tr-case[@${\ED = \ehole}]{
    @tr-step{
      @${\ctxE{e} = e
         @tr-and[]
         \ctxE{e'} = e'}
    }
    @tr-step{
      @${\wellCE e : \tau}
      (1)
    }
    @tr-step{
      @${\tau' = \tau}
    }
    @tr-step{
      @${\wellCE e' : \tau}
    }
    @tr-qed{
      by (1, 4)
    }
  }

  @tr-case[@${\ED = \vpair{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}
        @tr-and[]
        \ctxE{e'} = \vpair{\ED_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellCE \vpair{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellCE \ED_0[e] : \tau_0
         @tr-and[]
         \wellCE e_1 : \tau_1}
      @|C-S-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \vpair{\ED_0[e']}{e_1} : \tau}
      (2, 3, 4)
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
      @${\wellCE \vpair{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE \ED_1[e] : \tau_1}
      @|C-S-inversion|
    }
    @tr-step{
      @${\wellCE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \vpair{v_0}{\ED_1[e']} : \tau}
      (2, 3, 4)
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
      @${\wellCE \ED_0[e]~e_1 : \tau}
    }
    @tr-step{
      @${\wellCE \ED_0[e] : \tau_0
         @tr-and[]
         \wellCE e_1 : \tau_1}
      @|C-S-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ED_0[e']~e_1 : \tau}
      (2, 3, 4)
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
      @${\wellCE v_0~\ED_1[e] : \tau}
    }
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE \ED_1[e] : \tau_1}
      @C-S-inversion
    }
    @tr-step{
      @${\wellCE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE v_0~\ED_1[e'] : \tau}
      (2, 3, 4)
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
      @${\wellCE \eunop{\ED_0[e]} : \tau}
    }
    @tr-step{
      @${\wellCE \ED_0[e] : \tau_0}
      @|C-S-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \eunop{\ED_0[e']} : \tau}
      (2, 3, 4)
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
      @${\wellCE \ebinop{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellCE \ED_0[e] : \tau_0
         @tr-and[]
         \wellCE e_1 : \tau_1}
      @C-S-inversion
    }
    @tr-step{
      @${\wellCE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ebinop{\ED_0[e']}{e_1} : \tau}
      (2, 3, 4)
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
      @${\wellCE \ebinop{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE \ED_1[e] : \tau_1}
      @C-S-inversion
    }
    @tr-step{
      @${\wellCE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ebinop{v_0}{\ED_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@tr-lemma[#:key "C-D-hole-subst" @elem{@${\langC} dynamic hole substitution}]{
  If @${\wellCE \ctxE{e}} and @${\wellCE e'} then @${\wellCE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\ED}

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
      @${\wellCE \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellCE \ED_0[e]
         @tr-and[]
         \wellCE e_1}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \vpair{\ED_0[e']}{e_1}}
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
      @${\wellCE \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellCE v_0
         @tr-and[]
         \wellCE \ED_1[e]}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \vpair{v_0}{\ED_1[e']}}
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
      @${\wellCE \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellCE \ED_0[e]
         @tr-and[]
         \wellCE e_1}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ED_0[e']~e_1}
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
      @${\wellCE v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellCE v_0
         @tr-and[]
         \wellCE \ED_1[e]}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE v_0~\ED_1[e']}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \eunop{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \eunop{\ED_0[e]}
        @tr-and[] \ctxE{e'} = \eunop{\ED_0[e']}}
    }
    @tr-step{
      @${\wellCE \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellCE \ED_0[e]}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \eunop{\ED_0[e']}}
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
      @${\wellCE \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellCE \ED_0[e]
         @tr-and[]
         \wellCE e_1}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ebinop{\ED_0[e']}{e_1}}
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
      @${\wellCE \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellCE v_0
         @tr-and[]
         \wellCE \ED_1[e]}
      @|C-D-inversion|
    }
    @tr-step{
      @${\wellCE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellCE \ebinop{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-S-inversion" @elem{@${\wellCE} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellCE x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellCE e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}}
      then @${\Gamma \wellCE e_0 : \tau_0'}
      and @${\Gamma \wellCE e_1 : \tau_1'}
      and @${\tau_0' \subteq \tau_0}
      and @${\tau_1' \subteq \tau_1}
    }
    @item{
      If @${\Gamma \wellCE \vapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellCE e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellCE e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellCE \efst{e} : \tau}
      then @${\Gamma \wellCE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \esnd{e} : \tau}
      then @${\Gamma \wellCE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellCE e_0 : \tau_0}
      and @${\Gamma \wellCE e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vmonpair{\tpair{\tau_0'}{\tau_1'}}{v'} : \tpair{\tau_0}{\tau_1}}
      then @${\Gamma \wellCE v'}
      and @${\tpair{\tau_0'}{\tau_1'} \subteq \tpair{\tau_0}{\tau_1}}
    }
    @item{
      If @${\Gamma \wellCE \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v'} : \tarr{\tau_d}{\tau_c}}
      then @${\Gamma \wellCE v'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellCE \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellCE e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellCE e : \tau} and by @|C-finite-subtyping|
  }
}

@tr-lemma[#:key "C-D-inversion" @elem{@${\wellCE} dynamic inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellCE x}
      then @${x \in \Gamma}
    }
    @item{
      If @${\Gamma \wellCE \vlam{x}{e'}}
      then @${x,\Gamma \wellCE e'}
    }
    @item{
      If @${\Gamma \wellCE \vpair{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \vapp{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \eunop{e_0}}
      then @${\Gamma \wellCE e_0}
    }
    @item{
      If @${\Gamma \wellCE \ebinop{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}
      then @${\Gamma \wellCE v' : \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}
      then @${\Gamma \wellCE v' : \tpair{\tau_0}{\tau_1}}
    }
    @item{
      If @${\Gamma \wellCE \esta{\tau'}{e'}}
      then @${\Gamma \wellCE e' : \tau'}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellCE e}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-S-canonical" @elem{@${\langC} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellCE v : \tpair{\tau_0}{\tau_1}}
      then either:
      @itemlist[
        @item{
          @${v \eeq \vpair{v_0}{v_1}}
        }
        @item{
          or @${v \eeq \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{v'}
                @tr-and[]
                \tpair{\tau_0'}{\tau_1'} \subteq \tpair{\tau_0}{\tau_1}}
        }
      ]
    }
    @item{
      If @${\wellCE v : \tarr{\tau_d}{\tau_c}}
      then either:
      @itemlist[
        @item{
          @${v \eeq \vlam{\tann{x}{\tau_x}}{e'}
             @tr-and[]
             \tau_d \subteq \tau_x}
        }
        @item{
          or @${v \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'}
                @tr-and[]
                \tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
        }
      ]
    }
    @item{
      If @${\wellCE v : \tint}
      then @${v \eeq i}
    }
    @item{
      If @${\wellCE v : \tnat}
      then @${v \eeq i} and @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellCE e : \tau}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-Delta-type-soundness" @elem{@${\Delta} type soundness}]{
  If @${\wellCE v_0 : \tau_0 \mbox{ and }
        \wellCE v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then either:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellCE v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on the definition of @${\Delta}.

  @tr-case[@${\Delta(\vsum, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|C-S-canonical|
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
      @|C-S-canonical|
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
      @|C-S-canonical|
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
      @|C-S-canonical|
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

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellCE v} and @${\delta(\vunop, v) = v'} then @${\wellCE v'}
    }
    @item{
      If @${\wellCE v_0} and @${\wellCE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellCE v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellCE v_0}
      @|C-D-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellCE v_1}
      @|C-D-inversion|
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

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-SS-subst" @elem{@${\langC} static-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellCE e : \tau}
  and @${\wellCE v : \tau_x}
  then @${\Gamma \wellCE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE x : \tau}}
    @tr-step{
      @${\tau_x \subteq \tau}
      @|C-S-inversion|}
    @tr-step{
      @${\wellCE v : \tau}
      (3)}
    @tr-step{
      @${\Gamma \wellCE v : \tau}
      @|C-weakening|}
    @tr-qed[]
  }

  @tr-case[@${e = x'}]{
    @tr-qed{
      by @${(\vsubst{x'}{x}{v}) = x'}
    }
  }

  @tr-case[@${e = i}]{
    @tr-qed{
      by @${\vsubst{i}{x}{v} = i}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellCE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},\tann{x}{\tau_x},\Gamma \wellCE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellCE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellCE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE v'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v}}
      @|C-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE v'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v}}
      @|C-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}} : \tau} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0 : \tau_0}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e'}{x}{v}}
      @|C-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-SD-subst" @elem{@${\langC} static-dynamic substitution}]{
  If @${x,\Gamma \wellCE e : \tau}
  and @${\wellCE v}
  then @${\Gamma \wellCE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${x,\Gamma \wellCE x : \tau}}
  }

  @tr-case[@${e = x'}]{
    @tr-qed{
      by @${(\vsubst{x'}{x}{v}) = x'}
    }
  }

  @tr-case[@${e = i}]{
    @tr-qed{
      by @${\vsubst{i}{x}{v} = i}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellCE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellCE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellCE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellCE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellCE v'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v}}
      @|C-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellCE v'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v}}
      @|C-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}} : \tau} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0 : \tau_0}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellCE e_1 : \tau_1}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e'}
      @|C-S-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e'}{x}{v}}
      @|C-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-DS-subst" @elem{@${\langC} dynamic-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellCE e}
  and @${\wellCE v : \tau_x}
  then @${\Gamma \wellCE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellCE x}}
  }

  @tr-case[@${e = x'}]{
    @tr-qed{
      by @${(\vsubst{x'}{x}{v}) = x'}
    }
  }

  @tr-case[@${e = i}]{
    @tr-qed{
      by @${\vsubst{i}{x}{v} = i}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{x'}{(\vsubst{e'}{x}{v})}} }
    @tr-step{
      @${x',\tann{x}{\tau_x},\Gamma \wellCE e'}
      @|C-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellCE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellCE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellCE e}}
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE v' : \tarr{\tau_d}{\tau_c}}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v} : \tarr{\tau_d}{\tau_c}}
      @|C-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE v' : \tpair{\tau_0}{\tau_1}}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v} : \tpair{\tau_0}{\tau_1}}
      @|C-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellCE e' : \tau'}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e'}{x}{v} : \tau'}
      @|C-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-DD-subst" @elem{@${\langC} dynamic-dynamic substitution}]{
  If @${x,\Gamma \wellCE e}
  and @${\wellCE v}
  then @${\Gamma \wellCE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\Gamma \wellCE v}
      @|C-weakening|}
    @tr-qed[]
  }

  @tr-case[@${e = x'}]{
    @tr-qed{
      by @${(\vsubst{x'}{x}{v}) = x'}
    }
  }

  @tr-case[@${e = i}]{
    @tr-qed{
      by @${\vsubst{i}{x}{v} = i}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{x'}{(\vsubst{e'}{x}{v})}} }
    @tr-step{
      @${x',x,\Gamma \wellCE e'}
      @|C-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellCE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellCE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${x,\Gamma \wellCE e}}
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellCE v'}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0
         @tr-and[]
         x,\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellCE v' : \tpair{\tau_0}{\tau_1}}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{v'}{x}{v} : \tpair{\tau_0}{\tau_1}}
      @|C-SD-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{\vsubst{v'}{x}{v}}} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0
         @tr-and[]
         x,\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e_0
         @tr-and[]
         x,\Gamma \wellCE e_1}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellCE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellCE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellCE e' : \tau'}
      @|C-D-inversion|}
    @tr-step{
      @${\Gamma \wellCE \vsubst{e'}{x}{v} : \tau'}
      @|C-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellCE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-finite-subtyping" @elem{@${\tau \subt \tau} finite}]{
  All chains @${\tau_0 \subt \cdots \subt \tau_{n-1}} are finite.
}@tr-proof{
  By structural induction on @${\tau}, every type has a finite number of subtypes:

  @tr-case[@${\tau = \tnat}]{
    @tr-qed{
      zero subtypes}
  }

  @tr-case[@${\tau = \tint}]{
    @tr-qed{
      one subtype, @${\tnat}}
  }

  @tr-case[@${\tau = \tpair{\tau_0}{\tau_1}}]{
    @tr-step{
      @elem{@${\tau_0} has @${N_0} subtypes}
      @tr-IH}
    @tr-step{
      @elem{@${\tau_1} has @${N_1} subtypes}
      @tr-IH}
    @tr-qed{
      @${N_0 + N_1} subtypes}
  }

  @tr-case[@${\tau = \tarr{\tau_d}{\tau_c}}]{
    @tr-step{
      @elem{@${\tau_d} has @${N_d} supertypes}
      @|C-finite-supertyping|}
    @tr-step{
      @elem{@${\tau_c} has @${N_c} subtypes}
      @tr-IH}
    @tr-qed{
      @${N_d + N_c} subtypes}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-finite-supertyping" @elem{finite supertyping}]{
  Every type @${\tau} has a finite number of supertypes.
}@tr-proof{
  By structural induction on @${\tau}.

  @tr-case[@${\tau = \tnat}]{
    @tr-qed{
      one supertype, @${\tint}}
  }

  @tr-case[@${\tau = \tint}]{
    @tr-qed{
      zero supertypes}
  }

  @tr-case[@${\tau = \tpair{\tau_0}{\tau_1}}]{
    @tr-step{
      @elem{@${\tau_0} has @${N_0} supertypes}
      @tr-IH}
    @tr-step{
      @elem{@${\tau_1} has @${N_1} supertypes}
      @tr-IH}
    @tr-qed{
      @${N_0 + N_1} supertypes}
  }

  @tr-case[@${\tau = \tarr{\tau_d}{\tau_c}}]{
    @tr-step{
      @elem{@${\tau_d} has @${N_d} subtypes}
      @|C-finite-subtyping|}
    @tr-step{
      @elem{@${\tau_c} has @${N_c} supertypes}
      @tr-IH}
    @tr-qed{
      @${N_d + N_c} supertypes}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellCE e} then @${x,\Gamma \wellCE e}
    }
    @item{
      If @${\Gamma \wellCE e : \tau} then @${\tann{x}{\tau'},\Gamma \wellCE e : \tau}
    }
  ]
}@tr-proof{
  @; TODO
  @itemize[
    @item{
      @tr-step[
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellCE e
           @tr-or[]
           \Gamma \wellCE e : \tau}
      ]
    }
  ]
}

