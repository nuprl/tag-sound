#lang gf-pldi-2018
@require{techreport.rkt}

@appendix-title++{Natural Embedding}

@section{@${\langN} Definitions}
@exact{\input{fig:natural-embedding.tex}}

@|clearpage|
@section{@${\langN} Properties}

@(begin
   (define N-S-progress @tr-ref[#:key "N-S-progress"]{static progress})
   (define N-D-progress @tr-ref[#:key "N-D-progress"]{dynamic progress})
   (define N-S-preservation @tr-ref[#:key "N-S-preservation"]{static preservation})
   (define N-D-preservation @tr-ref[#:key "N-D-preservation"]{dynamic preservation})

   (define N-S-implies @tr-ref[#:key "N-S-implies"]{static implies})
   (define N-D-implies @tr-ref[#:key "N-D-implies"]{dynamic implies})

   (define N-S-uec @tr-ref[#:key "N-S-uec"]{unique evaluation contexts})
   (define N-D-uec @tr-ref[#:key "N-D-uec"]{unique evaluation contexts})

   (define N-S-hole-typing @tr-ref[#:key "N-S-hole-typing"]{static hole typing})
   (define N-D-hole-typing @tr-ref[#:key "N-D-hole-typing"]{dynamic hole typing})

   (define N-S-hole-subst @tr-ref[#:key "N-S-hole-subst"]{static hole substitution})
   (define N-D-hole-subst @tr-ref[#:key "N-D-hole-subst"]{dynamic hole substitution})

   (define N-S-inversion @tr-ref[#:key "N-S-inversion"]{inversion})
   (define N-D-inversion @tr-ref[#:key "N-D-inversion"]{inversion})

   (define N-S-canonical @tr-ref[#:key "N-S-canonical"]{canonical forms})

   (define N-Delta-soundness @tr-ref[#:key "N-Delta-type-soundness"]{@${\Delta} type soundness})
   (define N-delta-preservation @tr-ref[#:key "N-delta-preservation"]{@${\delta} preservation})

   (define N-SS-subst @tr-ref[#:key "N-SS-subst"]{substitution})
   (define N-DS-subst @tr-ref[#:key "N-DS-subst"]{substitution})
   (define N-SD-subst @tr-ref[#:key "N-SD-subst"]{substitution})
   (define N-DD-subst @tr-ref[#:key "N-DD-subst"]{substitution})

   (define N-finite-subtyping @tr-ref[#:key "N-finite-subtyping"]{finite subtyping})
   (define N-finite-supertyping @tr-ref[#:key "N-finite-supertyping"]{finite supertyping})
   (define N-weakening @tr-ref[#:key "N-weakening"]{weakening})

)

@tr-theorem[#:key "N-soundness" @elem{@${\langN} type soundness}]{
  If @${\wellM e : \tau} then @${\wellNE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrNEstar v \mbox{ and } \wellNE v : \tau} }
    @item{ @${e \rrNEstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccND \tagerror} }
    @item{ @${e \rrNEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step[
      @${\wellNE e : \tau}
      @|N-S-implies|
    ]}
    @item{@tr-qed{
      by @|N-S-progress| and @|N-S-preservation|.
    }}
  ]
}

@tr-lemma[#:key "N-S-implies" @elem{@${\langN} static implies}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellNE e : \tau}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e : \tau}

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellNE x : \tau}
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
      @${\tann{x}{\tau_d},\Gamma \wellNE e : \tau_c}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c}} }
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
      @${\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}} }
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
      @${\Gamma \wellNE e_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_d}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \vapp{e_0}{e_1} : \tau_c} }
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
      @${\Gamma \wellNE e_0 : \tau_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \eunop{e_0} : \tau} }
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
      @${\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \ebinop{e_0}{e_1} : \tau} }
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
      @${\Gamma \wellNE e : \tau'}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE e : \tau}
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
      @${\Gamma \wellNE e}
      @|N-D-implies|]
    @tr-step{
      @${\Gamma \wellNE \edyn{\tau}{e} : \tau}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "N-D-implies" @elem{@${\langN} dynamic implies}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellNE e}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e}.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @tr-step[
      @${\Gamma \wellNE x}
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
      @${x,\Gamma \wellNE e}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellNE \vlam{x}{e}}
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
      @${\Gamma \wellNE e_0
         @tr-and[]
         \Gamma \wellNE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE \vpair{e_0}{e_1}}
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
      @${\Gamma \wellNE e_0
         @tr-and[]
         \Gamma \wellNE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE \vapp{e_0}{e_1}}
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
      @${\Gamma \wellNE e}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE \eunop{e}}
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
      @${\Gamma \wellNE e_0
         @tr-and[]
         \Gamma \wellNE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE \ebinop{e_0}{e_1}}
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
      @${\Gamma \wellNE e : \tau}
      @|N-S-implies|}
    @tr-step{
      @${\Gamma \wellNE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "N-S-progress" @elem{@${\langN} static progress}]{
  If @${\wellNE e : \tau} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccNS e'} }
    @item{ @${e \ccNS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccND \tagerror} }
  ]
}@tr-proof{
  By the @|N-S-uec| lemma, there are five possible cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${\wellNE \vapp{v_0}{v_1} : \tau'}
      @|N-S-hole-typing|}
    @tr-step{
      @${\wellNE v_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \wellNE v_1 : \tau_d}
      @|N-S-inversion|}
    @tr-step{
      @${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}
      @|N-S-canonical|}
    @list[
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}}]{
        @tr-step[
          @${e \ccNS \ctxE{\vsubst{e'}{x}{v_1}}}
          @${\vapp{v_0}{v_1} \rrNS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}]{
        @tr-step{
          @${e \ccNS \ctxE{\edyn{\tau_c'}{(\vapp{v_f}{\esta{\tau_d'}{v_1}})}}}
          @${\vapp{v_0}{v_1} \rrNS \edyn{\tau_c'}{(\vapp{v_f}{\esta{\tau_d'}{v_1}})}}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step[
      @${\wellNE \eunop{v} : \tau'}
      @|N-S-hole-typing|]
    @tr-step[
      @${\wellNE v : \tpair{\tau_0}{\tau_1}}
      @|N-S-inversion|]
    @tr-step[
      @${v = \vpair{v_0}{v_1}}
      @|N-S-canonical|]
    @list[
      @tr-if[@${\vunop = \vfst}]{
        @${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}
        @tr-step{
          @${e \ccNS \ctxE{v_0}}
          @${\eunop{v} \rrNS v_0}}
        @tr-qed[]
      }
      @tr-else[@${\vunop = \vsnd}]{
        @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}
        @tr-step[
          @${e \ccNS \ctxE{v_1}}
          @${\eunop{v} \rrNS v_1}]
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step[
      @${\wellNE \ebinop{v_0}{v_1} : \tau'}
      @|N-S-hole-typing|]
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|N-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = A}
      @elem{@|N-Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrNS A}
      (3)}
    @tr-qed{
      by @${e \ccNS \ctxE{A}} if @${A \in v}
      @linebreak[]
      and by @${e \ccNS A} otherwise}
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\tau'}{e'}}} #:itemize? #false]{
    @tr-if[@${e' \in v} #:itemize? #false]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}
                @tr-and[2]
                e' = \vlam{x}{e''} \mbox{ or } e' = \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v}}]{
        @tr-step{
          @${e \ccNS \ctxE{\vmonfun{\tarr{\tau_d}{\tau_c}}{e'}}}
          @${\edyn{\tau'}{e'} \rrNS \vmonfun{\tarr{\tau_d}{\tau_c}}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tpair{\tau_0}{\tau_1}
                @tr-and[2]
                e' = \vpair{v_0}{v_1}}]{
        @tr-step{
          @${e \ccNS \ctxE{\vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}}}}
          @${\edyn{\tau'}{e'} \rrNS \vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}}}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tint
                @tr-and[2]
                e' \in i}]{
        @tr-step{
          @${e \ccNS \ctxE{e'}}
          @${\edyn{\tau'}{e'} \rrNS e'}}
        @tr-qed[]
      }
      @tr-if[@${\tau = \tnat
                @tr-and[2]
                e' \in \naturals}]{
        @tr-step{
          @${e \ccNS \ctxE{e'}}
          @${\edyn{\tau'}{e'} \rrNS e'}}
        @tr-qed[]
      }
      @tr-else[""]{
        @tr-qed{
          @${e \ccNS \boundaryerror}}
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccND A}
        @|N-D-progress|
      ]
      @tr-qed{
        by @${e \ccNS \ctxE{\edyn{\tau}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccNS A} otherwise}
    }
  }

}

@tr-lemma[#:key "N-D-progress" @elem{@${\langN} dynamic progress}]{
  If @${\wellNE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccND e'} }
    @item{ @${e \ccND \boundaryerror} }
    @item{ @${e \ccND \tagerror} }
  ]
}@tr-proof{
  By the @|N-D-uec| lemma, there are five cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccND \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrND \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}}]{
      @tr-step{
        @${e \ccND \ctxE{\esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
        @${\vapp{v_0}{v_1}
           \rrND \esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${(\vapp{v_0}{v_1}) \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${\delta(\vunop, v) = A}]{
      @tr-step{
        @${(\eunop{v}) \rrND A}}
      @tr-qed{
        by @${e \ccND \ctxE{A}} if @${A \in v}
        @linebreak[]
        and by @${e \ccND A} otherwise}
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${(\eunop{v}) \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = A}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrND A}}
      @tr-qed{
        by @${e \ccND \ctxE{A}} if @${A \in v}
        @linebreak[]
        and by @${e \ccND A} otherwise}
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${\ebinop{v_0}{v_1} \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}}]{
        @tr-step{
          @${e \ccNS \ctxE{\vmonfun{\tau'}{e'}}}
          @${\esta{\tau'}{e'} \rrNS \vmonfun{\tau'}{e'}}}
        @tr-qed[]
      }
      @tr-if[@${\tau' = \tpair{\tau_0}{\tau_1}}]{
        @tr-step{
          @${e \ccNS \ctxE{\vpair{\esta{\tau_0}{v_0}}{\esta{\tau_1}{v_1}}}}
          @${\esta{\tau'}{e'} \rrNS \vpair{\esta{\tau_0}{v_0}}{\esta{\tau_1}{v_1}}}}
        @tr-qed[]
      }
      @tr-if[@${\tau' = \tint}]{
        @tr-step{
          @${e \ccNS \ctxE{e'}}
          @${\esta{\tau'}{e'} = e'}}
        @tr-qed[]
      }
      @tr-else[@${\tau' = \tnat}]{
        @tr-step{
          @${e \ccNS \ctxE{e'}}
          @${\esta{\tau'}{e'} = e'}}
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion|}
      @tr-step{
        @${e' \ccNS A}
        @|N-S-progress| (2)}
      @tr-qed{
        by @${e \ccND \ctxE{\esta{\tau'}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccND A} otherwise}
    }
  }
}

@tr-lemma[#:key "N-S-preservation" @elem{@${\langN} static preservation}]{
  If @${\wellNE e : \tau} and @${e \ccNS e'} then @${\wellNE e' : \tau}
}@tr-proof{
  By the @|N-S-uec| lemma there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_x}}{e'}
              @tr-and[2]
              e \ccNS \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step[
        @${\wellNE \vapp{v_0}{v_1} : \tau'}
        @|N-S-hole-typing|]
      @tr-step{
        @${\wellNE v_0 : \tarr{\tau_d}{\tau_c}
           @tr-and[]
           \wellNE v_1 : \tau_d
           @tr-and[]
           \tau_c \subteq \tau'}
        @|N-S-inversion|}
      @tr-step{
        @${\tau_d \subteq \tau_x}
        @|N-S-canonical| (2)}
      @tr-step{
        @${\tann{x}{\tau_x} \wellNE e' : \tau_c}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\wellNE v_1 : \tau_x}
        (2, 3)}
      @tr-step{
        @${\wellNE \vsubst{e'}{x}{v_1} : \tau_c}
        @elem{@|N-SS-subst| (4, 5)}}
      @tr-step{
        @${\wellNE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|N-S-hole-subst| (7)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{v_f}
              @tr-and[4]
              e \ccNS \ctxE{\edyn{\tau_c}{(\vapp{v_f}{(\esta{\tau_d}{v_1})})}}}]{
      @tr-step{
        @${\wellNE \vapp{v_0}{v_1} : \tau'}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE v_0 : \tarr{\tau_d'}{\tau_c'}
           @tr-and[]
           \wellNE v_1 : \tau_d'
           @tr-and[]
           \tau_c' \subteq \tau'}
        @|N-S-inversion|}
      @tr-step{
        @${\wellNE v_f}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\tarr{\tau_d}{\tau_c} \subteq \tarr{\tau_d'}{\tau_c'}}
        @|N-S-canonical| (2)}
      @tr-step{
        @${\tau_d' \subteq \tau_d
           @tr-and[]
           \tau_c \subteq \tau_c'}
        (4)}
      @tr-step{
        @${\wellNE v_1 : \tau_d}
        (2, 5)}
      @tr-step{
        @${\wellNE \esta{\tau_d}{v_1}}
        (6)}
      @tr-step{
        @${\wellNE \vapp{v_f}{(\esta{\tau_d}{v_1})}}
        (3, 7)}
      @tr-step{
        @${\wellNE \edyn{\tau_c}{\vapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau_c}
        (8)}
      @tr-step{
        @${\wellNE \edyn{\tau_c}{\vapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|N-S-hole-subst| (10)}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccNS \ctxE{v_0}}]{
      @tr-step{
        @${\wellNE \efst{\vpair{v_0}{v_1}} : \tau'}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_0 \subteq \tau'}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\wellNE v_0 : \tau_0}
        @|N-S-inversion| (3)}
      @tr-step{
        @${\wellNE v_0 : \tau'}
        (2)}
      @tr-qed{
        by @|N-S-hole-subst| (4)}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccNS \ctxE{v_1}}]{
      @tr-step{
        @${\wellNE \esnd{\vpair{v_0}{v_1}} : \tau'}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_1 \subteq \tau'}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\wellNE v_1 : \tau_1}
        @|N-S-inversion| (3)}
      @tr-step{
        @${\wellNE v_1 : \tau'}
        (2)}
      @tr-qed{
        by @|N-S-hole-subst| (4)}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccNS \ctxE{v}}]{
    @tr-step{
      @${\wellNE \ebinop{v_0}{v_1} : \tau'}
      @|N-S-hole-typing|}
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''
         @tr-and[]
         \tau'' \subteq \tau'}
      @|N-S-inversion| (1)}
    @tr-step{
      @${\wellNE v : \tau''}
      @|N-Delta-soundness| (2)}
    @tr-step{
      @${\wellNE v : \tau'}
      (2, 3)}
    @tr-qed{
      by @|N-S-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \eeq \vlam{x}{e'}
              @tr-and[2]
              \tau' = \tarr{\tau_d}{\tau_c}
              @tr-and[2]
              e \ccNS \ctxE{\vmonfun{\tau'}{e'}}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE \vmonfun{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellNE \vmonfun{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
    @tr-if[@${e' \eeq \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v'}
              @tr-and[2]
              \tau' = \tarr{\tau_d}{\tau_c}
              @tr-and[2]
              e \ccNS \ctxE{\vmonfun{\tau'}{e'}}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE \vmonfun{\tau'}{e'} : \tau'}
        (2)}
      @tr-step{
        @${\wellNE \vmonfun{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
    @tr-if[@${e' \eeq \vpair{v_0}{v_1}
              @tr-and[2]
              \tau' = \tpair{\tau_0}{\tau_1}
              @tr-and[2]
              e \ccNS \ctxE{\vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}}}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE v_0
           @tr-and[]
           \wellNE v_1}
        @|N-D-inversion| (2)}
      @tr-step{
        @${\wellNE \edyn{\tau_0}{v_0} : \tau_0
           @tr-and[]
           \wellNE \edyn{\tau_1}{v_1} : \tau_1}
        (3)}
      @tr-step{
        @${\wellNE \vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}} : \tpair{\tau_0}{\tau_1}}
        (4)}
      @tr-step{
        @${\wellNE \vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}} : \tau''}
        (2, 5)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
    @tr-if[@${e' \eeq i
              @tr-and[2]
              \tau' = \tint
              @tr-and[2]
              e \ccNS \ctxE{i}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\tau' \subteq \tau''}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE i : \tau'}
        @${\tau' = \tint}}
      @tr-step{
        @${\wellNE i : \tau''}
        (2, 3)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
    @tr-if[@${e' \eeq i
              @tr-and[2]
              i \in \naturals
              @tr-and[2]
              \tau' = \tnat
              @tr-and[2]
              e \ccNS \ctxE{i}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\tau' \subteq \tau''}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE i : \tau'}
        @${\tau' = \tnat \mbox{ and } i \in \naturals}}
      @tr-step{
        @${\wellNE i : \tau''}
        (2, 3)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccND e''
                @tr-and[4]
                e \ccNS \ctxE{\edyn{\tau'}{e''}}}]{
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau''}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|N-S-inversion|}
      @tr-step{
        @${\wellNE e''}
        @|N-D-preservation|}
      @tr-step{
        @${\wellNE \edyn{\tau'}{e''} : \tau'}
        (3)}
      @tr-step{
        @${\wellNE \edyn{\tau'}{e''} : \tau''}
        (2, 4)}
      @tr-qed{
        by @|N-S-hole-subst|}
    }
  }
}

@tr-lemma[#:key "N-D-preservation" @elem{@${\langN} dynamic preservation}]{
  If @${\wellNE e} and @${e \ccND e'} then @${\wellNE e'}
}@tr-proof{
  By the @|N-D-uec| lemma, there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccND \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step{
        @${\wellNE \vapp{v_0}{v_1}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE v_0
           @tr-and[]
           \wellNE v_1}
        @|N-D-inversion| (1)}
      @tr-step{
        @${x \wellNE e'}
        @|N-D-inversion| (2)}
      @tr-step{
        @${\wellNE \vsubst{e'}{x}{v_1}}
        @|N-DD-subst| (2, 3)}
      @tr-qed{
        @|N-D-hole-subst| (4)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}
                @tr-and[4]
                e \ccND \ctxE{\esta{\tau_c}{(\vapp{v_f}{(\edyn{\tau_d}{v_1})})}}}]{
      @tr-step{
        @${\wellNE \vapp{v_0}{v_1}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE v_0
           @tr-and[]
           \wellNE v_1}
        @|N-D-inversion| (1)}
      @tr-step{
        @${\wellNE v_f : \tarr{\tau_d}{\tau_c}}
        @|N-D-inversion| (2)}
      @tr-step{
        @${\wellNE \edyn{\tau_d}{v_1} : \tau_d}
        (2)}
      @tr-step{
        @${\wellNE \vapp{v_f}{(\edyn{\tau_d}{v_1})} : \tau_c}
        (3, 4)}
      @tr-step{
        @${\wellNE \esta{\tau_c}{\vapp{v_f}{(\edyn{\tau_d}{v_1})}}}
        (5)}
      @tr-qed{
        by @|N-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccND \ctxE{v_0}}]{
      @tr-step{
        @${\wellNE \eunop{v}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE v}
        @|N-D-inversion| (1)}
      @tr-step{
        @${\wellNE v_0}
        @|N-D-inversion| (2)}
      @tr-qed{
        by @|N-D-hole-subst|}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccND \ctxE{v_1}}]{
      @tr-step{
        @${\wellNE \eunop{v}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE v}
        @|N-D-inversion| (1)}
      @tr-step{
        @${\wellNE v_1}
        @|N-D-inversion| (2)}
      @tr-qed{
        by @|N-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccND \ctxE{v}}]{
    @tr-step{
      @${\wellNE \ebinop{v_0}{v_1}}
      @|N-D-hole-typing|}
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE v_1}
      @|N-D-inversion| (1)}
    @tr-step{
      @${\wellNE v}
      @|N-delta-preservation| (2)}
    @tr-qed{
      by @|N-D-hole-subst| (3)}
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\tau' = \tarr{\tau_d}{\tau_c}
                @tr-and[2]
                e \ccND \ctxE{\vmonfun{\tau'}{e'}}}]{
        @tr-step{
          @${\wellNE \esta{\tau'}{e'}}
          @|N-D-hole-typing|}
        @tr-step{
          @${\wellNE e' : \tau'}
          @|N-D-inversion| (1)}
        @tr-step{
          @${\wellNE \vmonfun{\tau'}{e'}}
          (2)}
        @tr-qed{
          by @|N-D-hole-subst|}
      }
      @tr-if[@${\tau' = \tpair{\tau_0}{\tau_1}
                @tr-and[2]
                e' = \vpair{v_0}{v_1}
                @tr-and[2]
                e \ccND \ctxE{\vpair{\esta{\tau_0}{v_0}}{\esta{\tau_1}{v_1}}}}]{
        @tr-step{
          @${\wellNE \esta{\tau'}{e'}}
          @|N-D-hole-typing|}
        @tr-step{
          @${\wellNE e' : \tau'}
          @|N-D-inversion| (1)}
        @tr-step{
          @${\wellNE v_0 : \tau_0
             @tr-and[]
             \wellNE v_1 : \tau_1}
          @|N-S-inversion|}
        @tr-step{
          @${\wellNE \esta{\tau_0}{v_0}
             @tr-and[]
             \wellNE \esta{\tau_1}{v_1}}
          (4)}
        @tr-step{
          @${\wellNE \vpair{\esta{\tau_0}{v_0}}{\esta{\tau_1}{v_1}}}
          (5)}
        @tr-qed{
          by @|N-D-hole-subst| (6)}
      }
      @tr-if[@${\tau' = \tint
                @tr-and[2]
                e' \in i
                @tr-and[2]
                e \ccND \ctxE{e'}}]{
        @tr-step{
          @${\wellNE \esta{\tau'}{e'}}
          @|N-D-hole-typing|}
        @tr-step{
          @${\wellNE e'}
          @${e' \in i}}
        @tr-qed{
          by @|N-D-hole-subst| (2)}
      }
      @tr-else[@${\tau' = \tnat
                  @tr-and[4]
                  e' \in \naturals
                  @tr-and[4]
                  e \ccND \ctxE{e'}}]{
        @tr-step{
          @${\wellNE \esta{\tau'}{e'}}
          @|N-D-inversion|}
        @tr-step{
          @${\wellNE e'}
          @${e' \in \naturals}}
        @tr-qed{
          by @|N-D-hole-subst| (2)}
      }
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccNS e''
                @tr-and[4]
                e \ccND \ctxE{\esta{\tau'}{e''}}}]{
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-D-hole-typing|}
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion| (1)}
      @tr-step{
        @${\wellNE e'' : \tau'}
        @|N-S-preservation| (2)}
      @tr-step{
        @${\wellNE \esta{\tau'}{e''}}
        (3)}
      @tr-qed{
        by @|N-D-hole-subst| (4)}
    }
  }
}

@tr-lemma[#:key "N-S-uec" @elem{@${\langN} unique static evaluation contexts}]{
  If @${\wellNE e : \tau} then either:
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
    @tr-contradiction[@${\wellNE e : \tau}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}
              @tr-or[4]
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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

@tr-lemma[#:key "N-D-uec" @elem{@${\langN} unique dynamic evaluation contexts}]{
  If @${\wellNE e} then either:
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
    @tr-contradiction{@${\wellNE e}}
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} }]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellNE e_0}
        @|N-D-inversion|]
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
        @${\wellNE e_1}
        @|N-D-inversion|]
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
        @${\wellNE e_0}
        @|N-D-inversion|]
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
        @${\wellNE e_1}
        @|N-D-inversion|]
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
        @${\wellNE e_0}
        @|N-D-inversion|]
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
        @${\wellNE e_0}
        @|N-D-inversion|]
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
        @${\wellNE e_1}
        @|N-D-inversion|]
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

@tr-lemma[#:key "N-S-hole-typing" @elem{@${\langN} static hole typing}]{
  If @${\wellNE \ctxE{e} : \tau} then the derivation
   contains a sub-term @${\wellNE e : \tau'}
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
      @${\wellNE \ED_0[e] : \tarr{\tau_d}{\tau_c}}
      @|N-S-inversion|
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
      @${\wellNE \ED_1[e] : \tau_d}
      @|N-S-inversion|
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
      @${\wellNE \ED_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ED_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \ED_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ED_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ED_1[e] : \tau_1}
      @|N-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "N-D-hole-typing" @elem{@${\langN} dynamic hole typing}]{
  If @${\wellNE \ctxE{e}} then the derivation contains a sub-term @${\wellNE e}
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
      @${\wellNE \ED_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ED_1[e]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "N-S-hole-subst" @elem{@${\langN} static hole substitution}]{
  If @${\wellNE \ctxE{e} : \tau}
   and contains @${\wellNE e : \tau'},
   and furthermore @${\wellNE e' : \tau'},
   then @${\wellNE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\ED}

  @tr-case[@${\ED = \ehole}]{
    @tr-step{
      @${\ctxE{e} = e
         @tr-and[]
         \ctxE{e'} = e'}
    }
    @tr-step{
      @${\wellNE e : \tau}
      (1)
    }
    @tr-step{
      @${\tau' = \tau}
    }
    @tr-step{
      @${\wellNE e' : \tau}
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
      @${\wellNE \vpair{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellNE \ED_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{\ED_0[e']}{e_1} : \tau}
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
      @${\wellNE \vpair{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ED_1[e] : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{v_0}{\ED_1[e']} : \tau}
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
      @${\wellNE \ED_0[e]~e_1 : \tau}
    }
    @tr-step{
      @${\wellNE \ED_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ED_0[e']~e_1 : \tau}
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
      @${\wellNE v_0~\ED_1[e] : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ED_1[e] : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE v_0~\ED_1[e'] : \tau}
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
      @${\wellNE \eunop{\ED_0[e]} : \tau}
    }
    @tr-step{
      @${\wellNE \ED_0[e] : \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \eunop{\ED_0[e']} : \tau}
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
      @${\wellNE \ebinop{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellNE \ED_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{\ED_0[e']}{e_1} : \tau}
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
      @${\wellNE \ebinop{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ED_1[e] : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{v_0}{\ED_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@tr-lemma[#:key "N-D-hole-subst" @elem{@${\langN} dynamic hole substitution}]{
  If @${\wellNE \ctxE{e}} and @${\wellNE e'} then @${\wellNE \ctxE{e'}}
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
      @${\wellNE \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \ED_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{\ED_0[e']}{e_1}}
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
      @${\wellNE \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ED_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{v_0}{\ED_1[e']}}
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
      @${\wellNE \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellNE \ED_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ED_0[e']~e_1}
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
      @${\wellNE v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ED_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE v_0~\ED_1[e']}
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
      @${\wellNE \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellNE \ED_0[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \eunop{\ED_0[e']}}
      (4)
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
      @${\wellNE \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \ED_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{\ED_0[e']}{e_1}}
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
      @${\wellNE \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ED_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-S-inversion" @elem{@${\wellNE} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellNE x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellNE e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \vpair{e_0}{e_1} : \tau}
      then @${\Gamma \wellNE e_0 : \tau_0}
      and @${\Gamma \wellNE e_1 : \tau_1}
      and @${\tpair{\tau_0}{\tau_1} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \vapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellNE e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellNE e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellNE \efst{e} : \tau}
      then @${\Gamma \wellNE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \esnd{e} : \tau}
      then @${\Gamma \wellNE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellNE e_0 : \tau_0}
      and @${\Gamma \wellNE e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{v'} : \tau}
      then @${\Gamma \wellNE v'}
      and @${\tarr{\tau_d}{\tau_c} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellNE \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellNE e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellNE e : \tau} and by @|N-finite-subtyping|
  }
}

@tr-lemma[#:key "N-D-inversion" @elem{@${\wellNE} dynamic inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellNE x}
      then @${x \in \Gamma}
    }
    @item{
      If @${\Gamma \wellNE \vlam{x}{e'}}
      then @${x,\Gamma \wellNE e'}
    }
    @item{
      If @${\Gamma \wellNE \vpair{e_0}{e_1}}
      then @${\Gamma \wellNE e_0}
      and @${\Gamma \wellNE e_1}
    }
    @item{
      If @${\Gamma \wellNE \vapp{e_0}{e_1}}
      then @${\Gamma \wellNE e_0}
      and @${\Gamma \wellNE e_1}
    }
    @item{
      If @${\Gamma \wellNE \eunop{e_0}}
      then @${\Gamma \wellNE e_0}
    }
    @item{
      If @${\Gamma \wellNE \ebinop{e_0}{e_1}}
      then @${\Gamma \wellNE e_0}
      and @${\Gamma \wellNE e_1}
    }
    @item{
      If @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}
      then @${\Gamma \wellNE v' : \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellNE \esta{\tau'}{e'}}
      then @${\Gamma \wellNE e' : \tau'}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellNE e}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-S-canonical" @elem{@${\langN} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellNE v : \tpair{\tau_0}{\tau_1}}
      then @${v \eeq \vpair{v_0}{v_1}}
    }
    @item{
      If @${\wellNE v : \tarr{\tau_d}{\tau_c}}
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
      If @${\wellNE v : \tint}
      then @${v \in i}
    }
    @item{
      If @${\wellNE v : \tnat}
      then @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellNE e : \tau}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-Delta-type-soundness" @elem{@${\Delta} type soundness}]{
  If @${\wellNE v_0 : \tau_0 \mbox{ and }
        \wellNE v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then either:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellNE v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on the definition of @${\Delta}.

  @tr-case[@${\Delta(\vsum, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|N-S-canonical|
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
      @|N-S-canonical|
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
      @|N-S-canonical|
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
      @|N-S-canonical|
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
@tr-lemma[#:key "N-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellNE v} and @${\delta(\vunop, v) = v'} then @${\wellNE v'}
    }
    @item{
      If @${\wellNE v_0} and @${\wellNE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellNE v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellNE v_0}
      @|N-D-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellNE v_1}
      @|N-D-inversion|
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
@tr-lemma[#:key "N-SS-subst" @elem{@${\langN} static-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellNE e : \tau}
  and @${\wellNE v : \tau_x}
  then @${\Gamma \wellNE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE x : \tau}}
    @tr-step{
      @${\tau_x \subteq \tau}
      @|N-S-inversion|}
    @tr-step{
      @${\wellNE v : \tau}
      (3)}
    @tr-step{
      @${\Gamma \wellNE v : \tau}
      @|N-weakening|}
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
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellNE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},\tann{x}{\tau_x},\Gamma \wellNE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellNE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellNE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE v'}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{v'}{x}{v}}
      @|N-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0 : \tau_0}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e'}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e'}{x}{v}}
      @|N-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-SD-subst" @elem{@${\langN} static-dynamic substitution}]{
  If @${x,\Gamma \wellNE e : \tau}
  and @${\wellNE v}
  then @${\Gamma \wellNE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${x,\Gamma \wellNE x : \tau}}
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
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellNE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellNE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellNE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellNE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellNE v'}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{v'}{x}{v}}
      @|N-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0 : \tau_0}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellNE e_1 : \tau_1}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e'}
      @|N-S-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e'}{x}{v}}
      @|N-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-DS-subst" @elem{@${\langN} dynamic-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellNE e}
  and @${\wellNE v : \tau_x}
  then @${\Gamma \wellNE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellNE x}}
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
      @${x',\tann{x}{\tau_x},\Gamma \wellNE e'}
      @|N-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellNE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellNE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellNE e}}
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE v' : \tarr{\tau_d}{\tau_c}}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{v'}{x}{v} : \tarr{\tau_d}{\tau_c}}
      @|N-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellNE e' : \tau'}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e'}{x}{v} : \tau'}
      @|N-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-DD-subst" @elem{@${\langN} dynamic-dynamic substitution}]{
  If @${x,\Gamma \wellNE e}
  and @${\wellNE v}
  then @${\Gamma \wellNE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\Gamma \wellNE v}
      @|N-weakening|}
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
      @${x',x,\Gamma \wellNE e'}
      @|N-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellNE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellNE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${x,\Gamma \wellNE e}}
  }

  @tr-case[@${e = \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellNE v' : \tarr{\tau_d}{\tau_c}}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{v'}{x}{v} : \tarr{\tau_d}{\tau_c}}
      @|N-SD-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vsubst{v'}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0
         @tr-and[]
         x,\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0
         @tr-and[]
         x,\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e_0
         @tr-and[]
         x,\Gamma \wellNE e_1}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellNE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellNE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellNE e' : \tau'}
      @|N-D-inversion|}
    @tr-step{
      @${\Gamma \wellNE \vsubst{e'}{x}{v} : \tau'}
      @|N-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellNE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-finite-subtyping" @elem{@${\tau \subt \tau} finite}]{
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
      @|N-finite-supertyping|}
    @tr-step{
      @elem{@${\tau_c} has @${N_c} subtypes}
      @tr-IH}
    @tr-qed{
      @${N_d + N_c} subtypes}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-finite-supertyping" @elem{finite supertyping}]{
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
      @|N-finite-subtyping|}
    @tr-step{
      @elem{@${\tau_c} has @${N_c} supertypes}
      @tr-IH}
    @tr-qed{
      @${N_d + N_c} supertypes}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "N-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellNE e} then @${x,\Gamma \wellNE e}
    }
    @item{
      If @${\Gamma \wellNE e : \tau} then @${\tann{x}{\tau'},\Gamma \wellNE e : \tau}
    }
  ]
}@tr-proof{
  @; TODO
  @itemize[
    @item{
      @tr-step[
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellNE e
           @tr-or[]
           \Gamma \wellNE e : \tau}
      ]
    }
  ]
}

