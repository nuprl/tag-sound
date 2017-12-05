#lang gf-pldi-2018
@require{techreport.rkt}

@appendix-title++{Forgetful Embedding}

@section{@${\langF} Definitions}
@exact{\input{fig:forgetful-embedding.tex}}

@|clearpage|
@section{@${\langF} Properties}

@(begin
   (define F-S-progress @tr-ref[#:key "F-S-progress"]{static progress})
   (define F-D-progress @tr-ref[#:key "F-D-progress"]{dynamic progress})
   (define F-S-preservation @tr-ref[#:key "F-S-preservation"]{static preservation})
   (define F-D-preservation @tr-ref[#:key "F-D-preservation"]{dynamic preservation})

   (define F-check-soundness @tr-ref[#:key "F-check-soundness"]{check soundness})

   (define F-S-implies @tr-ref[#:key "F-S-implies"]{static implies})
   (define F-D-implies @tr-ref[#:key "F-D-implies"]{dynamic implies})

   (define F-S-uec @tr-ref[#:key "F-S-uec"]{unique evaluation contexts})
   (define F-D-uec @tr-ref[#:key "F-D-uec"]{unique evaluation contexts})

   (define F-S-hole-typing @tr-ref[#:key "F-S-hole-typing"]{static hole typing})
   (define F-D-hole-typing @tr-ref[#:key "F-D-hole-typing"]{dynamic hole typing})

   (define F-S-hole-subst @tr-ref[#:key "F-S-hole-subst"]{static hole substitution})
   (define F-D-hole-subst @tr-ref[#:key "F-D-hole-subst"]{dynamic hole substitution})

   (define F-S-inversion @tr-ref[#:key "F-S-inversion"]{inversion})
   (define F-D-inversion @tr-ref[#:key "F-D-inversion"]{inversion})

   (define F-S-canonical @tr-ref[#:key "F-S-canonical"]{canonical forms})

   (define F-Delta-soundness @tr-ref[#:key "F-Delta-soundness"]{@${\Delta} tag soundness})
   (define F-delta-preservation @tr-ref[#:key "F-delta-preservation"]{@${\delta} preservation})

   @; TODO need these?
   @;(define F-S-value-inversion @tr-ref[#:key "F-S-value-inversion"]{static value inversion})
   @;(define F-D-value-inversion @tr-ref[#:key "F-D-value-inversion"]{dynamic value inversion})

   (define F-S-subst @tr-ref[#:key "F-S-subst"]{substitution})
   (define F-D-subst @tr-ref[#:key "F-D-subst"]{substitution})

   (define F-finite-subtyping @tr-ref[#:key "F-finite-subtyping"]{finite subtyping})
   (define F-weakening @tr-ref[#:key "F-weakening"]{weakening})
)

@tr-theorem[#:key "F-soundness" @elem{@${\langF} type soundness}]{
  If @${\wellM e : \tau} then @${\wellFE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrFEstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFEstar \ctxE{e'} \mbox{ and } e' \ccFD \tagerror} }
    @item{ @${e \rrFEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step[
      @${\wellFE e : \tau}
      @|F-S-implies|
    ]}
    @item{@tr-qed{
      by @|F-S-progress| and @|F-S-preservation|.
    }}
  ]
}

@tr-lemma[#:key "F-S-implies" @elem{@${\langF} static implies}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellFE e : \tau}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e : \tau}

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellFE x : \tau}
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
      @${\tann{x}{\tau_d},\Gamma \wellFE e : \tau_c}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c}}
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
                \Gamma \wellM i : \tint
              }}]{
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\\\
                \Gamma \wellM e_1 : \tau_1
              }{
                \Gamma \wellM \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}
              }}]{
    @tr-step[
      @${\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_d \tarrow \tau_c
                \\\\
                \Gamma \wellM e_1 : \tau_d
              }{
                \Gamma \wellM e_0~e_1 : \tau_c
              }}]{
    @tr-step[
      @${\Gamma \wellFE e_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_d}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \vapp{e_0}{e_1} : \tau_c}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\\\
                \Delta(\vunop, \tau_0) = \tau
              }{
                \Gamma \wellM \vunop~e_0 : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellFE e_0 : \tau_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \eunop{e_0} : \tau}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\
                \Gamma \wellM e_1 : \tau_1
                \\\\
                \Delta(\vbinop, \tau_0, \tau_1) = \tau
              }{
                \Gamma \wellM \vbinop~e_0~e_1 : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \ebinop{e_0}{e_1} : \tau}
      (1)}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau'
                \\\\
                \tau' \subt \tau
              }{
                \Gamma \wellM e : \tau
              }}]{
    @tr-step[
      @${\Gamma \wellFE e : \tau'}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE e : \tau}
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
      @${\Gamma \wellFE e}
      @|F-D-implies|]
    @tr-step{
      @${\Gamma \wellFE \edyn{\tau}{e} : \tau}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-D-implies" @elem{@${\langF} dynamic implies}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellFE e}.
}@tr-proof{
  By structural induction on @${\Gamma \wellM e}.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @tr-step[
      @${\Gamma \wellFE x}
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
      @${x,\Gamma \wellFE e}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \vlam{x}{e}}
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
      @${\Gamma \wellFE e_0
         @tr-and[]
         \Gamma \wellFE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellFE \vpair{e_0}{e_1}}
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
      @${\Gamma \wellFE e_0
         @tr-and[]
         \Gamma \wellFE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellFE \vapp{e_0}{e_1}}
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
      @${\Gamma \wellFE e}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellFE \eunop{e}}
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
      @${\Gamma \wellFE e_0
         @tr-and[]
         \Gamma \wellFE e_1}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellFE \ebinop{e_0}{e_1}}
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
      @${\Gamma \wellFE e : \tau}
      @|F-S-implies|}
    @tr-step{
      @${\Gamma \wellFE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-S-progress" @elem{${\langF} static progress}]{
  If @${\wellFE e : \tau} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccFS e'} }
    @item{ @${e \ccFS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccFD \tagerror} }
  ]
}@tr-proof{
  By the @|F-S-uec| lemma, there are five possible cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${\wellFE \vapp{v_0}{v_1} : \tau_c}
      @|F-S-hole-typing|}
    @tr-step{
      @${\wellFE v_0 : \tarr{\tau_d'}{\tau_c'}
         @tr-and[]
         \wellFE v_1 : \tau_d'
         @tr-and[]
         \tau_c' \subteq \tau_c}
      @|F-S-inversion|}
    @tr-step{
      @${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_d'}}{e'}}}
      @|F-S-canonical|}
    @list[
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}}]{
        @tr-step[
          @${e \ccFS \ctxE{\vsubst{e'}{x}{v_1}}}
          @${\vapp{(\vlam{\tann{x}{\tau_d'}}{e'})}{v_1} \rrFS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
                @tr-and[2]
                \mchk{\tau_d'}{v_1} = v_1'}]{
        @tr-step[
          @${e \ccFS \ctxE{\edyn{\tau_c'}{(\vsubst{e'}{x}{v_1'})}}}
          @${\vapp{(\vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}})}{v_1} \rrFS \edyn{\tau_c'}{(\vsubst{e'}{x}{v_1'})}}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
                @tr-and[2]
                \mchk{\tau_d'}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccFS \boundaryerror}
          @${\vapp{(\vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}})}{v_1} \rrFS \boundaryerror}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}}
                @tr-and[2]
                \mchk{\tau_x}{v_1} = v_1'}]{
        @tr-step[
          @${e \ccFS \ctxE{\vsubst{e'}{x}{v_1'}}}
          @${\vapp{(\vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}})}{v_1} \rrFS \vsubst{e'}{x}{v_1'}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}}
                  @tr-and[4]
                  \mchk{\tau_x}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccFS \boundaryerror}
          @${\vapp{(\vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}})}{v_1} \rrFS \boundaryerror}]
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e = \ctxE{\eunop{v}}}]{
    @tr-step[
      @${\wellFE \eunop{v} : \tau'}
      @|F-S-hole-typing|]
    @tr-step[
      @${\wellFE v : \tpair{\tau_0}{\tau_1}}
      @|F-S-inversion|]
    @tr-step[
      @${v = \vpair{v_0}{v_1}
         @tr-or[]
         v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
      @|F-S-canonical|]
    @list[
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vfst}]{
        @tr-step{
          @${\eunop{v} \rrFS v_0}
          @${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}}
        @tr-step{
          @${e \ccFS \ctxE{v_0}}
          (1)}
        @tr-qed[]
      }
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vsnd}]{
        @tr-step[
          @${\eunop{v} \rrFS v_1}
          @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]
        @tr-step{
          @${e \ccFS \ctxE{v_1}}
          (1)}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vfst
                @tr-and[2]
                \mchk{\tau_0}{v_0} = v_0'}]{
        @tr-step{
          @${e \ccFS \ctxE{v_0'}}
          @${\efst{(\vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}})} \rrFS v_0'}}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vfst
                @tr-and[2]
                \mchk{\tau_0}{v_0} = \boundaryerror}]{
        @tr-step{
          @${e \ccFS \boundaryerror}
          @${\efst{(\vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}})} \rrFS \boundaryerror}}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vsnd
                @tr-and[2]
                \mchk{\tau_1}{v_1} = v_1'}]{
        @tr-step{
          @${e \ccFS \ctxE{v_1'}}
          @${\esnd{(\vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}})} \rrFS v_1'}}
        @tr-qed[]
      }
      @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                  @tr-and[4]
                  \vunop = \vsnd
                  @tr-and[4]
                  \mchk{\tau_1}{v_1} = \boundaryerror}]{
        @tr-step{
          @${e \ccFS \boundaryerror}
          @${\esnd{(\vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}})} \rrFS \boundaryerror}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step[
      @${\wellFE \ebinop{v_0}{v_1} : \tau'}
      @|F-S-hole-typing|]
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = A}
      @elem{@|Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrFS A}
      (3)}
    @tr-qed{
      by @${e \ccFS \ctxE{A}} if @${A \in v}
      @linebreak[]
      and by @${e \ccFS A} otherwise}
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\tau'}{e'}}} #:itemize? #false]{
    @tr-if[@${e' \in v} #:itemize? #false]{
      @tr-if[@${\mchk{\tagof{\tau}}{e'} = e''}]{
        @tr-step[
          @${e \ccFS \ctxE{e''}}
          @${(\edyn{\tau}{e'}) \rrFS e''}]
        @tr-qed[]
      }
      @tr-else[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @tr-step[
          @${e \ccFS \boundaryerror}
          @${(\edyn{\tau}{e'}) \rrFS \boundaryerror}]
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccFD A}
        @|F-D-progress|
      ]
      @tr-qed{
        by @${e \ccFS \ctxE{\edyn{\tau}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccFS A} otherwise}
    }
  }

}

@tr-lemma[#:key "F-D-progress" @elem{${\langF} dynamic progress}]{
  If @${\wellFE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccFD e'} }
    @item{ @${e \ccFD \boundaryerror} }
    @item{ @${e \ccFD \tagerror} }
  ]
}@tr-proof{
  By the @|F-D-uec| lemma, there are five cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccFD \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{(\vlam{x}{e'})}{v_1} \rrFD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})}
             @tr-and[2]
             \mchk{\tau_d}{v_1} = v_1'}]{
      @tr-step{
        @${e \ccFD \ctxE{\vsubst{e'}{x}{v_1'}}}
        @${\vapp{(\vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})})}{v_1}
           \rrFD \vsubst{e'}{x}{v_1'}}}
      @tr-qed[]
    }
    @tr-if[${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})}
             @tr-and[2]
             \mchk{\tau_d}{v_1} = \boundaryerror}]{
      @tr-step[
        @${e \ccFD \boundaryerror}
        @${\vapp{(\vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})})}{v_1} \rrFD \boundaryerror}]
      @tr-qed[]
    }
    @tr-if[${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})}
             @tr-and[2]
             \mchk{\tau_x}{v_1} = v_1'}]{
      @tr-step{
        @${e \ccFD \ctxE{\vsubst{e'}{x}{v_1'}}}
        @${\vapp{(\vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})})}{v_1}
           \rrFD \vsubst{e'}{x}{v_1'}}}
      @tr-qed[]
    }
    @tr-if[${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})}
             @tr-and[2]
             \mchk{\tau_x}{v_1} = \boundaryerror}]{
      @tr-step[
        @${e \ccFD \boundaryerror}
        @${\vapp{(\vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})})}{v_1}
           \rrFD \boundaryerror}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_x}}{e'}}]{
      @tr-contradiction{@${\wellFE e}}
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${(\vapp{v_0}{v_1}) \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${\delta(\vunop, v) = A}]{
      @tr-step{
        @${(\eunop{v}) \rrFD A}}
      @tr-qed{
        by @${e \ccFD \ctxE{A}} if @${A \in v}
        @linebreak[]
        and by @${e \ccFD A} otherwise}
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${(\eunop{v}) \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = A}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrFD A}}
      @tr-qed{
        by @${e \ccFD \ctxE{A}} if @${A \in v}
        @linebreak[]
        and by @${e \ccFD A} otherwise}
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${\ebinop{v_0}{v_1} \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #false]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccFS \ctxE{e'}}
        @${(\esta{\tau}{e'}) \rrFS e'}}
      @tr-qed[]
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccFS A}
        @|F-S-progress|]
      @tr-qed{
        by @${e \ccFD \ctxE{\edyn{\tau}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccFD A} otherwise}
    }
  }
}

@tr-lemma[#:key "F-S-preservation" @elem{${\langF} static preservation}]{
  If @${\wellFE e : \tau} and @${e \ccFS e'} then @${\wellFE e' : \tau}
}@tr-proof{
  By the @|F-S-uec| lemma there are TODO cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{

  }
}

@tr-lemma[#:key "F-D-preservation" @elem{${\langF} dynamic preservation}]{
  If @${\wellFE e} and @${e \ccFD e'} then @${\wellFE e'}
}@tr-proof{
  TODO
}

@tr-lemma[#:key "F-check-soundness" @elem{@${\mchk{\cdot}{\cdot}} soundness}]{
  If @${\mchk{\tau}{v} = v'} then @${\wellFE v' : \tau}
}@tr-proof{
  By case analysis of the definition of @${\mchk{\cdot}{\cdot}}.

  @tr-case[@${\mchk{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed[
      @${\wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}]
    }

  @tr-case[@${\mchk{\tarr{\tau_d}{\tau_c}}{(\vmonfun{\tau'}{v})} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed[
      @${\wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}]
  }

  @tr-case[@${\mchk{\tpair{\tau_0}{\tau_1}}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-qed[
      @${\wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v} : \tpair{\tau_0}{\tau_1}}]
  }

  @tr-case[@${\mchk{\tpair{\tau_0}{\tau_1}}{(\vmonpair{\tau'}{v})} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-qed[
      @${\wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v} : \tpair{\tau_0}{\tau_1}}]
  }

  @tr-case[@${\mchk{\tint}{i} = i}]{
    @tr-qed[
      @${\wellFE i : \tint}]
  }

  @tr-case[@${\mchk{\tnat}{i} = i} @tr-and[4] i \in \naturals]{
    @tr-step[
      @${\wellFE i : \tnat}
      @${i \in \naturals}]
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-S-uec" @elem{@${\langF} unique static evaluation contexts}]{
  If @${\wellFE e : \tau} then either:
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
    @tr-contradiction[@${\wellFE e : \tau}]
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
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step[
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vpair{ED_0}{e_1}}
      ]
      @tr-qed{
        @$e = \ED[e_0']
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step[
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vpair{e_0}{ED_1}}
      ]
      @tr-qed{
        @$e = \ED[e_1']
      }
    }
    @tr-else[@${e_0 \in v \tr-and[4] e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e} is a value
      }
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step[
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vapp{ED_0}{e_1}}
      ]
      @tr-qed{
        @$e = \ED[e_0']
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step[
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \vapp{e_0}{ED_1}}
      ]
      @tr-qed{
        @$e = \ED[e_1']
      }
    }
    @tr-else[@${e_0 \in v \tr-and[4] e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\vapp{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step[
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|
      ]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \eunop{\ED}}
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
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step[
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \ebinop{ED_0}{e_1}}
      ]
      @tr-qed{
        @$e = \ED[e_0']
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step[
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      ]
      @tr-step[
        @${\ED = \ebionp{e_0}{ED_1}}
      ]
      @tr-qed{
        @$e = \ED[e_1']
      }
    }
    @tr-else[@${e_0 \in v \tr-and[4] e_1 \in v}]{
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

@tr-lemma[#:key "F-D-uec" @elem{@${\langF} unique dynamic evaluation contexts}]{
  If @${\wellFE e} then either:
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
    @tr-contradiction{@${\wellFE e}}
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
        @${\wellFE e_0}
        @|F-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
      @tr-step{
        @${\ED = \vpair{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \not\in v @tr-and[2] e_1 \in v}]{
      @tr-step[
        @${\wellFE e_1}
        @|F-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}}
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
        @${\wellFE e_0}
        @|F-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
      @tr-step{
        @${\ED = \vapp{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \not\in v @tr-and[2] e_1 \in v}]{
      @tr-step[
        @${\wellFE e_1}
        @|F-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}}
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
        @${\wellFE e_0}
        @|F-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
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
        @${\wellFE e_0}
        @|F-D-inversion|]
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
      @tr-step{
        @${\ED = \ebinop{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \not\in v @tr-and[2] e_1 \in v}]{
      @tr-step[
        @${\wellFE e_1}
        @|F-D-inversion|]
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}}
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

@tr-lemma[#:key "F-S-hole-typing" @elem{@${\langF} hole typing}]{
  If @${\wellFE \ctxE{e} : \tau} then the derivation
   contains a sub-term @${\wellFE e : \tau'}
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
      @${\wellFE \ED_0[e] : \tarr{\tau_d}{\tau_c}}
      @|F-S-inversion|
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
      @${\wellFE \ED_1[e] : \tau_d}
      @|F-S-inversion|
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
      @${\wellFE \ED_0[e] : \tau_0}
      @|F-S-inversion|
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
      @${\wellFE \ED_1[e] : \tau_1}
      @|F-S-inversion|
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
      @${\wellFE \ED_0[e] : \tau_0}
      @|F-S-inversion|
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
      @${\wellFE \ED_0[e] : \tau_0}
      @|F-S-inversion|
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
      @${\wellFE \ED_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "F-D-hole-typing" @elem{@${\langF} hole typing}]{
  If @${\wellFE \ctxE{e}} then the derivation contains a sub-term @${\wellFE e}
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
      @${\wellFE \ED_0[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_1[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_0[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_1[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_0[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_0[e]}
      @|F-D-inversion|
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
      @${\wellFE \ED_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "F-S-hole-subst" @elem{@${\langF} static hole substitution}]{
  If @${\wellFE \ctxE{e} : \tau}
   and contains @${\wellFE \ctxE{e} : \tau'},
   and furthermore @${\wellFE e' : \tau'},
   then @${\wellFE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\ED}

  @tr-case[@${\ED = \ehole}]{
    @tr-step{
      @${\ctxE{e} = e
         @tr-and[]
         \ctxE{e'} = e'}
    }
    @tr-step{
      @${\wellFE e : \tau}
      (1)
    }
    @tr-step{
      @${\tau' = \tau}
    }
    @tr-step{
      @${\wellFE e' : \tau}
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
      @${\wellFE \vpair{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellFE \ED_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{\ED_0[e']}{e_1} : \tau}
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
      @${\wellFE \vpair{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ED_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ED_1[e']} : \tau}
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
      @${\wellFE \ED_0[e]~e_1 : \tau}
    }
    @tr-step{
      @${\wellFE \ED_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ED_0[e']~e_1 : \tau}
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
      @${\wellFE v_0~\ED_1[e] : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ED_1[e] : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE v_0~\ED_1[e'] : \tau}
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
      @${\wellFE \eunop{\ED_0[e]} : \tau}
    }
    @tr-step{
      @${\wellFE \ED_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \eunop{\ED_0[e']} : \tau}
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
      @${\wellFE \ebinop{\ED_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellFE \ED_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ED_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{\ED_0[e']}{e_1} : \tau}
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
      @${\wellFE \ebinop{v_0}{\ED_1[e]} : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ED_1[e] : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ED_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ED_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }
}

@tr-lemma[#:key "F-D-hole-subst" @elem{@${\langF} dynamic hole substitution}]{
  If @${\wellFE \ctxE{e}} and @${\wellFE e'} then @${\wellFE \ctxE{e'}}
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
      @${\wellFE \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ED_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{\ED_0[e']}{e_1}}
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
      @${\wellFE \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ED_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ED_1[e']}}
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
      @${\wellFE \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellFE \ED_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ED_0[e']~e_1}
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
      @${\wellFE v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ED_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE v_0~\ED_1[e']}
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
      @${\wellFE \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellFE \ED_0[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \eunop{\ED_0[e']}}
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
      @${\wellFE \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ED_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{\ED_0[e']}{e_1}}
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
      @${\wellFE \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ED_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ED_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }
}

@tr-lemma[#:key "F-S-inversion" @elem{@${\wellFE} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellFE x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellFE \vlam{\tann{x}{\tau_d'}}{e'} : \tarr{\tau_d}{\tau_c}}
      then @${\tann{x}{\tau_d'},\Gamma \wellFE e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}.
    }
    @item{
      If @${\Gamma \wellFE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}}
      then @${\Gamma \wellFE e_0 : \tau_0'}
      and @${\Gamma \wellFE e_1 : \tau_1'}
      and @${\tau_0' \subteq \tau_0}
      and @${\tau_1' \subteq \tau_1}
    }
    @item{
      If @${\Gamma \wellFE \vapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellFE e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellFE e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellFE \efst{e} : \tau}
      then @${\Gamma \wellFE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellFE \esnd{e} : \tau}
      then @${\Gamma \wellFE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellFE \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellFE e_0 : \tau_0}
      and @${\Gamma \wellFE e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellFE \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellFE e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellFE e : \tau}
  }
}

@tr-lemma[#:key "F-D-inversion" @elem{@${\wellFE} dynamic inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellFE x}
      then @${x \in \Gamma}
    }
    @item{
      If @${\Gamma \wellFE \vlam{x}{e'}}
      then @${x,\Gamma \wellFE e'}
    }
    @item{
      If @${\Gamma \wellFE \vpair{e_0}{e_1}}
      then @${\Gamma \wellFE e_0}
      and @${\Gamma \wellFE e_1}
    }
    @item{
      If @${\Gamma \wellFE \vapp{e_0}{e_1}}
      then @${\Gamma \wellFE e_0}
      and @${\Gamma \wellFE e_1}
    }
    @item{
      If @${\Gamma \wellFE \eunop{e_0}}
      then @${\Gamma \wellFE e_0}
    }
    @item{
      If @${\Gamma \wellFE \ebinop{e_0}{e_1}}
      then @${\Gamma \wellFE e_0}
      and @${\Gamma \wellFE e_1}
    }
    @item{
      If @${\Gamma \wellFE \esta{\tau'}{e'}}
      then @${\Gamma \wellFE e' : \tau'}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellFE e}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-S-canonical" @elem{@${\langF} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellFE v : \tpair{\tau_0}{\tau_1}}
      then @${v \eeq \vpair{v_0}{v_1}
              \mbox{ or }
              v \eeq \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
    }
    @item{
      If @${\wellFE v : \tarr{\tau_d}{\tau_c}}
      then @${v \eeq \vlam{\tann{x}{\tau_d}}{e'}
              \mbox{ or }
              v \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}}
    }
    @item{
      If @${\wellFE v : \tint}
      then @${v \eeq i}
    }
    @item{
      If @${\wellFE v : \tnat}
      then @${v \eeq i} and @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellFE \cdot : \tau}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-Delta-soundness" @elem{@${\Delta} tag soundness}]{
  If @${\wellFE v_0 : \tau_0 \mbox{ and }
        \wellFE v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then either:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellFE v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on @${\Delta}.

  @tr-case[@${\Delta(\vsum, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|F-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 = i}
    }
    @tr-step{
      @${i \in \naturals}
    }
    @tr-qed{
      by @${\wellFE i : \tnat}
    }
  }

  @tr-case[@${\Delta(\vsum, \tint, \tint) = \tint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|F-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 = i}
    }
    @tr-qed{
      by @${\wellFE i : \tint}
    }
  }

  @tr-case[@${\Delta(\vquotient, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|F-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1}} = i }
        @tr-step{
          @${i \in \naturals} }
        @tr-qed{
          by @${\wellFE i : \tnat} }
      }
    ]
  }

  @tr-case[@${\Delta(\vquotient, \tint, \tint) = \tint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|F-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror} }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1}} = i }
        @tr-qed{
          by @${\wellFE i : \tint} }
      }
    ]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-S-value-inversion" @elem{@${\langF} static value inversion}]{
  If @${\wellFE v : \tau} then @${\wellFE v}
}@tr-proof{ TODO } @;{
  By induction on the structure of @${v}.

  @tr-case[@${v = i}]{
    @tr-qed{
      by @${\wellKE v}
    }
  }

  @tr-case[@${v = \vpair{v_0}{v_1}}]{
    @tr-step{
      @${\wellKE v_0 : \kany
         @tr-and[]
         \wellKE v_1 : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE v_1}
      @tr-IH
    }
    @tr-qed{
      by (2)
    }
  }

  @tr-case[@${v = \vlam{x}{e}}]{
    @tr-step{
      @${x \wellKE e}
      @|K-S-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${v = \vlam{\tann{x}{\tau}}{e}}]{
    @tr-step{
      @${\tann{x}{\tau} \wellKE e : \kany}
      @|K-S-inversion|
    }
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-D-value-inversion" @elem{@${\langF} dynamic value inversion}]{
  If @${\wellFE v} then @${\wellFE v : \tau}
}@tr-proof{ TODO } @;{
  By induction on the structure of @${v}.

  @tr-case[@${v = i}]{
    @tr-step{
      @${\wellKE v : \kint}
    }
    @tr-qed{
      by @${\kint \subt \kany}
    }
  }

  @tr-case[@${v = \vpair{v_0}{v_1}}]{
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE v_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE v_0 : \kany
         @tr-and[]
         \wellKE v_1 : \kany}
      @tr-IH
    }
    @tr-step{
      @${\wellKE \vpair{v_0}{v_1} : \kpair}
      (2)
    }
    @tr-qed{
      by @${\kpair \subt \kany}
    }
  }

  @tr-case[@${v = \vlam{x}{e}}]{
    @tr-step{
      @${x \wellKE e}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \vlam{x}{e} : \kfun}
      (1)
    }
    @tr-qed{
      by @${\kfun \subt \kany}
    }
  }

  @tr-case[@${v = \vlam{\tann{x}{\tau}}{e}}]{
    @tr-step{
      @${\tann{x}{\tau} \wellFE e : \kany}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \vlam{\tann{x}{\tau}}{e} : \kfun}
      (1)
    }
    @tr-qed{
      by @${\kfun \subt \kany}
    }
  }
}

@tr-lemma[#:key "F-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellFE v} and @${\delta(\vunop, v) = v'} then @${\wellFE v'}
    }
    @item{
      If @${\wellFE v_0} and @${\wellFE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellFE v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellFE v_0}
      @|F-D-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellFE v_1}
      @|F-D-inversion|
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
@tr-lemma[#:key "F-S-subst" @elem{@${\langF} static substitution}]{
  TODO
}@tr-proof{
  TODO
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-D-subst" @elem{@${\langF} dynamic substitution}]{
  TODO
}@tr-proof{
  TODO
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-finite-subtyping" @elem{@${\tau \subt \tau} finite}]{
  All chains @${\tau_0 \subt \cdots \subt \tau_{n-1}} are finite.
}@tr-proof{
  TODO
}

@tr-lemma[#:key "F-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellFE e} then @${x,\Gamma \wellFE e}
    }
    @item{
      If @${\Gamma \wellFE e : \tau} then @${\tann{x}{\tau'},\Gamma \wellFE e : \tau}
    }
  ]
}@tr-proof{
  @; TODO
  @itemize[
    @item{
      @tr-step[
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellFE e
           @tr-or[]
           \Gamma \wellFE e : \tau}
      ]
    }
  ]
}

