#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Forgetful Embedding}

@section{@${\langF} Definitions}
@exact{\input{fig:forgetful-embedding.tex}}

@|clearpage|
@section{@${\langF} Theorems}

@(begin
   (define F-S-soundness @tr-ref[#:key "F-S-soundness"]{static @${\langF}-soundness})
   (define F-D-soundness @tr-ref[#:key "F-S-soundness"]{static @${\langF}-soundness})

   (define F-S-progress @tr-ref[#:key "F-S-progress"]{static progress})
   (define F-D-progress @tr-ref[#:key "F-D-progress"]{dynamic progress})
   (define F-S-preservation @tr-ref[#:key "F-S-preservation"]{static preservation})
   (define F-D-preservation @tr-ref[#:key "F-D-preservation"]{dynamic preservation})

   (define F-S-implies @tr-ref[#:key "F-S-implies"]{static subset})
   (define F-D-implies @tr-ref[#:key "F-D-implies"]{dynamic subset})

   (define F-S-factor @tr-ref[#:key "F-S-factor"]{boundary factoring})
   (define F-D-factor @tr-ref[#:key "F-D-factor"]{boundary factoring})

   (define F-boundary @tr-ref[#:key "F-boundary"]{inner boundary})

   (define F-S-uec @tr-ref[#:key "F-S-uec"]{unique static evaluation contexts})
   (define F-D-uec @tr-ref[#:key "F-D-uec"]{unique dynamic evaluation contexts})

   (define F-S-hole-typing @tr-ref[#:key "F-S-hole-typing"]{static hole typing})
   (define F-D-hole-typing @tr-ref[#:key "F-D-hole-typing"]{dynamic hole typing})

   (define F-boundary-typing @tr-ref[#:key "F-boundary-typing"]{boundary hole typing})
   (define F-DS-hole @tr-ref[#:key "F-DS-hole"]{static @${\vdyn} hole typing})
   (define F-DD-hole @tr-ref[#:key "F-DD-hole"]{dynamic @${\vdyn} hole typing})
   (define F-SS-hole @tr-ref[#:key "F-SS-hole"]{static @${\vsta} hole typing})
   (define F-SD-hole @tr-ref[#:key "F-SD-hole"]{dynamic @${\vsta} hole typing})

   (define F-hole-subst @tr-ref[#:key "F-hole-subst"]{hole substitution})
   (define F-DS-hole-subst @tr-ref[#:key "F-DS-hole-subst"]{dynamic context static hole substitution})
   (define F-DD-hole-subst @tr-ref[#:key "F-DD-hole-subst"]{dynamic context dynamic hole substitution})
   (define F-SS-hole-subst @tr-ref[#:key "F-SS-hole-subst"]{static context static hole substitution})
   (define F-SD-hole-subst @tr-ref[#:key "F-SD-hole-subst"]{static context dynamic hole substitution})

   (define F-S-hole-subst @tr-ref[#:key "F-S-hole-subst"]{static boundary-free hole substitution})
   (define F-D-hole-subst @tr-ref[#:key "F-D-hole-subst"]{dynamic boundary-free hole substitution})

   (define F-S-inversion @tr-ref[#:key "F-S-inversion"]{inversion})
   (define F-D-inversion @tr-ref[#:key "F-D-inversion"]{inversion})

   (define F-S-canonical @tr-ref[#:key "F-S-canonical"]{canonical forms})

   (define F-Delta-soundness @tr-ref[#:key "F-Delta-type-soundness"]{@${\Delta} type soundness})
   (define F-delta-preservation @tr-ref[#:key "F-delta-preservation"]{@${\delta} preservation})

   (define F-fromdyn-soundness @tr-ref[#:key "F-fromdyn-soundness"]{@${\vfromdynF} soundness})
   (define F-fromsta-soundness @tr-ref[#:key "F-fromsta-soundness"]{@${\vfromstaF} soundness})

   (define F-subst @tr-ref[#:key "F-subst"]{substitution})
   (define F-DS-subst @tr-ref[#:key "F-DS-subst"]{dynamic context static value substitution})
   (define F-DD-subst @tr-ref[#:key "F-DD-subst"]{dynamic context dynamic value substitution})
   (define F-SS-subst @tr-ref[#:key "F-SS-subst"]{static context static value substitution})
   (define F-SD-subst @tr-ref[#:key "F-SD-subst"]{static context dynamic value substitution})

   (define F-weakening @tr-ref[#:key "F-weakening"]{weakening})

   (define F-check @tr-ref[#:key "F-check"]{@${\vfromany} soundness})
)

@tr-theorem[#:key "F-soundness" @elem{@${\langF} type soundness}]{
  If @${\wellM e : \tau} then @${\wellFE e : \tau} and one of the following holds:
  @itemlist[
    @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFSstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccFD \tagerror} }
    @item{ @${e \rrFSstar \boundaryerror} }
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

@tr-corollary[#:key "F-pure-static" @elem{@${\langF} static soundness}]{
  If @${\wellM e : \tau} and @${e} is purely static, then one of the following holds:
  @itemlist[
    @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{(sketch)
  Purely-static terms cannot step to a @${\tagerror} and are preserved by the
   @${\ccFS} reduction relation.
}

@|clearpage|
@section{@${\langF} Lemmas}

@tr-lemma[#:key "F-S-implies" @elem{@${\langF} static subset}]{
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
      @${\Gamma \wellFE \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c}} }
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
      @${\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}} }
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
      @${\Gamma \wellFE e_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_d}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \vapp{e_0}{e_1} : \tau_c} }
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
      @${\Gamma \wellFE e_0 : \tau_0}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \eunop{e_0} : \tau} }
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
      @${\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellFE e_1 : \tau_1}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE \ebinop{e_0}{e_1} : \tau} }
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
      @${\Gamma \wellFE e : \tau'}
      @tr-IH]
    @tr-step{
      @${\Gamma \wellFE e : \tau}
      (1)}
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
    @tr-step[
      @${\Gamma \wellFE e}
      @|F-D-implies|]
    @tr-step{
      @${\Gamma \wellFE \edyn{\tau}{e} : \tau}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-D-implies" @elem{@${\langF} dynamic subset}]{
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
      @${\Gamma \wellFE e : \tau}
      @|F-S-implies|}
    @tr-step{
      @${\Gamma \wellFE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-S-progress" @elem{@${\langF} static progress}]{
  If @${\wellFE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccFS e'} }
    @item{ @${e \ccFS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccFD \tagerror} }
  ]
}@tr-proof{
  By the @|F-S-uec| lemma, there are six possible cases.

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-step{
      @${\wellFE \vapp{v_0}{v_1} : \tau'}
      @|F-S-hole-typing|}
    @tr-step{
      @${\wellFE v_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \wellFE v_1 : \tau_d}
      @|F-S-inversion|}
    @tr-step{
      @${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}}}
      @|F-S-canonical|}
    @list[
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}}]{
        @tr-step[
          @${e \ccFS \ctxE{\vsubst{e'}{x}{v_1}}}
          @${\vapp{v_0}{v_1} \rrFS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
                @tr-and[2]
                \mchk{\tau_d'}{v_1} = v_1'}]{
        @tr-step[
          @${e \ccFS \ctxE{\edyn{\tau_c'}{(\vsubst{e'}{x}{v_1'})}}}
          @${\vapp{v_0}{v_1} \rrFS \edyn{\tau_c'}{(\vsubst{e'}{x}{v_1'})}}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
                @tr-and[2]
                \mchk{\tau_d'}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccFS \boundaryerror}
          @${\vapp{v_0}{v_1} \rrFS \boundaryerror}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}}
                @tr-and[2]
                \mchk{\tau_x}{v_1} = v_1'}]{
        @tr-step[
          @${e \ccFS \ctxE{\esta{\tau_c'}{(\echk{\tau_c'}{\vsubst{e'}{x}{v_1'}})}}}
          @${\vapp{v_0}{v_1} \rrFS \esta{\tau_c'}{(\echk{\tau_c'}{\vsubst{e'}{x}{v_1'}})}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e'}}
                  @tr-and[4]
                  \mchk{\tau_x}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccFS \boundaryerror}
          @${\vapp{v_0}{v_1} \rrFS \boundaryerror}]
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
         v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}}
      @|F-S-canonical|]
    @list[
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vfst}]{
        @${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}
        @tr-step{
          @${e \ccFS \ctxE{v_0}}
          @${\eunop{v} \rrFS v_0}}
        @tr-qed[]
      }
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vsnd}]{
        @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}
        @tr-step[
          @${e \ccFS \ctxE{v_1}}
          @${\eunop{v} \rrFS v_1}]
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vfst
                @tr-and[2]
                \mchk{\tau_0'}{v_0} = v_0'}]{
        @tr-step{
          @${e \ccFS \ctxE{v_0'}}
          @${\efst{v} \rrFS v_0'}}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vfst
                @tr-and[2]
                \mchk{\tau_0'}{v_0} = \boundaryerror}]{
        @tr-step{
          @${e \ccFS \boundaryerror}
          @${\efst{v} \rrFS \boundaryerror}}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vsnd
                @tr-and[2]
                \mchk{\tau_1'}{v_1} = v_1'}]{
        @tr-step{
          @${e \ccFS \ctxE{v_1'}}
          @${\esnd{v} \rrFS v_1'}}
        @tr-qed[]
      }
      @tr-else[@${v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}
                  @tr-and[4]
                  \vunop = \vsnd
                  @tr-and[4]
                  \mchk{\tau_1'}{v_1} = \boundaryerror}]{
        @tr-step{
          @${e \ccFS \boundaryerror}
          @${\esnd{v} \rrFS \boundaryerror}}
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
      @elem{@|F-Delta-soundness| (2)}}
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
      @tr-if[@${\mchk{\tau}{e'} = e''}]{
        @tr-step[
          @${e \ccFS \ctxE{e''}}
          @${(\edyn{\tau}{e'}) \rrFS e''}]
        @tr-qed[]
      }
      @tr-else[@${\mchk{\tau}{e'} = \boundaryerror}]{
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

  @tr-case[@${e \eeq \ctxE{\echk{\tau'}{v}}} #:itemize? #false]{
    @tr-if[@${\mchk{\tau}{v} = v'}]{
      @tr-step[
        @${e \ccFS \ctxE{v'}}
        @${(\echk{\tau}{v}) \rrFS v'}]
      @tr-qed[]
    }
    @tr-else[@${\mchk{\tau}{v} = \boundaryerror}]{
      @tr-step[
        @${e \ccFS \boundaryerror}
        @${(\echk{\tau}{v}) \rrFS \boundaryerror}]
      @tr-qed[]
    }
  }

}

@tr-lemma[#:key "F-D-progress" @elem{@${\langF} dynamic progress}]{
  If @${\wellFE e} then one of the following holds:
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
        @${\vapp{v_0}{v_1} \rrFD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})}}]{
      @tr-step{
        @${e \ccFD \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1}
           \rrFD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})}
             @tr-and[2]
             \mchk{\tau_x}{v_1} = v_1'}]{
      @tr-step{
        @${e \ccFD \ctxE{\esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{v_1'}})}}}
        @${\vapp{v_0}{v_1}
           \rrFD \esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{v_1'}})}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})}
             @tr-and[2]
             \mchk{\tau_x}{v_1} = \boundaryerror}]{
      @tr-step[
        @${e \ccFD \boundaryerror}
        @${\vapp{v_0}{v_1} \rrFD \boundaryerror}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_x}}{e'}}]{
      @tr-contradiction{@${\wellFE e}}
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}
                @tr-or[4]
                v_0 \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{v'} }]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${(\vapp{v_0}{v_1}) \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop \eeq \vfst
              @tr-and[2]
              \mchk{\tau_0}{v_0} = v_0'}]{
      @tr-step{
        @${e \ccFD \ctxE{v_0'}}
        @${\eunop{v} \rrFD v_0'}}
      @tr-qed[]
    }
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop \eeq \vfst
              @tr-and[2]
              \mchk{\tau_0}{v_0} = \boundaryerror}]{
      @tr-step{
        @${e \ccFD \boundaryerror}
        @${\eunop{v} \rrFD \boundaryerror}}
      @tr-qed[]
    }
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop \eeq \vsnd
              @tr-and[2]
              \mchk{\tau_1}{v_1} = v_1'}]{
      @tr-step{
        @${e \ccFD \ctxE{v_1'}}
        @${\eunop{v} \rrFD v_1'}}
      @tr-qed[]
    }
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop \eeq \vsnd
              @tr-and[2]
              \mchk{\tau_1}{v_1} = \boundaryerror}]{
      @tr-step{
        @${e \ccFD \boundaryerror}
        @${\eunop{v} \rrFD \boundaryerror}}
      @tr-qed[]
    }
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
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\mchk{\tau'}{e'} = v'}]{
        @tr-step{
          @${e \ccFD \ctxE{v'}}
          @${(\esta{\tau'}{e'}) \rrFD v'}}
        @tr-qed[]
      }
      @tr-else[@${\mchk{\tau'}{e'} = \boundaryerror}]{
        @tr-step{
          @${e \ccFD \boundaryerror}
          @${(\esta{\tau'}{e'}) \rrFD \boundaryerror}}
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccFS A}
        @|F-S-progress|]
      @tr-qed{
        by @${e \ccFD \ctxE{\esta{\tau'}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccFD A} otherwise}
    }
  }
}

@tr-lemma[#:key "F-S-preservation" @elem{@${\langF} static preservation}]{
  If @${\wellFE e : \tau} and @${e \ccFS e'} then @${\wellFE e' : \tau}
}@tr-proof{
  By the @|F-S-uec| lemma there are six cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_x}}{e'}
              @tr-and[2]
              e \ccFS \vsubst{e'}{x}{v_1}}]{
      @tr-step[
        @${\wellFE \vapp{v_0}{v_1} : \tau'}
        @|F-S-hole-typing|]
      @tr-step{
        @${\wellFE v_0 : \tarr{\tau_d}{\tau_c}
           @tr-and[]
           \wellFE v_1 : \tau_d
           @tr-and[]
           \tau_c \subteq \tau'}
        @|F-S-inversion|}
      @tr-step{
        @${\tann{x}{\tau_x} \wellFE e' : \tau_c}
        @|F-S-inversion| (2)}
      @tr-step{
        @${\tau_d \subteq \tau_x}
        @|F-S-canonical| (2)}
      @tr-step{
        @${\wellFE v_1 : \tau_x}
        (2, 4)}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{v_1} : \tau_c}
        @elem{@|F-SS-subst| (3, 5)}}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
    @tr-if[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{\vlam{x}{e'}}
              @tr-and[2]
              e \ccFS \ctxE{\edyn{\tau_c}{(\vsubst{e'}{x}{\mchk{\tau_d}{v_1}})}}}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE v_0 : \tarr{\tau_d'}{\tau_c'}
           @tr-and[]
           \tau_c' \subteq \tau'}
        @|F-S-inversion|}
      @tr-step{
        @${\tarr{\tau_d}{\tau_c} \subteq \tarr{\tau_d'}{\tau_c'}}
        @|F-S-canonical| (2)}
      @tr-step{
        @${\wellFE \vlam{x}{e'}}
        @elem{@|F-S-inversion| (2)}}
      @tr-step{
        @${\tau_d' \subteq \tau_d
           @tr-and[]
           \tau_c \subteq \tau_c'}
        (3)}
      @tr-step{
        @${x \wellFE e'}
        @|F-S-inversion| (4)}
      @tr-step{
        @${\wellFE \mchk{\tau_d}{v_1}}
        @|F-check|}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{\mchk{\tau_d}{v_1}}}
        @elem{@|F-DD-subst| (6, 7)}}
      @tr-step{
        @${\wellFE \edyn{\tau_c}{(\vsubst{e'}{x}{\mchk{\tau_d}{v_1}})} : \tau_c}
        (8)}
      @tr-step{
        @${\wellFE \edyn{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_d}{v_1}}} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
    @tr-else[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{(\vlam{\tann{x}{\tau_x}}{e'})}
                @tr-and[4]
                e \ccFS \ctxE{\esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}})}}}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE v_0 : \tarr{\tau_d'}{\tau_c'}
           @tr-and[]
           \wellFE v_1 : \tau_d'
           @tr-and[]
           \tau_c' \subteq \tau'}
        @|F-S-inversion|}
      @tr-step{
        @${\wellFE \vlam{\tann{x}{\tau_x}}{e'} : \tarr{\tau_x}{\tau_x'}}
        @|F-S-inversion|}
      @tr-step{
        @${\tarr{\tau_d}{\tau_c} \subteq \tarr{\tau_d'}{\tau_c'}}
        @|F-S-canonical| (2)}
      @tr-step{
        @${\tau_c \subteq \tau_c'}
        (4)}
      @tr-step{
        @${\tann{x}{\tau_x} \wellFE e' : \tau_x'}
        @elem{@|F-S-inversion| (3)}}
      @tr-step{
        @${\wellFE \mchk{\tau_x}{v_1} : \tau_x}
        @|F-check|}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{\mchk{\tau_x}{v_1}} : \tau_x'}
        @elem{@|F-SS-subst| (6, 7)}}
      @tr-step{
        @${\wellFE \echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}} : \tau_c}
        (8)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}})} : \tau_c}
        (9)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}})} : \tau'}
        (2, 5, 10)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFS \ctxE{v_0}}]{
      @tr-step{
        @${\wellFE \efst{\vpair{v_0}{v_1}} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_0 \subteq \tau'}
        @elem{@|F-S-inversion|}}
      @tr-step{
        @${\wellFE v_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step{
        @${\wellFE v_0 : \tau'}
        (2)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccFS \ctxE{v_1}}]{
      @tr-step{
        @${\wellFE \esnd{\vpair{v_0}{v_1}} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_1 \subteq \tau'}
        @elem{@|F-S-inversion|}}
      @tr-step{
        @${\wellFE v_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step{
        @${\wellFE v_1 : \tau'}
        (2)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFS \ctxE{\mchk{\tau_0}{v_0}}}]{
      @tr-step{
        @${\wellFE \efst{v} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_0' \subt \tau'}
        @|F-S-inversion| (1)}
      @tr-step{
        @${\tau_0 \subteq \tau_0'}
        @|F-S-canonical| (2)}
      @tr-step{
        @${\wellFE \vpair{v_0}{v_1}
           @tr-or[]
           \wellFE \vpair{v_0}{v_1} : \tau''}
        @|F-S-inversion| (2)}
      @tr-step{
        @${\wellFE v_0
           @tr-or[]
           \wellFE v_0 : \tau'''}
        @|F-S-inversion| (4)}
      @tr-step{
        @${\wellFE \mchk{\tau_0}{v_0} : \tau_0}
        @|F-check| (5)}
      @tr-step{
        @${\wellFE \mchk{\tau_0}{v_0} : \tau'}
        (2, 3, 6)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccFS \ctxE{\mchk{\tau_1}{v_1}}}]{
      @tr-step{
        @${\wellFE \esnd{v} : \tau'}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_1' \subt \tau'}
        @|F-S-inversion| (1)}
      @tr-step{
        @${\tau_1 \subteq \tau_1'}
        @|F-S-canonical| (2)}
      @tr-step{
        @${\wellFE \vpair{v_0}{v_1}
           @tr-or[]
           \wellFE \vpair{v_0}{v_1} : \tau''}
        @|F-S-inversion| (2)}
      @tr-step{
        @${\wellFE v_1
           @tr-or[]
           \wellFE v_1 : \tau'''}
        @|F-S-inversion| (4)}
      @tr-step{
        @${\wellFE \mchk{\tau_1}{v_1} : \tau_1}
        @|F-check| (5)}
      @tr-step{
        @${\wellFE \mchk{\tau_1}{v_1} : \tau'}
        (2, 3, 6)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccFS \ctxE{v}}]{
    @tr-step{
      @${\wellFE \ebinop{v_0}{v_1} : \tau'}
      @|F-S-hole-typing|}
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''
         @tr-and[]
         \tau'' \subteq \tau'}
      @|F-S-inversion|}
    @tr-step{
      @${\wellFE v : \tau''}
      @elem{@|F-Delta-soundness| (2)}}
    @tr-step{
      @${\wellFE v : \tau'}
      (2, 3)}
    @tr-qed{
      by @|F-S-hole-subst| (4)}
  }

  @tr-case[@${e = \ctxE{\edyn{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v
              @tr-and[2]
              e \ccFS \ctxE{\mchk{\tau'}{e'}}}]{
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau''}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|F-S-inversion|}
      @tr-step{
        @${\wellFE \mchk{\tau'}{e'} : \tau'}
        @|F-check| (2)}
      @tr-step{
        @${\wellFE \mchk{\tau'}{e'} : \tau''}
        (2, 3)}
      @tr-qed{
        by @|F-S-hole-subst| (4)}
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccFD e''
                @tr-and[4]
                e \ccFS \ctxE{\edyn{\tau'}{e''}}}]{
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau''}
        @|F-S-hole-typing|}
      @tr-step{
        @${\wellFE e'
           @tr-and[]
           \tau' \subteq \tau''}
        @|F-S-inversion|}
      @tr-step{
        @${\wellFE e''}
        @|F-D-preservation|}
      @tr-step{
        @${\wellFE \edyn{\tau'}{e''} : \tau'}
        (3)}
      @tr-step{
        @${\wellFE \edyn{\tau'}{e''} : \tau''}
        (2, 4)}
      @tr-qed{
        by @|F-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\echk{\tau'}{v}}}]{
    @tr-step{
      @${e \ccFS \ctxE{\mchk{\tau'}{v}}}}
    @tr-step{
      @${\wellFE \echk{\tau'}{e'} : \tau''}
      @|F-S-hole-typing|}
    @tr-step{
      @${\tau' \subt \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\wellFE \mchk{\tau'}{v} : \tau'}
      @|F-check|}
    @tr-step{
      @${\wellFE \mchk{\tau'}{v} : \tau''}
      (2, 3)}
    @tr-qed{
      by @|F-S-hole-subst| (4)}
  }
}

@tr-lemma[#:key "F-D-preservation" @elem{@${\langF} dynamic preservation}]{
  If @${\wellFE e} and @${e \ccFD e'} then @${\wellFE e'}
}@tr-proof{
  By the @|F-D-uec| lemma, there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccFD \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v_0
           @tr-and[]
           \wellFE v_1}
        @|F-D-inversion| (1)}
      @tr-step{
        @${x \wellFE e'}
        @|F-D-inversion| (2)}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{v_1}}
        @|F-DD-subst| (2, 3)}
      @tr-qed{
        @|F-D-hole-subst| (4)}
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x}{e'}}
              @tr-and[2]
              e \ccFD \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v_0
           @tr-and[]
           \wellFE v_1}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE \vlam{x}{e'}}
        @|F-D-inversion| (2)}
      @tr-step{
        @${x \wellFE e'}
        @|F-D-inversion| (3)}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{v_1}}
        @|F-DD-subst| (2, 4)}
      @tr-qed{
        @|F-D-hole-subst| (5)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x}{\tau_x}}{e'}}
              @tr-and[4]
              e \ccFD \ctxE{\esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}})}}}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v_0
           @tr-and[]
           \wellFE v_1}
        @|F-D-inversion|}
      @tr-step{
        @${\wellFE \vlam{\tann{x}{\tau_x}}{e'} : \tarr{\tau_x}{\tau_x'}}
        @|F-D-inversion| (2)}
      @tr-step{
        @${\tann{x}{\tau_x} \wellFE e' : \tau_x'}
        @|F-S-inversion| (3)}
      @tr-step{
        @${\wellFE \mchk{\tau_x}{v_1} : \tau_x}
        @|F-check| (2)}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{\mchk{\tau_x}{v_1}} : \tau_x}
        @|F-SS-subst| (4, 5)}
      @tr-step{
        @${\wellFE \echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}} : \tau_c}
        (6)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{\mchk{\tau_x}{v_1}}})}}
        (7)}
      @tr-qed{
        @|F-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFD \ctxE{v_0}}]{
      @tr-step{
        @${\wellFE \eunop{v}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE v_0}
        @|F-D-inversion| (2)}
      @tr-qed{
        by @|F-D-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccFD \ctxE{v_1}}]{
      @tr-step{
        @${\wellFE \eunop{v}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE v_1}
        @|F-D-inversion| (2)}
      @tr-qed{
        by @|F-D-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFD \ctxE{\mchk{\tau_0}{v_0}}}]{
      @tr-step{
        @${\wellFE \eunop{v}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE v_0
           @tr-or[]
           \wellFE v_0 : \tau_0'}
        @|F-D-inversion| (2)}
      @tr-step{
        @${\wellFE \mchk{\tau_0}{v_0}}
        @|F-check| (3)}
      @tr-qed{
        by @|F-D-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccFD \ctxE{\mchk{\tau_1}{v_1}}}]{
      @tr-step{
        @${\wellFE \eunop{v}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE v_1
           @tr-or[]
           \wellFE v_1 : \tau_1'}
        @|F-D-inversion| (2)}
      @tr-step{
        @${\wellFE \mchk{\tau_1}{v_1}}
        @|F-check| (3)}
      @tr-qed{
        by @|F-D-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccFD \ctxE{v}}]{
    @tr-step{
      @${\wellFE \ebinop{v_0}{v_1}}
      @|F-D-hole-typing|}
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE v_1}
      @|F-D-inversion| (1)}
    @tr-step{
      @${\wellFE v}
      @|F-delta-preservation| (2)}
    @tr-qed{
      by @|F-D-hole-subst| (3)}
  }

  @tr-case[@${e = \ctxE{\esta{\tau'}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v
              @tr-and[2]
              e \ccFD \ctxE{\mchk{\tau'}{e'}}}]{
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE \mchk{\tau'}{e'}}
        @|F-check| (2)}
      @tr-qed{
        @|F-D-hole-subst|}
    }
    @tr-else[@${e' \not\in v
                @tr-and[4]
                e' \ccFS e''
                @tr-and[4]
                e \ccFD \ctxE{\esta{\tau'}{e''}}}]{
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE e'' : \tau'}
        @|F-S-preservation| (2)}
      @tr-step{
        @${\wellFE \esta{\tau'}{e''}}
        (3)}
      @tr-qed{
        by @|F-D-hole-subst|}
    }
  }
}

@tr-lemma[#:key "F-check" @elem{@${\mchk{\cdot}{\cdot}} soundness}]{
  If @${\Gamma \wellFE v \mbox{ or } \Gamma \wellFE v : \tau}
   @linebreak[]
   and @${\mchk{\tau'}{v} = v'},
   @linebreak[]
   then @${\Gamma \wellFE v'} and @${\Gamma \wellFE v' : \tau'}
}@tr-proof{
  By case analysis of the definition of @${\mchk{\cdot}{\cdot}}.

  @tr-case[@${\mchk{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}} #:itemize? #f]{
    @tr-if[@${v = \vlam{x}{e}
              @tr-and[2]
              \Gamma \wellFE v}]{
      @tr-step{
        @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}
        @${\Gamma \wellFE v}}
      @tr-step{
        @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}
        @${\Gamma \wellFE v}}
      @tr-qed[]
    }
    @tr-else[@${v = \vlam{\tann{x}{\tau_x}}{e}
                @tr-and[4]
                \Gamma \wellFE v : \tarr{\tau_d'}{\tau_c'}}]{
      @tr-step{
        @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}
        @${\Gamma \wellFE v : \tarr{\tau_d'}{\tau_c'}}}
      @tr-step{
        @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}
        @${\Gamma \wellFE v : \tarr{\tau_d'}{\tau_c'}}}
      @tr-qed[]
    }
  }

  @tr-case[@${\mchk{\tarr{\tau_d}{\tau_c}}{\vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'}} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}} #:itemize? #f]{
    @tr-if[@${\Gamma \wellFE \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'}} #:itemize? #f]{
      @tr-if[@${v' \eeq \vlam{x}{e'}
                @tr-and[2]
                \Gamma \wellFE v'}]{
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}}
          @${\Gamma \wellFE v'}}
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'} : \tarr{\tau_d}{\tau_c}}
          @${\Gamma \wellFE v'}}
        @tr-qed[]
      }
      @tr-else[@${v' \eeq \vlam{\tann{x}{\tau_x}}{e'}
                  @tr-and[4]
                  \Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}]{
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}}
          @${\Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}}
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'} : \tarr{\tau_d}{\tau_c}}
          @${\Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}}
        @tr-qed[]
      }
    }
    @tr-else[@${\Gamma \wellFE \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'} : \tarr{\tau_d'}{\tau_c'}} #:itemize? #f]{
      @tr-if[@${v' \eeq \vlam{x}{e'}
                @tr-and[2]
                \Gamma \wellFE v'}]{
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}}
          @${\Gamma \wellFE v'}}
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'} : \tarr{\tau_d}{\tau_c}}
          @${\Gamma \wellFE v'}}
        @tr-qed[]
      }
      @tr-else[@${v' \eeq \vlam{\tann{x}{\tau_x}}{e'}
                  @tr-and[4]
                  \Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}]{
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'}}
          @${\Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}}
        @tr-step{
          @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v'} : \tarr{\tau_d}{\tau_c}}
          @${\Gamma \wellFE v' : \tarr{\tau_d''}{\tau_c''}}}
        @tr-qed[]
      }
    }
  }

  @tr-case[@${\mchk{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${\Gamma \wellFE \vpair{v_0}{v_1}}]{
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @${\Gamma \wellFE \vpair{v_0}{v_1}}}
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}} : \tpair{\tau_0}{\tau_1}}
        @${\Gamma \wellFE \vpair{v_0}{v_1}}}
      @tr-qed[]
    }
    @tr-else[@${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0'}{\tau_1'}}]{
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0'}{\tau_1'}}}
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}} : \tpair{\tau_0}{\tau_1}}
        @${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0'}{\tau_1'}}}
      @tr-qed[]
    }
  }

  @tr-case[@${\mchk{\tpair{\tau_0}{\tau_1}}{\vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${\Gamma \wellFE \vpair{v_0}{v_1}}]{
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @${\Gamma \wellFE \vpair{v_0}{v_1}}}
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}} : \tpair{\tau_0}{\tau_1}}
        @${\Gamma \wellFE \vpair{v_0}{v_1}}}
      @tr-qed[]
    }
    @tr-else[@${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0''}{\tau_1''}}]{
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
        @${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0''}{\tau_1''}}}
      @tr-step{
        @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}} : \tpair{\tau_0}{\tau_1}}
        @${\Gamma \wellFE \vpair{v_0}{v_1} : \tpair{\tau_0''}{\tau_1''}}}
      @tr-qed[]
    }
  }

  @tr-case[@${\mchk{\tint}{i} = i}]{
    @tr-step{
      @${\Gamma \wellFE i}}
    @tr-step{
      @${\Gamma \wellFE i : \tint}}
    @tr-qed[]
  }

  @tr-case[@${\mchk{\tnat}{i} = i}]{
    @tr-step{
      @${\Gamma \wellFE i}}
    @tr-step{
      @${\Gamma \wellFE i : \tnat}
      @${i \in \naturals}}
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-S-uec" @elem{@${\langF} unique static evaluation contexts}]{
  If @${\wellFE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ctxE{\vapp{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{e'}}} }
    @item{ @${e = \ctxE{\echk{\tau}{v}}} }
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
        @${\ED = \vpair{\ED_0}{e_1}}
      ]
      @tr-qed{
        @${e = \ED[e_0']}
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
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
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
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
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
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|
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
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
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
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
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

  @tr-case[@${e = \echk{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau'}
        @|F-S-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \echk{\tau'}{\ED_0}}}
      @tr-qed{
        @${e = \ctxE{e_0'}}}
    }
    @tr-else[@${e_0 \in v}]{
      @tr-step{
        @${\ED = \ehole}}
      @tr-qed{
        @${e = \ctxE{\echk{\tau}{e_0}}}}
    }
  }
}

@tr-lemma[#:key "F-D-uec" @elem{@${\langF} unique dynamic evaluation contexts}]{
  If @${\wellFE e} then one of the following holds:
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
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
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
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
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
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
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

  @tr-case[@${\ED = \echk{\tau'}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \echk{\tau'}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellFE \ED_0[e] : \tau_0}
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

  @tr-case[@${\ED = \echk{\tau}{\ED_0}}]{
    @tr-contradiction{@${\wellFE e}}
  }
}

@tr-lemma[#:key "F-S-hole-subst" @elem{@${\langF} static hole substitution}]{
  If @${\wellFE \ctxE{e} : \tau}
   and contains @${\wellFE e : \tau'},
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

  @tr-case[@${\ED = \echk{\tau}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \echk{\tau}{\ED_0[e]}
        @tr-and[]
        \ctxE{e'} = \echk{\tau}{\ED_0[e']}}
    }
    @tr-step{
      @${\wellFE \echk{\tau}{\ED_0[e]} : \tau}
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
      @${\wellFE \echk{\tau}{\ED_0[e']} : \tau}
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
      If @${\Gamma \wellFE \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellFE e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
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
      If @${\Gamma \wellFE \vmonpair{\tpair{\tau_0'}{\tau_1'}}{\vpair{v_0}{v_1}} : \tpair{\tau_0}{\tau_1}}
      then either:
      @itemlist[
        @item{
          @${\Gamma \wellFE \vpair{v_0}{v_1}}
        }
        @item{
          or
          @${\Gamma \wellFE \vpair{v_0}{v_1} : \tau}
        }
      ]
    }
    @item{
      If @${\Gamma \wellFE \vmonfun{\tarr{\tau_d'}{\tau_c'}}{\vlam{x}{e}} : \tarr{\tau_d}{\tau_c}}
      then @${\Gamma \wellFE \vlam{x}{e}}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellFE \vmonfun{\tarr{\tau_d'}{\tau_c'}}{\vlam{\tann{x}{\tau_d''}}{e}} : \tarr{\tau_d}{\tau_c}}
      then @${\Gamma \wellFE \vlam{\tann{x}{\tau_x}}{e} : \tarr{\tau_d''}{\tau_c''}}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellFE \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellFE e'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellFE \echk{\tau}{e'} : \tau}
      then @${\Gamma \wellFE e' : \tau'}
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
      If @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x}{e}}}
      then @${\Gamma \wellFE \vlam{x}{e}}
    }
    @item{
      If @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x}{\tau_x}}{e}}}
      then @${\Gamma \wellFE \vlam{\tann{x}{\tau_x}}{e} : \tarr{\tau_x}{\tau_x'}}
    }
    @item{
      If @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}
      then either:
      @itemlist[
        @item{
          @${\Gamma \wellFE \vpair{v_0}{v_1}}
        }
        @item{
          or @${\Gamma \wellFE \vpair{v_0}{v_1} : \tau'}
        }
      ]
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
      then either:
      @itemlist[
        @item{
          @${v \eeq \vpair{v_0}{v_1}}
        }
        @item{
          or @${v \eeq \vmonpair{\tpair{\tau_0'}{\tau_1'}}{\vpair{v_0}{v_1}}
                @tr-and[]
                \tpair{\tau_0'}{\tau_1'} \subteq \tpair{\tau_0}{\tau_1}}
        }
      ]
    }
    @item{
      If @${\wellFE v : \tarr{\tau_d}{\tau_c}}
      then either:
      @itemlist[
        @item{
          @${v \eeq \vlam{\tann{x}{\tau_x}}{e'}
             @tr-and[]
             \tau_d \subteq \tau_x}
        }
        @item{
          or
          @${v \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{(\vlam{x}{e}}
             @tr-and[]
             \tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
        }
        @item{
          or
          @${v \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{\tann{x}{\tau_x}}{e}}
             @tr-and[]
             \tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
        }
      ]
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
@tr-lemma[#:key "F-Delta-type-soundness" @elem{@${\Delta} type soundness}]{
  If @${\wellFE v_0 : \tau_0 \mbox{ and }
        \wellFE v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then one of the following holds:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellFE v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on the definition of @${\Delta}.

  @tr-case[@${\Delta(\vsum, \tnat, \tnat) = \tnat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|F-S-canonical|
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
      @|F-S-canonical|
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
      @|F-S-canonical|
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
@tr-lemma[#:key "F-SS-subst" @elem{@${\langF} static-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellFE e : \tau}
  and @${\wellFE v : \tau_x}
  then @${\Gamma \wellFE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE x : \tau}}
    @tr-step{
      @${\tau_x \subteq \tau}
      @|F-S-inversion|}
    @tr-step{
      @${\wellFE v : \tau}
      (3)}
    @tr-step{
      @${\Gamma \wellFE v : \tau}
      @|F-weakening|}
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
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellFE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},\tann{x}{\tau_x},\Gamma \wellFE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellFE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x'}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vsubst{(\vlam{x'}{e'})}{x}{v})}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE \vlam{x'}{e'}}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{x'}{e'})}{x}{v}}
      @|F-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vsubst{(\vlam{x'}{e'})}{x}{v})} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x'}{\tau'}}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v} : \tau''}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @list[
      @tr-if[@${\tann{x}{\tau_x},\Gamma \wellFE \vpair{v_0}{v_1}}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v}}
          @|F-DS-subst|}
      }
      @tr-else[@${\tann{x}{\tau_x},\Gamma \wellFE \vpair{v_0}{v_1} : \tau''}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v} : \tau''}
          @tr-IH}
      }
    ]
    @tr-step{
      @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}} : \tau} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0 : \tau_0}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e'}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v}}
      @|F-DS-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \echk{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \echk{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e' : \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \echk{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-SD-subst" @elem{@${\langF} static-dynamic substitution}]{
  If @${x,\Gamma \wellFE e : \tau}
  and @${\wellFE v}
  then @${\Gamma \wellFE \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${x,\Gamma \wellFE x : \tau}}
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
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellFE e : \tau}}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}}
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellFE e' : \tau_c'
         @tr-and[]
         \tarr{\tau'}{\tau_c'} \subteq \tau}}
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellFE \vsubst{e'}{x}{v} : \tau_c'}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau}}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x'}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellFE \vlam{x'}{e'}}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{x'}{e'})}{x}{v}}
      @|F-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x'}{\tau'}}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v} : \tau''}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @list[
      @tr-if[@${x,\Gamma \wellFE \vpair{v_0}{v_1}}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v}}
          @|F-DD-subst|}
      }
      @tr-else[@${x,\Gamma \wellFE \vpair{v_0}{v_1} : \tau''}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v} : \tau''}
          @tr-IH}
      }
    ]
    @tr-step{
      @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}} : \tau} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0 : \tau_0}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \eunop{\vsubst{e_0}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0 : \tau_0
         @tr-and[]
         x,\Gamma \wellFE e_1 : \tau_1}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v} : \tau_0
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v} : \tau_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e'}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v}}
      @|F-DD-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \edyn{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \echk{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \echk{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e' : \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \echk{\tau'}{\vsubst{e'}{x}{v}} : \tau}
      (3)}
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-DS-subst" @elem{@${\langF} dynamic-static substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellFE e}
  and @${\wellFE v : \tau_x}
  then @${\Gamma \wellFE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellFE x}}
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
      @${x',\tann{x}{\tau_x},\Gamma \wellFE e'}
      @|F-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellFE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${\tann{x}{\tau_x},\Gamma \wellFE e}}
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x'}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE \vlam{x'}{e'}}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{x'}{e'})}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x'}{\tau'}}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}} }
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau''}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v} : \tau''}
      @|F-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @list[
      @tr-if[@${\tann{x}{\tau_x},\Gamma \wellFE \vpair{v_0}{v_1}}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v}}
          @tr-IH}
      }
      @tr-else[@${\tann{x}{\tau_x},\Gamma \wellFE \vpair{v_0}{v_1} : \tau''}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v} : \tau''}
          @|F-SS-subst|}
      }
    ]
    @tr-step{
      @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e_0
         @tr-and[]
         \tann{x}{\tau_x},\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${\tann{x}{\tau_x},\Gamma \wellFE e' : \tau'}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v} : \tau'}
      @|F-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-DD-subst" @elem{@${\langF} dynamic-dynamic substitution}]{
  If @${x,\Gamma \wellFE e}
  and @${\wellFE v}
  then @${\Gamma \wellFE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}}
    @tr-step{
      @${\Gamma \wellFE v}
      @|F-weakening|}
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
      @${x',x,\Gamma \wellFE e'}
      @|F-D-inversion|}
    @tr-step{
      @${x',\Gamma \wellFE \vsubst{e'}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vlam{x'}{(\vsubst{e'}{x}{v})}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-contradiction{@${x,\Gamma \wellFE e}}
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x'}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellFE \vlam{x'}{e'}}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{x'}{e'})}{x}{v}}
      @tr-IH (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{x'}{e'})}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x'}{\tau'}}{e'}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}} }
    @tr-step{
      @${x,\Gamma \wellFE \vlam{\tann{x'}{\tau'}}{e'} : \tau''}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v} : \tau''}
      @|F-SD-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vsubst{(\vlam{\tann{x'}{\tau'}}{e'})}{x}{v}}}
      (3)}
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0
         @tr-and[]
         x,\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @list[
      @tr-if[@${x,\Gamma \wellFE \vpair{v_0}{v_1}}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v}}
          @tr-IH}
      }
      @tr-else[@${x,\Gamma \wellFE \vpair{v_0}{v_1} : \tau''}]{
        @tr-step{
          @${\Gamma \wellFE \vsubst{\vpair{v_0}{v_1}}{x}{v} : \tau''}
          @|F-SD-subst|}
      }
    ]
    @tr-step{
      @${\Gamma \wellFE \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vsubst{\vpair{v_0}{v_1}}{x}{v}}} }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0
         @tr-and[]
         x,\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e_0
         @tr-and[]
         x,\Gamma \wellFE e_1}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellFE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellFE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}}
    @tr-step{
      @${x,\Gamma \wellFE e' : \tau'}
      @|F-D-inversion|}
    @tr-step{
      @${\Gamma \wellFE \vsubst{e'}{x}{v} : \tau'}
      @|F-SS-subst| (2)}
    @tr-step{
      @${\Gamma \wellFE \esta{\tau'}{\vsubst{e'}{x}{v}}}
      (3)}
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
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

