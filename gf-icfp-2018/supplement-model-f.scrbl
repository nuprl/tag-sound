#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{(@${\langF}) Forgetful Embedding}

@section{@|FHlong| Definitions}
@exact{\input{fig:forgetful-embedding.tex}}

@|clearpage|
@section{@|FHlong| Theorems}

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

@tr-theorem[#:key "F-S-soundness" @elem{static @${\langF}-soundness}]{
  If @${\wellM e : \tau} then @${\wellFE e : \tau} and one of the following holds:
  @itemlist[
    @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFSstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \rrFD \tagerror} }
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

@tr-theorem[#:key "F-D-soundness" @elem{dynamic @${\langF}-soundness}]{
    If @${\wellM e} then @${\wellFE e} and one of the following holds:
    @itemlist[
      @item{ @${e \rrFDstar v \mbox{ and } \wellFE v} }
      @item{ @${e \rrFDstar \ctxE{e'}} and @${e' \rrFD \tagerror} }
      @item{ @${e \rrFDstar \boundaryerror} }
      @item{ @${e} diverges}
    ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellFE e}
      @|F-D-implies|
    }}
    @item{@tr-qed{
      by @|F-D-progress| and @|F-D-preservation|.
    }}
  ]
}

@tr-corollary[#:key "F-pure-static" @elem{@${\langF} static soundness}]{
  If @${\wellM e : \tau} and @${e} is boundary-free, then one of the following holds:
  @itemlist[
    @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  Consequence of the proof for @|F-S-soundness|
}


@|clearpage|
@section{@|FHlong| Lemmas}

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

@tr-corollary[#:key "F-fromdyn-soundness" @elem{@${\vfromdynF} soundness}]{
  If @${\wellFE v} then @${\wellFE \efromdynF{\tau}{v} : \tau}
}@tr-proof{
  @tr-qed{by @|F-check|}
}

@tr-corollary[#:key "F-fromsta-soundness" @elem{@${\vfromstaF} soundness}]{
  If @${\wellFE v : \tau} then @${\wellFE \efromstaF{\tau}{v}}
}@tr-proof{
  @tr-qed{by @|F-check|}
}

@tr-corollary[#:key "F-S-implies" @elem{@${\langF} static subset}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellFE e : \tau}.
}@tr-proof{
  Consequence of the proof for the @|holong| @tr-ref[#:key "N-S-implies"]{static subset} lemma; both
   @${\wellFE} and @${\wellNE} have the same typing rules for surface-language
   expressions.
}

@tr-corollary[#:key "F-D-implies" @elem{@${\langF} dynamic subset}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellFE e}.
}@tr-proof{
  Consequence of the proof for the @|holong| @tr-ref[#:key "N-D-implies"]{dynamic subset} lemma.
}

@tr-lemma[#:key "F-S-progress" @elem{@${\langF} static progress}]{
  If @${\wellFE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccFS e'} }
    @item{ @${e \ccFS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccFD \tagerror} }
  ]
}@tr-proof{
  By the @|F-S-factor| lemma, there are eight possible cases.

  @tr-case[@elem{@${e} is a value}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\wellFE \eapp{v_0}{v_1} : \tau'}
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
          @${e \ccFS \ebase[{\vsubst{e'}{x}{v_1}}]}
          @${\vapp{v_0}{v_1} \rrFS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\vlam{x}{e'}}
                @tr-and[2]
                \mchk{\tau_d'}{v_1} = v_1'}]{
        @tr-step[
          @${e \ccFS \ebase[{\edyn{\tau_c'}{(\vsubst{e'}{x}{v_1'})}}]}
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
          @${e \ccFS \ebase[{\esta{\tau_c'}{(\echk{\tau_c'}{\vsubst{e'}{x}{v_1'}})}}]}
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

  @tr-case[@${e = \ebase[{\eunop{v}}]}]{
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
          @${e \ccFS \ebase[{v_0}]}
          @${\eunop{v} \rrFS v_0}}
        @tr-qed[]
      }
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vsnd}]{
        @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}
        @tr-step[
          @${e \ccFS \ebase[{v_1}]}
          @${\eunop{v} \rrFS v_1}]
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{\vpair{v_0}{v_1}}
                @tr-and[2]
                \vunop = \vfst
                @tr-and[2]
                \mchk{\tau_0'}{v_0} = v_0'}]{
        @tr-step{
          @${e \ccFS \ebase[{v_0'}]}
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
          @${e \ccFS \ebase[{v_1'}]}
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

  @tr-case[@${e \eeq \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${\wellFE \ebinop{v_0}{v_1} : \tau'}
      @|F-S-hole-typing|}
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|F-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = e'}
      @elem{@|F-Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrFS e'}
      (3)}
    @tr-qed{
      by @${e \ccFS \ebase[e']}
    }
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccFD e''
         @tr-or[]
         e' \ccFD \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrFD \tagerror
      }
      @|F-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccFS \ctxE{\efromdynF{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccFS e'}
        }
      }
      @tr-if[@${e' \ccFD e''}]{
        @tr-qed{
          @${e \ccFS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccFD \boundaryerror}]{
        @tr-qed{
          @${e \ccFS \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrFD \tagerror}]{
        @tr-step{
          @${\esd' \in \ebase}
          @elem{@${e'} is boundary-free}
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccFS e''
         @tr-or[]
         e' \ccFS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrFD \tagerror}
      @|F-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccFS \ctxE{\efromstaF{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccFS e'}
        }
      }
      @tr-if[@${e' \ccFS e''}]{
        @tr-qed{
          @${e \ccFS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccFS \boundaryerror}]{
        @tr-qed{
          @${e \ccFS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e'\!\eeq\!\esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrFD\!\tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\eerr}}]{
    @tr-qed[@${e \ccFS \eerr}]
  }

  @tr-case[@${e \eeq \ebase[{\echk{\tau'}{v}}]} #:itemize? #false]{
    @tr-if[@${\mchk{\tau}{v} = v'}]{
      @tr-step[
        @${e \ccFS \ebase[{v'}]}
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
    @item{ @${e \in \eerr} }
    @item{ @${e \ccFD e'} }
    @item{ @${e \ccFD \boundaryerror} }
    @item{ @${e \ccFD \tagerror} }
  ]
}@tr-proof{
  By the @|F-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[{\vapp{v_0}{v_1}}]} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccFD \ebase[{\vsubst{e'}{x}{v_1}}]}
        @${\vapp{v_0}{v_1} \rrFD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{x}{e'})}}]{
      @tr-step{
        @${e \ccFD \ebase[{\vsubst{e'}{x}{v_1}}]}
        @${\vapp{v_0}{v_1}
           \rrFD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau_x}}{e'})}
             @tr-and[2]
             \mchk{\tau_x}{v_1} = v_1'}]{
      @tr-step{
        @${e \ccFD \ebase[{\esta{\tau_c}{(\echk{\tau_c}{\vsubst{e'}{x}{v_1'}})}}]}
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

  @tr-case[@${e = \ebase[\eunop{v}]} #:itemize? #f]{
    @tr-if[@${v \eeq \vmonpair{\tpair{\tau_0}{\tau_1}}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop \eeq \vfst
              @tr-and[2]
              \mchk{\tau_0}{v_0} = v_0'}]{
      @tr-step{
        @${e \ccFD \ebase[{v_0'}]}
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
        @${e \ccFD \ebase[{v_1'}]}
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
    @tr-if[@${\delta(\vunop, v) = e'}]{
      @tr-step{
        @${(\eunop{v}) \rrFD e'}}
      @tr-qed{
        by @${e \ccFD \ebase[e']}}
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${(\eunop{v}) \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrFD e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccFD \tagerror}
        @${\ebinop{v_0}{v_1} \rrFD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@elem{@${e = \esd[{\edyn{\tau'}{e'}}]} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccFD e''
         @tr-or[]
         e' \ccFD \boundaryerror
         @tr-or[]
         e' \eeq \ebase[{e''}] \mbox{ and } e'' \rrFD \tagerror}
      @|F-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccFD \ctxE{\efromdynF{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccFD e'}
        }
      }
      @tr-if[@${e' \ccFD e''}]{
        @tr-qed{
          @${e \ccFS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccFD \boundaryerror}]{
        @tr-qed{
          @${e \ccFD \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \ctxE{e''} \mbox{ and } e'' \rrFD \tagerror}]{
        @tr-step{
          @${\esd \in \ebase}
          @${e'} is boundary-free
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e = \esd[{\esta{\tau'}{e'}}]} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccFS e''
         @tr-or[]
         e' \ccFS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrFD \tagerror}
      @|F-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccFS \ctxE{\efromstaF{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccFS e'}
        }
      }
      @tr-if[@${e' \ccFS e''}]{
        @tr-qed{
          @${e \ccFS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccFS \boundaryerror}]{
        @tr-qed{
          @${e \ccFS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e'\!\eeq\!\esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrFD\!\tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e = \esd[\eerr]}]{
    @tr-qed{
      @${e \ccFD \eerr}
    }
  }
}


@tr-lemma[#:key "F-S-preservation" @elem{@${\langF} static preservation}]{
  If @${\wellFE e : \tau} and @${e \ccFS e'} then @${\wellFE e' : \tau}
}@tr-proof{
  By the @|F-S-factor| lemma there are eight cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccFS e'}}
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
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
        @elem{@|F-subst| (3, 5)}}
      @tr-step{
        @${\wellFE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|F-hole-subst|}
    }
    @tr-if[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{\vlam{x}{e'}}
              @tr-and[2]
              e \ccFS \ebase[{\edyn{\tau_c}{(\eapp{(\vlam{x}{e'})}{(\efromany{\tau_d}{v_1}})}}]}]{
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
        @${\wellFE \mchk{\tau_d}{v_1}}
        @|F-check|}
      @tr-step{
        @${\wellFE \eapp{(\vlam{x}{e'})}{\mchk{\tau_d}{v_1}}}
        @elem{(4, 6)}}
      @tr-step{
        @${\wellFE \edyn{\tau_c}{(\eapp{(\vlam{x}{e'})}{\mchk{\tau_d}{v_1}})} : \tau_c}
        (7)}
      @tr-step{
        @${\wellFE \edyn{\tau_c}{(\eapp{(\vlam{x}{e'})}{\mchk{\tau_d}{v_1}})} : \tau'}
        (2, 5, 8)}
      @tr-qed{
        by @|F-hole-subst|}
    }
    @tr-else[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{(\vlam{\tann{x}{\tau_x}}{e'})}
                @tr-and[4]
                e \ccFS \ebase[{\esta{\tau_c}{(\echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})})}}]}]{
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
        @${\wellFE \mchk{\tau_x}{v_1} : \tau_x}
        @|F-check|}
      @tr-step{
        @${\wellFE \eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}} : \tau_x'}
        @elem{(3, 6)}}
      @tr-step{
        @${\wellFE \echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})} : \tau_c}
        (7)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})})} : \tau_c}
        (8)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})})} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|F-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFS \ebase[{v_0}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccFS \ebase[{v_1}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFS \ebase[{\mchk{\tau_0}{v_0}}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccFS \ebase[{\mchk{\tau_1}{v_1}}]}]{
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
        by @|F-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccFS \ebase[{v}]}]{
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
      by @|F-hole-subst| (4)}
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccFS \ctxE{\efromdynF{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau'}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e'}
        @|F-S-inversion| (2)
      }
      @tr-step{
        @${\wellFE \efromdynF{\tau'}{e'} : \tau'}
        @|F-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|F-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccFD e''}]{
      @tr-step{
        @${e \ccFS \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau'}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e'}
        @|F-S-inversion| (2)
      }
      @tr-step{
        @${\wellFE e''}
        @|F-D-preservation| (3)
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|F-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccFS \ctxE{\efromstaF{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (2)
      }
      @tr-step{
        @${\wellFE \efromstaF{\tau'}{e'}}
        @|F-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|F-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccFS e''}]{
      @tr-step{
        @${e \ccFS \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (2)
      }
      @tr-step{
        @${\wellFE e'' : \tau'}
        @|F-S-preservation| (3)
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|F-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[\eerr]}}]{
    @tr-step{
      @${e \ccFS \eerr}
    }
    @tr-qed{
      by @${\wellFE \eerr : \tau}
    }
  }

  @tr-case[@${e = \ebase[{\echk{\tau}{v}}]}]{
    @tr-step{
      @${\wellFE \echk{\tau}{v} : \tau}
      @|F-S-hole-typing|}
    @tr-step{
      @${\wellFE v : \tau'}
      @|F-S-inversion| (1)}
    @tr-step{
      @${\wellFE \efromany{\tau}{v'} : \tau}
      @|F-check| (2)
    }
    @tr-qed{
      by @|F-hole-subst| (3)
    }
  }
}

@tr-lemma[#:key "F-D-preservation" @elem{@${\langF} dynamic preservation}]{
  If @${\wellFE e} and @${e \ccFD e'} then @${\wellFE e'}
}@tr-proof{
  By the @|F-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccFD e'}}
  }

  @tr-case[@${e = \ebase[{\vapp{v_0}{v_1}}]} #:itemize? #f]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccFD \ebase[{\vsubst{e'}{x}{v_1}}]}]{
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
        @|F-subst| (2, 3)}
      @tr-qed{
        @|F-hole-subst| (4)}
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{x}{e'}}
              @tr-and[2]
              e \ccFD \ebase[{\eapp{(\vlam{x}{e'})}{v_1}}]}]{
      @tr-step{
        @${\wellFE \vapp{v_0}{v_1}}
        @|F-D-hole-typing|}
      @tr-step{
        @${\wellFE v_0
           @tr-and[]
           \wellFE v_1}
        @|F-D-inversion| (1)}
      @tr-step{
        @${\wellFE \eapp{(\vlam{x}{e'})}{v_1}}
        (2)}
      @tr-qed{
        @|F-hole-subst| (5)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{\vlam{\tann{x}{\tau_x}}{e'}}
              @tr-and[4]
              e \ccFD \ebase[{\esta{\tau_c}{(\echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})})}}]}]{
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
        @${\wellFE \mchk{\tau_x}{v_1} : \tau_x}
        @|F-check| (2)}
      @tr-step{
        @${\wellFE (\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}}) : \tau_x'}
        (3, 4)}
      @tr-step{
        @${\wellFE \echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})} : \tau_c}
        (5)}
      @tr-step{
        @${\wellFE \esta{\tau_c}{(\echk{\tau_c}{(\eapp{(\vlam{\tann{x}{\tau_x}}{e'})}{\mchk{\tau_x}{v_1}})})}}
        (6)}
      @tr-qed{
        @|F-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #f]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFD \ebase[{v_0}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vsnd
              @tr-and[2]
              e \ccFD \ebase[{v_1}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccFD \ebase[{\mchk{\tau_0}{v_0}}]}]{
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
        by @|F-hole-subst|}
    }
    @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccFD \ebase[{\mchk{\tau_1}{v_1}}]}]{
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
        by @|F-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccFD \ebase[{v}]}]{
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
      by @|F-hole-subst| (3)}
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccFD \ctxE{\efromdynF{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau'}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e'}
        @|F-S-inversion| (2)
      }
      @tr-step{
        @${\wellFE \efromdynF{\tau'}{e'} : \tau'}
        @|F-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|F-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccFD e''}]{
      @tr-step{
        @${e \ccFD \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e'} : \tau'}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e' 
           @tr-and[]
           \tau' \subteq \tau''}
        @|F-S-inversion| (2)
      }
      @tr-step{
        @${\wellFE e''}
        @|F-D-preservation| (3)
      }
      @tr-step{
        @${\wellFE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|F-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccFD \ctxE{\efromstaF{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (2)
      }
      @tr-step{
        @${\wellFE \efromstaF{\tau'}{e'}}
        @|F-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|F-hole-subst| (5)
      }
    }
    @tr-else[@${e' \ccFS e''}]{
      @tr-step{
        @${e \ccFD \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e'}}
        @|F-boundary-typing|
      }
      @tr-step{
        @${\wellFE e' : \tau'}
        @|F-D-inversion| (2)
      }
      @tr-step{
        @${\wellFE e'' : \tau'}
        @|F-S-preservation| (3)
      }
      @tr-step{
        @${\wellFE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|F-hole-subst| (5)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccFD \eerr}}
    @tr-qed{
      @${\wellFE \eerr}
    }
  }

}

@tr-lemma[#:key "F-S-factor" @elem{@${\langF} static boundary factoring}]{
  If @${\wellFE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ebase[\eapp{v_0}{v_1}]} }
    @item{ @${e = \ebase[\eunop{v}]} }
    @item{ @${e = \ebase[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \ebase[\echk{\tau}{v}]} }
    @item{ @${e = \esd[\edyn{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\esta{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\eerr]} }
  ]
}@tr-proof{
  By the @|F-S-uec| lemma, there are eight cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \esd[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eapp{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\eapp{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\eapp{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\eunop{v}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eunop{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\eunop{v}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\eunop{v}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\ebinop{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\ebinop{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\echk{\tau}{v}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\echk{\tau}{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-contradiction{ @${\wellFE e : \tau} }
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\echk{\tau}{v}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\edyn{\tau}{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\esta{\tau}{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\eerr]}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-S-uec" @elem{@${\langF} unique static evaluation contexts}]{
  If @${\wellFE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \esd[\eapp{v_0}{v_1}]} }
    @item{ @${e = \esd[\eunop{v}]} }
    @item{ @${e = \esd[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \esd[\echk{\tau}{v}]} }
    @item{ @${e = \esd[\edyn{\tau}{v}]} }
    @item{ @${e = \esd[\esta{\tau}{v}]} }
    @item{ @${e = \esd[\eerr]} }
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
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH (1)
      }
      @tr-step{
        @${\ED = \vpair{\ED_0}{e_1}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \vpair{e_0}{\ED_1}}
      }
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

  @tr-case[@${e = \eapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \eapp{\ED_0}{e_1}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \eapp{e_0}{\ED_1}}
      }
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\eapp{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|
      }
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
      @tr-step{
        @${\ED = \ebinop{\ED_0}{e_1}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1 : \tau_1}
        @|F-S-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \ebinop{e_0}{\ED_1}}
      }
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

  @tr-case[@${e = \echk{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0 : \tau_0}
        @|F-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}
      }
      @tr-step{
        @${\ED = \echk{\tau}{\ED_0}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\echk{\tau}{e_0}}}
      }
    }
  }

  @tr-case[@${e = \edyn{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|F-D-uec| (1)
      }
      @tr-step{
        @${\ED = \edyn{\tau}{\ED_0}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e = \ED[\edyn{\tau}{e_0}]}
      }
    }
  }

  @tr-case[@${e = \eerr}]{
    @tr-step{
      @${\esd = \ehole}
    }
    @tr-qed[@${e = \esd[\eerr]}]
  }

}

@tr-lemma[#:key "F-boundary" @elem{@${\langF} inner boundary}]{
  For all contexts @${\esd}, one of the following holds:
  @itemlist[
  @item{@${\esd = \ebase}}
  @item{@${\esd = \esd'[\edyn{\tau}{\ebase}]}}
  @item{@${\esd = \esd'[\esta{\tau}{\ebase}]}}
  ]
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd = \ebase}]{
    @tr-qed[]
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd_1 = \ebase
         @tr-or[]
         \esd_1 = \esd_1'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_1 = \esd_1'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_1 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_1 = \esd_1'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd_1 = \ebase
         @tr-or[]
         \esd_1 = \esd_1'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_1 = \esd_1'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_1 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_1 = \esd_1'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eunop{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \eunop{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd_1 = \ebase
         @tr-or[]
         \esd_1 = \esd_1'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_1 = \esd_1'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_1 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_1 = \esd_1'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \echk{\tau}{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \edyn{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau'}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \edyn{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau'}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \esta{\tau}{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \esta{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau'}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \esta{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau'}{\ebase}]}
        ]
      }
    ]
  }

}

@tr-lemma[#:key "F-D-factor" @elem{@${\langF} dynamic boundary factoring}]{
  If @${\wellFE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ebase[\eapp{v_0}{v_1}]} }
    @item{ @${e = \ebase[\eunop{v}]} }
    @item{ @${e = \ebase[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \esd[\edyn{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\esta{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\eerr]} }
  ]
}@tr-proof{
  By the @|F-D-uec| lemma, there are eight cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \esd[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eapp{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\eapp{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\eapp{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\eunop{v}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eunop{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\eunop{v}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\eunop{v}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\ebinop{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\ebinop{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\echk{\tau'}{v}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|F-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-contradiction{ @${\wellFE e} }
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-contradiction{ @${\wellFE e} }
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\echk{\tau'}{v}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\edyn{\tau}{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\esta{\tau}{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\eerr]}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "F-D-uec" @elem{@${\langF} unique dynamic evaluation contexts}]{
  If @${\wellFE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \esd[\eapp{v_0}{v_1}]} }
    @item{ @${e = \esd[\eunop{v}]} }
    @item{ @${e = \esd[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \esd[\echk{\tau}{v}]} }
    @item{ @${e = \esd[\edyn{\tau}{v}]} }
    @item{ @${e = \esd[\esta{\tau}{v}]} }
    @item{ @${e = \esd[\eerr]} }
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
              e = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} }]{
    @tr-qed{
      @${e} is a value
    }
  }

  @tr-case[@${e = \eerr}]{
    @tr-step{@${\esd = \ehole}}
    @tr-qed[@${e = \esd[\eerr]}]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-D-inversion|}
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
      @tr-step{
        @${\wellFE e_1}
        @|F-D-inversion|}
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
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e} is a value
      }
    }
  }

  @tr-case[@${e = \eapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-D-inversion|}
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @elem{@tr-IH (1)}}
      @tr-step{
        @${\ED = \eapp{\ED_0}{e_1}}}
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-if[@${e_0 \in v @tr-and[2] e_1 \not\in v}]{
      @tr-step{
        @${\wellFE e_1}
        @|F-D-inversion|}
      @tr-step{
        @${e_1 = \ED_1[e_1']}
        @tr-IH (1)}
      @tr-step{
        @${\ED = \eapp{e_0}{\ED_1}}}
      @tr-qed{
        @${e = \ED[e_1']}
      }
    }
    @tr-else[@${e_0 \in v @tr-and[4] e_1 \in v}]{
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e = \ctxE{\eapp{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-D-inversion|}
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
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e = \ctxE{\eunop{e_0}}}
      }
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-D-inversion|}
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
      @tr-step{
        @${\wellFE e_1}
        @|F-D-inversion|}
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
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e = \ctxE{\ebinop{e_0}{e_1}}}
      }
    }
  }

  @tr-case[@${e = \echk{\tau}{e_0}} #:itemize? #f]{
    @tr-contradiction{@${\wellFE e}}
  }

  @tr-case[@${e = \esta{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellFE e_0}
        @|F-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|F-S-uec| (1)
      }
      @tr-step{
        @${\ED = \esta{\tau}{\ED_0}}
      }
      @tr-qed{
        @${e = \ED[e_0']}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @tr-step{
        @${\ED = \ehole}
      }
      @tr-qed{
        @${e = \ED[\esta{\tau}{e_0}]}
      }
    }
  }
}

@tr-lemma[#:key "F-S-hole-typing" @elem{@${\langF} static hole typing}]{
  If @${\wellFE \ebase[{e}] : \tau} then the derivation
   contains a sub-term @${\wellFE e : \tau'}
}@tr-proof{
  By induction on the structure of @${\ebase}.

  @tr-case[@${\ebase = \ehole}]{
    @tr-qed{
      @${\ebase[{e}] = e}
    }
  }

  @tr-case[@${\ebase = \eapp{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \eapp{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tarr{\tau_d}{\tau_c}}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eapp{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \eapp{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e] : \tau_d}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \echk{\tau}{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \echk{\tau}{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

}

@tr-lemma[#:key "F-D-hole-typing" @elem{@${\langF} dynamic hole typing}]{
  If @${\wellFE \ebase[{e}]} then the derivation contains a sub-term @${\wellFE e}
}@tr-proof{
  By induction on the structure of @${\ebase}.

  @tr-case[@${\ebase = \ehole}]{
    @tr-qed{
      @${\ebase[{e}] = e}
    }
  }

  @tr-case[@${\ebase = \eapp{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \eapp{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eapp{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \eapp{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "F-boundary-typing" @elem{@${\langF} boundary hole typing}]{
  @itemlist[
  @item{
    If @${\wellFE \ctxE{\edyn{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellFE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellFE \ctxE{\edyn{\tau}{e}}} then the derivation contains a
    sub-term @${\wellFE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellFE \ctxE{\esta{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellFE \esta{\tau}{e}}
  }
  @item{
    If @${\wellFE \ctxE{\esta{\tau}{e}}} then the derivation contains a
    sub-term @${\wellFE \esta{\tau}{e}}
  }
  ]
}@tr-proof{
  By the following four lemmas: @|F-DS-hole|, @|F-DD-hole|, @|F-SS-hole|, and @|F-SD-hole|.
}

@tr-lemma[#:key "F-DS-hole" @elem{@${\langF} static @${\vdyn} hole typing}]{
  If @${\wellFE \ctxE{\edyn{\tau}{e}} : \tau'} then the derivation contains
   a sub-term @${\wellFE \edyn{\tau}{e} : \tau}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-step{
      @${\wellFE \edyn{\tau}{e} : \tau''}
      @|F-S-hole-typing|
    }
    @tr-step{
      @${\wellFE \edyn{\tau}{e} : \tau}
      @|F-S-inversion| (1)
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \vpair{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \vpair{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eunop{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \ebinop{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \ebinop{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \echk{\tau''}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \edyn{\tau_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}]}
      @|F-S-inversion|
    }
    @tr-qed{
      by @|F-DD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{\edyn{\tau}{e}} : \tau'}
    }
  }
}

@tr-lemma[#:key "F-DD-hole" @elem{@${\langF} dynamic @${\vdyn} hole typing}]{
  If @${\wellFE \ctxE{\edyn{\tau}{e}}} then the derivation contains
   a sub-term @${\wellFE \edyn{\tau}{e} : \tau}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellFE \ctxE{\edyn{\tau}{e}}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \vpair{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \vpair{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eunop{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \ebinop{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \ebinop{v_0}{\esd_1[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\edyn{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-contradiction{ @${\wellFE \ctxE{\edyn{\tau}{e}}}} }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{\edyn{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \esta{\tau_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|F-D-inversion|
    }
    @tr-qed{
      by @|F-DS-hole| (2)
    }
  }
}

@tr-lemma[#:key "F-SS-hole" @elem{@${\langF} static @${\vsta} hole typing}]{
  If @${\wellFE \ctxE{\esta{\tau}{e}} : \tau'} then the derivation contains
   a sub-term @${\wellFE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellFE \ctxE{\esta{\tau}{e}} : \tau'} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \vpair{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \vpair{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eunop{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \ebinop{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \ebinop{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \echk{\tau''}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \edyn{\tau_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}]}
      @|F-S-inversion|
    }
    @tr-qed{
      by @|F-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{\esta{\tau}{e}} : \tau'}
    }
  }
}

@tr-lemma[#:key "F-SD-hole" @elem{@${\langF} dynamic @${\vsta} hole typing}]{
  If @${\wellFE \ctxE{\esta{\tau}{e}}} then the derivation contains
   a sub-term @${\wellFE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{
      by @|F-D-hole-typing|
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \vpair{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \vpair{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eunop{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \ebinop{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \ebinop{v_0}{\esd_1[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_1[{\esta{\tau}{e}}]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{\esta{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{\esta{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \esta{\tau_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellFE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|F-D-inversion|
    }
    @tr-qed{
      by @|F-SS-hole| (2)
    }
  }
}

@tr-lemma[#:key "F-S-hole-subst" @elem{@${\langF} static boundary-free hole substitution}]{
  If @${\wellFE \ebase[e] : \tau}
   and the derivation contains a sub-term @${\wellFE e : \tau'}
   and @${\wellFE e' : \tau'}
   then @${\wellFE \ebase[e'] : \tau}.
}@tr-proof{
  By induction on the structure of @${\ebase}

  @tr-case[@${\ebase = \ehole}]{
    @tr-step{
      @${\ebase[{e}] = e
         @tr-and[]
         \ebase[{e'}] = e'}
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

  @tr-case[@${\ebase = \ebase_0~e_1}]{
    @tr-step{
      @${\ebase[{e}] = \ebase_0[e]~e_1
        @tr-and[]
        \ebase[{e'}] = \ebase_0[e']~e_1}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]~e_1 : \tau}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebase_0[e']~e_1 : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = v_0~\ebase_1}]{
    @tr-step{
      @${\ebase[{e}] = v_0~\ebase_1[e]
         @tr-and[]
         \ebase[{e'}] = v_0~\ebase_1[e']}
    }
    @tr-step{
      @${\wellFE v_0~\ebase_1[e] : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ebase_1[e] : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE v_0~\ebase_1[e'] : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}
        @tr-and[]
        \ebase[{e'}] = \eunop{\ebase_0[e']}}
    }
    @tr-step{
      @${\wellFE \eunop{\ebase_0[e]} : \tau}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \eunop{\ebase_0[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}
        @tr-and[]
        \ebase[{e'}] = \vpair{\ebase_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellFE \vpair{\ebase_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{\ebase_0[e']}{e_1} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \vpair{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{v_0}{\ebase_1[e]}
         @tr-and[]
         \ebase[{e'}] = \vpair{v_0}{\ebase_1[e']}}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ebase_1[e]} : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ebase_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ebase_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}
        @tr-and[]
        \ebase[{e'}] = \ebinop{\ebase_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebinop{\ebase_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellFE e_1 : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{\ebase_0[e']}{e_1} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}
         @tr-and[]
         \ebase[{e'}] = \ebinop{v_0}{\ebase_1[e']}}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ebase_1[e]} : \tau}
    }
    @tr-step{
      @${\wellFE v_0 : \tau_0
         @tr-and[]
         \wellFE \ebase_1[e] : \tau_1}
      @F-S-inversion
    }
    @tr-step{
      @${\wellFE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ebase_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \echk{\tau''}{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \echk{\tau''}{\ebase_0[e]}
        @tr-and[]
        \ebase[{e'}] = \echk{\tau''}{\ebase_0[e']}}
    }
    @tr-step{
      @${\wellFE \echk{\tau''}{\ebase_0[e]} : \tau}
    }
    @tr-step{
      @${\wellFE \ebase_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \echk{\tau''}{\ebase_0[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@tr-lemma[#:key "F-D-hole-subst" @elem{@${\langF} dynamic hole substitution}]{
  If @${\wellFE \ebase[{e}]} and @${\wellFE e'} then @${\wellFE \ebase[{e'}]}
}@tr-proof{
  By induction on the structure of @${\ebase}

  @tr-case[@${\ebase = \ehole}]{
    @tr-qed{
      @${\ebase[{e'}] = e'}
    }
  }

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}
        @tr-and[]
        \ebase[{e'}] = \vpair{\ebase_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellFE \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{\ebase_0[e']}{e_1}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \vpair{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{v_0}{\ebase_1[e]}
         @tr-and[]
         \ebase[{e'}] = \vpair{v_0}{\ebase_1[e']}}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \vpair{v_0}{\ebase_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \ebase_0~e_1}]{
    @tr-step{
      @${\ebase[{e}] = \ebase_0[e]~e_1
        @tr-and[]
        \ebase[{e'}] = \ebase_0[e']~e_1}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]~e_1}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebase_0[e']~e_1}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = v_0~\ebase_1}]{
    @tr-step{
      @${\ebase[{e}] = v_0~\ebase_1[e]
         @tr-and[]
         \ebase[{e'}] = v_0~\ebase_1[e']}
    }
    @tr-step{
      @${\wellFE v_0~\ebase_1[e]}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE v_0~\ebase_1[e']}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}
        @tr-and[] \ebase[{e'}] = \eunop{\ebase_0[e']}}
    }
    @tr-step{
      @${\wellFE \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \eunop{\ebase_0[e']}}
      (4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}
        @tr-and[]
        \ebase[{e'}] = \ebinop{\ebase_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \ebase_0[e]
         @tr-and[]
         \wellFE e_1}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{\ebase_0[e']}{e_1}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}
         @tr-and[]
         \ebase[{e'}] = \ebinop{v_0}{\ebase_1[e']}}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellFE v_0
         @tr-and[]
         \wellFE \ebase_1[e]}
      @|F-D-inversion|
    }
    @tr-step{
      @${\wellFE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellFE \ebinop{v_0}{\ebase_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \echk{\tau_0}{\ebase_0}}]{
    @tr-contradiction{
      @${\wellFE \ebase[{e}]}
    }
  }

}

@tr-lemma[#:key "F-hole-subst" @elem{@${\langF} hole substitution}]{
  @itemlist[
  @item{
    If @${\wellFE \ctxE{e}} and the derivation contains a sub-term
     @${\wellFE e : \tau'} and @${\wellFE e' : \tau'} then @${\wellFE \ctxE{e'}}.
  }
  @item{
    If @${\wellFE \ctxE{e}} and the derivation contains a sub-term
     @${\wellFE e} and @${\wellFE e'} then @${\wellFE \ctxE{e'}}.
  }
  @item{
    If @${\wellFE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellFE e : \tau'} and @${\wellFE e' : \tau'} then @${\wellFE \ctxE{e'} : \tau}.
  }
  @item{
    If @${\wellFE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellFE e} and @${\wellFE e'} then @${\wellFE \ctxE{e'} : \tau}.
  }
  ]
}@tr-proof{
  By the following four lemmas:
   @|F-DS-hole-subst|, @|F-DD-hole-subst|, @|F-SS-hole-subst|, and @|F-SD-hole-subst|.
}


@tr-lemma[#:key "F-DS-hole-subst" @elem{@${\langF} dynamic context static hole substitution}]{
  If @${\wellFE \ctxE{e}}
   and contains @${\wellFE e : \tau'},
   and furthermore @${\wellFE e' : \tau'},
   then @${\wellFE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellFE \ctxE{e}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \eunop{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \echk{\tau''}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-D-inversion|
    }
    @tr-qed{
      by @|F-SS-hole-subst| (2)
    }
  }
}

@tr-lemma[#:key "F-DD-hole-subst" @elem{@${\langF} dynamic context dynamic hole substitution}]{
  If @${\wellFE \ctxE{e}}
   and contains @${\wellFE e},
   and furthermore @${\wellFE e'},
   then @${\wellFE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|F-D-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \eunop{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e]}
      @|F-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-D-inversion|
    }
    @tr-qed{
      by @|F-SD-hole-subst| (2)
    }
  }
}

@tr-lemma[#:key "F-SS-hole-subst" @elem{@${\langF} static context static hole substitution}]{
  If @${\wellFE \ctxE{e} : \tau}
   and contains @${\wellFE e : \tau'},
   and furthermore @${\wellFE e' : \tau'},
   then @${\wellFE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|F-S-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \eunop{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \echk{\tau''}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-S-inversion|
    }
    @tr-qed{
      by @|F-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e} : \tau}
    }
  }
}

@tr-lemma[#:key "F-SD-hole-subst" @elem{@${\langF} static context dynamic hole substitution}]{
  If @${\wellFE \ctxE{e} : \tau}
   and contains @${\wellFE e},
   and furthermore @${\wellFE e'},
   then @${\wellFE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellFE \ctxE{e} : \tau} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eapp{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \vpair{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \vpair{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \eunop{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \eunop{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellFE \esd_0[e] : \tau_0}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \ebinop{v_0}{\esd_1}}]{
    @tr-step{
      @${\esd[e] = \ebinop{v_0}{\esd_1[e]}}
    }
    @tr-step{
      @${\wellFE \esd_1[e] : \tau_1}
      @|F-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \echk{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e} : \tau}
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellFE \esd_0[e]}
      @|F-S-inversion|
    }
    @tr-qed{
      by @|F-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellFE \ctxE{e} : \tau}
    }
  }
}

@; ---------
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
}@tr-proof[#:sketch? #true]{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-Delta-type-soundness"]{@${\Delta} type soundness} lemma.
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
  Similar to the proof for the @|holong| @tr-ref[#:key "N-delta-preservation"]{@${\delta} preservation} lemma.
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "F-subst" @elem{@${\langF} substitution}]{
  @itemlist[
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellFE e}
    and @${\wellFE v : \tau_x}
    then @${\Gamma \wellFE \vsubst{e}{x}{v}}
  }
  @item{
    If @${x,\Gamma \wellFE e}
    and @${\wellFE v}
    then @${\Gamma \wellFE \vsubst{e}{x}{v}}
  }
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellFE e : \tau}
    and @${\wellFE v : \tau_x}
    then @${\Gamma \wellFE \vsubst{e}{x}{v} : \tau}
  }
  @item{
    If @${x,\Gamma \wellFE e : \tau}
    and @${\wellFE v}
    then @${\Gamma \wellFE \vsubst{e}{x}{v} : \tau}
  }
  ]
}@tr-proof{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-subst"]{substitution} lemma.
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
  @tr-qed{because @${e} is closed under @${\Gamma}}
}

