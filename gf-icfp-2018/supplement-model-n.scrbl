#lang gf-icfp-2018
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

   (define N-S-implies @tr-ref[#:key "N-S-implies"]{static subset})
   (define N-D-implies @tr-ref[#:key "N-D-implies"]{dynamic subset})

   (define N-S-factor @tr-ref[#:key "N-S-factor"]{boundary factoring})
   (define N-D-factor @tr-ref[#:key "N-D-factor"]{boundary factoring})

   (define N-boundary @tr-ref[#:key "N-boundary"]{inner boundary})

   (define N-S-uec @tr-ref[#:key "N-S-uec"]{unique static evaluation contexts})
   (define N-D-uec @tr-ref[#:key "N-D-uec"]{unique dynamic evaluation contexts})

   (define N-S-hole-typing @tr-ref[#:key "N-S-hole-typing"]{static hole typing})
   (define N-D-hole-typing @tr-ref[#:key "N-D-hole-typing"]{dynamic hole typing})

   (define N-boundary-typing @tr-ref[#:key "N-boundary-typing"]{boundary hole typing})
   (define N-DS-hole @tr-ref[#:key "N-DS-hole"]{static @${\vdyn} hole typing})
   (define N-DD-hole @tr-ref[#:key "N-DD-hole"]{dynamic @${\vdyn} hole typing})
   (define N-SS-hole @tr-ref[#:key "N-SS-hole"]{static @${\vsta} hole typing})
   (define N-SD-hole @tr-ref[#:key "N-SD-hole"]{dynamic @${\vsta} hole typing})

   (define N-hole-subst @tr-ref[#:key "N-hole-subst"]{hole substitution})
   (define N-DS-hole-subst @tr-ref[#:key "N-DS-hole-subst"]{dynamic context static hole substitution})
   (define N-DD-hole-subst @tr-ref[#:key "N-DD-hole-subst"]{dynamic context dynamic hole substitution})
   (define N-SS-hole-subst @tr-ref[#:key "N-SS-hole-subst"]{static context static hole substitution})
   (define N-SD-hole-subst @tr-ref[#:key "N-SD-hole-subst"]{static context dynamic hole substitution})

   (define N-S-hole-subst @tr-ref[#:key "N-S-hole-subst"]{static boundary-free hole substitution})
   (define N-D-hole-subst @tr-ref[#:key "N-D-hole-subst"]{dynamic boundary-free hole substitution})

   (define N-S-inversion @tr-ref[#:key "N-S-inversion"]{inversion})
   (define N-D-inversion @tr-ref[#:key "N-D-inversion"]{inversion})

   (define N-S-canonical @tr-ref[#:key "N-S-canonical"]{canonical forms})

   (define N-Delta-soundness @tr-ref[#:key "N-Delta-type-soundness"]{@${\Delta} type soundness})
   (define N-delta-preservation @tr-ref[#:key "N-delta-preservation"]{@${\delta} preservation})

   (define N-D-soundness @tr-ref[#:key "N-D-soundness"]{@${\langN} dynamic soundness})
   (define N-S-soundness @tr-ref[#:key "N-S-soundness"]{@${\langN} static soundness})

   (define N-fromdyn-soundness @tr-ref[#:key "N-fromdyn-soundness"]{@${\vfromdynN} soundness})
   (define N-fromsta-soundness @tr-ref[#:key "N-fromsta-soundness"]{@${\vfromstaN} soundness})

   (define N-subst @tr-ref[#:key "N-subst"]{substitution})
   (define N-DS-subst @tr-ref[#:key "N-DS-subst"]{dynamic context static value substitution})
   (define N-DD-subst @tr-ref[#:key "N-DD-subst"]{dynamic context dynamic value substitution})
   (define N-SS-subst @tr-ref[#:key "N-SS-subst"]{static context static value substitution})
   (define N-SD-subst @tr-ref[#:key "N-SD-subst"]{static context dynamic value substitution})

   (define N-weakening @tr-ref[#:key "N-weakening"]{weakening})

)

@tr-theorem[#:key "N-S-soundness" @elem{static @${\langN}-soundness}]{
  If @${\wellM e : \tau} then @${\wellNE e : \tau} and one of the following holds:
  @itemlist[
    @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
    @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrND \tagerror} }
    @item{ @${e \rrNSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellNE e : \tau}
      @|N-S-implies|
    }}
    @item{@tr-qed{
      by @|N-S-progress| and @|N-S-preservation|.
    }}
  ]
}

@tr-theorem[#:key "N-D-soundness" @elem{dynamic @${\langN}-soundness}]{
    If @${\wellM e} then @${\wellNE e} and one of the following holds:
    @itemlist[
      @item{ @${e \rrNDstar v \mbox{ and } \wellNE v} }
      @item{ @${e \rrNDstar \ctxE{e'}} and @${e' \rrND \tagerror} }
      @item{ @${e \rrNDstar \boundaryerror} }
      @item{ @${e} diverges}
    ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellNE e}
      @|N-D-implies|
    }}
    @item{@tr-qed{
      by @|N-D-progress| and @|N-D-preservation|.
    }}
  ]
}

@; TODO compilation
@;@tr-remark[#:key "N-compilation" @elem{@${\langN}-compilation}]{
@;  The @${\rrNSstar} reduction relation is a subset of the @${\rrNDstar} relation.
@;  In practice, uses of @${\rrNSstar} may be replaced with @${\rrNDstar}.
@;}
@;
@;@tr-theorem[#:key "N-compilation" @elem{@${\langN}-compilation}]{
@;  If @${\wellM e : \tau} and @${\rastar} is a reduction relation based on @${\rrND}
@;   in which @${\vfromstaN} is defined as @${\vfromdynN}, then
@;  @${\wellNE e : \tau} and one of the following holds:
@;  @itemlist[
@;    @item{ @${e \rastar v \mbox{ and } \wellNE v : \tau} }
@;    @item{ @${e \rastar \tagerror} }
@;    @item{ @${e \rastar \boundaryerror} }
@;    @item{ @${e} diverges}
@;  ]
@;}@tr-proof[#:sketch? #true]{
@;  Progress and preservation holds because @${\rrNS} is a subset of @${\rrND}
@;   and @${\vfromdynN} performs a subset of the checks that @${\vfromstaN} does.
@;}

@;@tr-corollary[#:key "N-pure-static" @elem{@${\langN} static soundness}]{
@;  If @${\wellM e : \tau} and @${e} is purely static, then one of the following holds:
@;  @itemlist[
@;    @item{ @${e \rrNEstar v \mbox{ and } \wellNE v : \tau} }
@;    @item{ @${e \rrNEstar \boundaryerror} }
@;    @item{ @${e} diverges}
@;  ]
@;}@tr-proof{(sketch)
@;  Purely-static terms cannot step to a @${\tagerror} and are preserved by the
@;   @${\ccNS} reduction relation.
@;}

@tr-lemma[#:key "N-fromdyn-soundness" @elem{@${\vfromdynN} soundness}]{
  If @${\wellNE v} then @${\wellNE \efromdynN{\tau}{v}}.
}@tr-proof{
  @tr-case[@${\efromdynN{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-step{
      @${\wellNE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}
      @${\wellNE v}
    }
    @tr-qed{}
  }

  @tr-case[@${v \valeq \vpair{v_0}{v_1}
              @tr-and[4]
              \efromdynN{\tpair{\tau_0}{\tau_1}}{v} = \vpair{\edyn{\tau_0}{v_0}}{\edyn{\tau_1}{v_1}}}]{
    @tr-step{
      @${\wellNE v_0 @tr-and[4] \wellNE v_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \edyn{\tau_0}{v_0} : \tau_0
         @tr-and[]
         \wellNE \edyn{\tau_1}{v_1} : \tau_1}
      (1)
    }
    @tr-qed{(2)}
  }

  @tr-case[@${v = i @tr-and[4] \efromdynN{\tnat}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${v \in \naturals @tr-and[4] \efromdynN{\tnat}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${\efromdynN{\tau}{v} = \boundaryerror}]{
    @tr-qed{}
  }
}

@tr-lemma[#:key "N-fromsta-soundness" @elem{@${\vfromstaN} soundness}]{
  If @${\wellNE v : \tau} then @${\wellNE \efromstaN{\tau}{v}}.
}@tr-proof{
  @tr-case[@${\wellNE v : \tarr{\tau_d}{\tau_c}
              @tr-and[4]
              \efromstaN{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed{}
  }

  @tr-case[@${\wellNE v : \tpair{\tau_0}{\tau_1}
              @tr-and[4]
              \efromstaN{\tpair{\tau_0}{\tau_1}}{v} = \vpair{\esta{\tau_0}{v_0}}{\esta{\tau_1}{v_1}}}]{
    @tr-step{
      @${v = \vpair{v_0}{v_1}}
      @|N-S-canonical|
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE v_1 : \tau_1}
      @|N-S-inversion| (1)
    }
    @tr-step{
      @${\wellNE {\esta{\tau_0}{v_0}} : \tau_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\wellNE {\esta{\tau_1}{v_1}} : \tau_1}
      @tr-IH (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\wellNE v : \tint
              @tr-and[4]
              \efromstaN{\tint}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${\wellNE v : \tnat
              @tr-and[4]
              \efromstaN{\tnat}{v} = v}]{
    @tr-qed{}
  }
}

@tr-lemma[#:key "N-S-implies" @elem{@${\langN} static subset}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellNE e : \tau}.
}@tr-proof{
  @; alt: \wellM is a subset of \wellNE

  By structural induction on the derivation of @${\Gamma \wellM e : \tau}.

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @tr-step{
      @${\Gamma \wellNE x : \tau}
      @${\tann{x}{\tau} \in \Gamma}}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tau_d \tarrow \tau_c
              }}]{
    @tr-step{
      @${\tann{x}{\tau_d},\Gamma \wellNE e : \tau_c}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellNE e_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_d}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE \eapp{e_0}{e_1} : \tau_c} }
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
      @${\Gamma \wellNE e_0 : \tau_0}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellNE e_0 : \tau_0
         @tr-and[]
         \Gamma \wellNE e_1 : \tau_1}
      @tr-IH}
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
    @tr-step{
      @${\Gamma \wellNE e : \tau'}
      @tr-IH}
    @tr-step{
      @${\Gamma \wellNE e : \tau}
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
    @tr-step{
      @${\Gamma \wellNE e}
      @|N-D-implies|}
    @tr-step{
      @${\Gamma \wellNE \edyn{\tau}{e} : \tau}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "N-D-implies" @elem{@${\langN} dynamic subset}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellNE e}.
}@tr-proof{
  By structural induction on the derivation of @${\Gamma \wellM e}.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @tr-step{
      @${\Gamma \wellNE x}
      @${x \in \Gamma}}
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e
              }{
                \Gamma \wellM \vlam{x}{e}
              }}]{
    @tr-step{
      @${x,\Gamma \wellNE e}
      @tr-IH}
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
      @${\Gamma \wellNE \eapp{e_0}{e_1}}
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
      @${\Gamma \wellNE e : \tau}
      @|N-S-implies|}
    @tr-step{
      @${\Gamma \wellNE \esta{\tau}{e}}
      (1)}
    @tr-qed[]
  }
}

@tr-lemma[#:key "N-S-progress" @elem{@${\langN} static progress}]{
  If @${\wellNE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccNS e'} }
    @item{ @${e \ccNS \boundaryerror} }
    @item{ @${e \eeq \esd[{\edyn{\tau'}{\ebase[e']}}] \mbox{ and } e' \rrND \tagerror} }
  ]
}@tr-proof{
  By the @|N-S-factor| lemma, there are seven possible cases.

  @tr-case[@elem{@${e} is a value}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\wellNE \eapp{v_0}{v_1} : \tau'}
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
        @tr-step{
          @${e \ccNS \ebase[{\vsubst{e'}{x}{v_1}}]}
          @${\eapp{v_0}{v_1} \rrNS \vsubst{e'}{x}{v_1}}}
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}]{
        @tr-step{
          @${e \ccNS \ebase[{\edyn{\tau_c'}{(\eapp{v_f}{\esta{\tau_d'}{v_1}})}}]}
          @${\eapp{v_0}{v_1} \rrNS \edyn{\tau_c'}{(\eapp{v_f}{\esta{\tau_d'}{v_1}})}}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]}]{
    @tr-step{
      @${\wellNE \eunop{v} : \tau'}
      @|N-S-hole-typing|}
    @tr-step{
      @${\wellNE v : \tpair{\tau_0}{\tau_1}}
      @|N-S-inversion|}
    @tr-step{
      @${v = \vpair{v_0}{v_1}}
      @|N-S-canonical|}
    @list[
      @tr-if[@${\vunop = \vfst}]{
        @${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}
        @tr-step{
          @${e \ccNS \ebase[{v_0}]}
          @${\eunop{v} \rrNS v_0}}
        @tr-qed[]
      }
      @tr-else[@${\vunop = \vsnd}]{
        @${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}
        @tr-step{
          @${e \ccNS \ebase[{v_1}]}
          @${\eunop{v} \rrNS v_1}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${\wellNE \ebinop{v_0}{v_1} : \tau'}
      @|N-S-hole-typing|}
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|N-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = e'}
      @elem{@|N-Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrNS e'}
      (3)}
    @tr-qed{
      by @${e \ccNS \ebase[e']}
    }
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \ccND e''
         @tr-or[]
         e' \ccND \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrND \tagerror
      }
      @|N-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccNS \ctxE{\efromdynN{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \ccND e''}]{
        @tr-qed{
          @${e \ccNS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccND \boundaryerror}]{
        @tr-qed{
          @${e \ccNS \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrND \tagerror}]{
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
         e' \ccNS e''
         @tr-or[]
         e' \ccNS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrND \tagerror}
      @|N-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccNS \ctxE{\efromstaN{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \ccNS e''}]{
        @tr-qed{
          @${e \ccNS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccNS \boundaryerror}]{
        @tr-qed{
          @${e \ccNS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrND \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\eerr}}]{
    @tr-qed[@${e \ccNS \eerr}]
  }
}

@tr-lemma[#:key "N-D-progress" @elem{@${\langN} dynamic progress}]{
  If @${\wellNE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccND e'} }
    @item{ @${e \ccND \boundaryerror} }
    @item{ @${e \eeq \ctxE{e'}} and @${e' \rrND \tagerror} }
  ]
}@tr-proof{
  By the @|N-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccND \ebase[{\vsubst{e'}{x}{v_1}}]}
        @${\eapp{v_0}{v_1} \rrND \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}}]{
      @tr-step{
        @${e \ccND \ebase[{\esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}]}
        @${\eapp{v_0}{v_1}
           \rrND \esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${(\eapp{v_0}{v_1}) \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vunop, v) = e'}]{
      @tr-step{
        @${(\eunop{v}) \rrND e'}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${(\eunop{v}) \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrND e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccND \tagerror}
        @${\ebinop{v_0}{v_1} \rrND \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@elem{@${e = \esd[{\edyn{\tau'}{e'}}]} and @${e'} is boundary-free}]{
    @tr-step{
      @${e \mbox{ is a value}
         @tr-or[]
         e' \ccND e''
         @tr-or[]
         e' \ccND \boundaryerror
         @tr-or[]
         e' \eeq \ctxE{e''} \mbox{ and } e'' \rrND \tagerror}
      @|N-D-progress|
    }
    @list[
      @tr-if[@${e \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccND \ctxE{\efromdynN{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \ccND e''}]{
        @tr-qed{
          @${e \ccNS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccND \boundaryerror}]{
        @tr-qed{
          @${e \ccND \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \ctxE{e''} \mbox{ and } e'' \rrND \tagerror}]{
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
         e' \ccNS e''
         @tr-or[]
         e' \ccNS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrND \tagerror}
      @|N-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccNS \ctxE{\efromstaN{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \ccNS e''}]{
        @tr-qed{
          @${e \ccNS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccNS \boundaryerror}]{
        @tr-qed{
          @${e \ccNS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrND \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e = \esd[\eerr]}]{
    @tr-qed{
      @${e \ccND \eerr}
    }
  }

}

@tr-lemma[#:key "N-S-preservation" @elem{@${\langN} static preservation}]{
  If @${\wellNE e : \tau} and @${e \ccNS e'} then @${\wellNE e' : \tau}
}@tr-proof{
  By the @|N-S-factor| lemma there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccNS e'}}
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_x}}{e'}
              @tr-and[2]
              e \ccNS \ebase[{\vsubst{e'}{x}{v_1}}]}]{
      @tr-step{
        @${\wellNE \eapp{v_0}{v_1} : \tau'}
        @|N-S-hole-typing|}
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
        @elem{@|N-subst| (4, 5)}}
      @tr-step{
        @${\wellNE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|N-hole-subst| (7)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{\tarr{\tau_d}{\tau_c}}{v_f}
              @tr-and[4]
              e \ccNS \ebase[{\edyn{\tau_c}{(\eapp{v_f}{(\esta{\tau_d}{v_1})})}}]}]{
      @tr-step{
        @${\wellNE \eapp{v_0}{v_1} : \tau'}
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
        @${\wellNE \eapp{v_f}{(\esta{\tau_d}{v_1})}}
        (3, 7)}
      @tr-step{
        @${\wellNE \edyn{\tau_c}{\eapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau_c}
        (8)}
      @tr-step{
        @${\wellNE \edyn{\tau_c}{\eapp{v_f}{(\esta{\tau_d}{v_1})}} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|N-hole-subst| (10)}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccNS \ebase[{v_0}]}]{
      @tr-step{
        @${\wellNE \efst{\vpair{v_0}{v_1}} : \tau'}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_0 \subteq \tau'}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE v_0 : \tau_0}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\wellNE v_0 : \tau'}
        (2, 3)}
      @tr-qed{
        by @|N-hole-subst| (4)}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccNS \ebase[{v_1}]}]{
      @tr-step{
        @${\wellNE \esnd{\vpair{v_0}{v_1}} : \tau'}
        @|N-S-hole-typing|}
      @tr-step{
        @${\wellNE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_1 \subteq \tau'}
        @|N-S-inversion| (1)}
      @tr-step{
        @${\wellNE v_1 : \tau_1}
        @|N-S-inversion| (2)}
      @tr-step{
        @${\wellNE v_1 : \tau'}
        (2, 3)}
      @tr-qed{
        by @|N-hole-subst| (4)}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${e \ccNS \ctxE{\delta(\vbinop, v_0, v_1)}}
      @${e \ccNS e'}
    }
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
      @${\wellNE \delta(\vbinop, v_0, v_1) : \tau''}
      @|N-Delta-soundness| (2)}
    @tr-step{
      @${\wellNE \delta(\vbinop, v_0, v_1) : \tau'}
      (2, 3)}
    @tr-qed{
      by @|N-hole-subst| (4)
    }
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccNS \ctxE{\efromdynN{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau'}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e'}
        @|N-S-inversion| (2)
      }
      @tr-step{
        @${\wellNE \efromdynN{\tau'}{e'} : \tau'}
        @|N-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|N-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccND e''}]{
      @tr-step{
        @${e \ccNS \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau'}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e'}
        @|N-S-inversion| (2)
      }
      @tr-step{
        @${\wellNE e''}
        @|N-D-preservation| (3)
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|N-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccNS \ctxE{\efromstaN{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion| (2)
      }
      @tr-step{
        @${\wellNE \efromstaN{\tau'}{e'}}
        @|N-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|N-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccND e''}]{
      @tr-step{
        @${e \ccNS \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion| (2)
      }
      @tr-step{
        @${\wellNE e'' : \tau'}
        @|N-S-preservation| (3)
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|N-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[\eerr]}}]{
    @tr-step{
      @${e \ccNS \eerr}
    }
    @tr-qed{
      @${\wellNE \eerr : \tau}
    }
  }

}

@tr-lemma[#:key "N-D-preservation" @elem{@${\langN} dynamic preservation}]{
  If @${\wellNE e} and @${e \ccND e'} then @${\wellNE e'}
}@tr-proof{
  By the @|N-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccND e'}}
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccND \ebase[{\vsubst{e'}{x}{v_1}}]}]{
      @tr-step{
        @${\wellNE \eapp{v_0}{v_1}}
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
        @|N-subst| (2, 3)}
      @tr-qed{
        @|N-hole-subst| (4)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}
                @tr-and[4]
                e \ccND \ebase[{\esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}]}]{
      @tr-step{
        @${\wellNE \eapp{v_0}{v_1}}
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
        @${\wellNE \eapp{v_f}{(\edyn{\tau_d}{v_1})} : \tau_c}
        (3, 4)}
      @tr-step{
        @${\wellNE \esta{\tau_c}{\eapp{v_f}{(\edyn{\tau_d}{v_1})}}}
        (5)}
      @tr-qed{
        by @|N-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccND \ebase[{v_0}]}]{
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
        by @|N-hole-subst|}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccND \ebase[{v_1}]}]{
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
        by @|N-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${e \ccND \ebase[{\delta(\vbinop, v_0, v_1)}]}
    }
    @tr-step{
      @${\wellNE \ebinop{v_0}{v_1}}
      @|N-D-hole-typing|}
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE v_1}
      @|N-D-inversion| (1)}
    @tr-step{
      @${\wellNE {\delta(\vbinop, v_0, v_1)}}
      @|N-delta-preservation| (2)}
    @tr-qed{
      by @|N-hole-subst| (3)}
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccND \ctxE{\efromdynN{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau'}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e'}
        @|N-S-inversion| (2)
      }
      @tr-step{
        @${\wellNE \efromdynN{\tau'}{e'} : \tau'}
        @|N-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|N-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccND e''}]{
      @tr-step{
        @${e \ccND \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e'} : \tau'}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e' 
           @tr-and[]
           \tau' \subteq \tau''}
        @|N-S-inversion| (2)
      }
      @tr-step{
        @${\wellNE e''}
        @|N-D-preservation| (3)
      }
      @tr-step{
        @${\wellNE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|N-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccND \ctxE{\efromstaN{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion| (2)
      }
      @tr-step{
        @${\wellNE \efromstaN{\tau'}{e'}}
        @|N-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|N-hole-subst| (5)
      }
    }
    @tr-else[@${e' \ccND e''}]{
      @tr-step{
        @${e \ccND \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e'}}
        @|N-boundary-typing|
      }
      @tr-step{
        @${\wellNE e' : \tau'}
        @|N-D-inversion| (2)
      }
      @tr-step{
        @${\wellNE e'' : \tau'}
        @|N-S-preservation| (3)
      }
      @tr-step{
        @${\wellNE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|N-hole-subst| (5)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccND \eerr}}
    @tr-qed{
      @${\wellNE \eerr}
    }
  }
}

@tr-lemma[#:key "N-S-factor" @elem{@${\langN} static boundary factoring}]{
  If @${\wellNE e : \tau} then one of the following holds:
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
  By the @|N-S-uec| lemma, there are seven cases.

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
      @|N-boundary|
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
      @|N-boundary|
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
      @|N-boundary|
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

@tr-lemma[#:key "N-S-uec" @elem{@${\langN} unique static evaluation contexts}]{
  If @${\wellNE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \esd[\eapp{v_0}{v_1}]} }
    @item{ @${e = \esd[\eunop{v}]} }
    @item{ @${e = \esd[\ebinop{v_0}{v_1}]} }
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

  @tr-case[@${e = \eerr}]{
    @tr-step{
      @${\esd = \ehole}
    }
    @tr-qed[@${e = \esd[\eerr]}]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|
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
        @${\wellNE e_0 : \tau_0}
        @|N-S-inversion|}
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
        @${\wellNE e_1 : \tau_1}
        @|N-S-inversion|}
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

  @tr-case[@${e = \edyn{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellNE e_0}
        @|N-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|N-D-uec| (1)
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

}

@tr-lemma[#:key "N-boundary" @elem{@${\langN} inner boundary}]{
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
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
      @tr-if[@${\esd_1 = \esd_1'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{v_0}{\esd_1'}}
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
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
      @tr-if[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
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

@tr-lemma[#:key "N-D-factor" @elem{@${\langN} dynamic boundary factoring}]{
  If @${\wellNE e} then one of the following holds:
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
  By the @|N-D-uec| lemma, there are seven cases.

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
      @|N-boundary|
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
      @|N-boundary|
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
      @|N-boundary|
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

@tr-lemma[#:key "N-D-uec" @elem{@${\langN} unique dynamic evaluation contexts}]{
  If @${\wellNE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \esd[\eapp{v_0}{v_1}]} }
    @item{ @${e = \esd[\eunop{v}]} }
    @item{ @${e = \esd[\ebinop{v_0}{v_1}]} }
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

  @tr-case[@${e = \eerr}]{
    @tr-step{@${\esd = \ehole}}
    @tr-qed[@${e = \esd[\eerr]}]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellNE e_0}
        @|N-D-inversion|}
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
        @${\wellNE e_1}
        @|N-D-inversion|}
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
        @${\wellNE e_0}
        @|N-D-inversion|}
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
        @${\wellNE e_1}
        @|N-D-inversion|}
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
        @${\wellNE e_0}
        @|N-D-inversion|}
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
        @${\wellNE e_0}
        @|N-D-inversion|}
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
        @${\wellNE e_1}
        @|N-D-inversion|}
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

  @tr-case[@${e = \esta{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellNE e_0}
        @|N-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|N-D-uec| (1)
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
}

@tr-lemma[#:key "N-S-hole-typing" @elem{@${\langN} static hole typing}]{
  If @${\wellNE \ebase[{e}] : \tau} then the derivation
   contains a sub-term @${\wellNE e : \tau'}
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
      @${\wellNE \ebase_0[e] : \tarr{\tau_d}{\tau_c}}
      @|N-S-inversion|
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
      @${\wellNE \ebase_1[e] : \tau_d}
      @|N-S-inversion|
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
      @${\wellNE \ebase_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ebase_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \ebase_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ebase_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \ebase_1[e] : \tau_1}
      @|N-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "N-D-hole-typing" @elem{@${\langN} dynamic hole typing}]{
  If @${\wellNE \ebase[{e}]} then the derivation contains a sub-term @${\wellNE e}
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
      @${\wellNE \ebase_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \ebase_1[e]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "N-boundary-typing" @elem{@${\langN} boundary hole typing}]{
  @itemlist[
  @item{
    If @${\wellNE \ctxE{\edyn{\tau}{e}}} then the derivation contains a
    sub-term @${\wellNE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellNE \ctxE{\edyn{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellNE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellNE \ctxE{\esta{\tau}{e}}} then the derivation contains a
    sub-term @${\wellNE \esta{\tau}{e}}
  }
  @item{
    If @${\wellNE \ctxE{\esta{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellNE \esta{\tau}{e}}
  }
  ]
}@tr-proof{
  By the following four lemmas: @|N-DS-hole|, @|N-DD-hole|, @|N-SS-hole|, and @|N-SD-hole|.
}

@tr-lemma[#:key "N-DS-hole" @elem{@${\langN} static @${\vdyn} hole typing}]{
  If @${\wellNE \ctxE{\edyn{\tau}{e}} : \tau'} then the derivation contains
   a sub-term @${\wellNE \edyn{\tau}{e} : \tau}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-step{
      @${\wellNE \edyn{\tau}{e} : \tau''}
      @|N-S-hole-typing|
    }
    @tr-step{
      @${\wellNE \edyn{\tau}{e} : \tau}
      @|N-S-inversion| (1)
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}]}
      @|N-S-inversion|
    }
    @tr-qed{
      by @|N-DD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{\edyn{\tau}{e}} : \tau'}
    }
  }
}

@tr-lemma[#:key "N-DD-hole" @elem{@${\langN} dynamic @${\vdyn} hole typing}]{
  If @${\wellNE \ctxE{\edyn{\tau}{e}}} then the derivation contains
   a sub-term @${\wellNE \edyn{\tau}{e} : \tau}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellNE \ctxE{\edyn{\tau}{e}}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\edyn{\tau}{e}}]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{\edyn{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau_0}{e}} = \esta{\tau_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\edyn{\tau}{e}}] : \tau_0}
      @|N-D-inversion|
    }
    @tr-qed{
      by @|N-DS-hole| (2)
    }
  }
}

@tr-lemma[#:key "N-SS-hole" @elem{@${\langN} static @${\vsta} hole typing}]{
  If @${\wellNE \ctxE{\esta{\tau}{e}} : \tau'} then the derivation contains
   a sub-term @${\wellNE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellNE \ctxE{\esta{\tau}{e}} : \tau'} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}]}
      @|N-S-inversion|
    }
    @tr-qed{
      by @|N-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{\esta{\tau}{e}} : \tau'}
    }
  }
}

@tr-lemma[#:key "N-SD-hole" @elem{@${\langN} dynamic @${\vsta} hole typing}]{
  If @${\wellNE \ctxE{\esta{\tau}{e}}} then the derivation contains
   a sub-term @${\wellNE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{
      by @|N-D-hole-typing|
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[{\esta{\tau}{e}}]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[{\esta{\tau}{e}}]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{\esta{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau_0}{e}} = \esta{\tau_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellNE \esd_0[{\esta{\tau}{e}}] : \tau_0}
      @|N-D-inversion|
    }
    @tr-qed{
      by @|N-SS-hole| (2)
    }
  }
}

@tr-lemma[#:key "N-S-hole-subst" @elem{@${\langN} static boundary-free hole substitution}]{
  If @${\wellNE \ebase[e] : \tau}
   and the derivation contains a sub-term @${\wellNE e : \tau'}
   and @${\wellNE e' : \tau'}
   then @${\wellNE \ebase[e'] : \tau}.
}@tr-proof{
  By induction on the structure of @${\ebase}

  @tr-case[@${\ebase = \ehole}]{
    @tr-step{
      @${\ebase[{e}] = e
         @tr-and[]
         \ebase[{e'}] = e'}
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

  @tr-case[@${\ebase = \ebase_0~e_1}]{
    @tr-step{
      @${\ebase[{e}] = \ebase_0[e]~e_1
        @tr-and[]
        \ebase[{e'}] = \ebase_0[e']~e_1}
    }
    @tr-step{
      @${\wellNE \ebase_0[e]~e_1 : \tau}
    }
    @tr-step{
      @${\wellNE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebase_0[e']~e_1 : \tau}
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
      @${\wellNE v_0~\ebase_1[e] : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ebase_1[e] : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE v_0~\ebase_1[e'] : \tau}
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
      @${\wellNE \eunop{\ebase_0[e]} : \tau}
    }
    @tr-step{
      @${\wellNE \ebase_0[e] : \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \eunop{\ebase_0[e']} : \tau}
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
      @${\wellNE \vpair{\ebase_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellNE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{\ebase_0[e']}{e_1} : \tau}
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
      @${\wellNE \vpair{v_0}{\ebase_1[e]} : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ebase_1[e] : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{v_0}{\ebase_1[e']} : \tau}
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
      @${\wellNE \ebinop{\ebase_0[e]}{e_1} : \tau}
    }
    @tr-step{
      @${\wellNE \ebase_0[e] : \tau_0
         @tr-and[]
         \wellNE e_1 : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ebase_0[e'] : \tau_0}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{\ebase_0[e']}{e_1} : \tau}
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
      @${\wellNE \ebinop{v_0}{\ebase_1[e]} : \tau}
    }
    @tr-step{
      @${\wellNE v_0 : \tau_0
         @tr-and[]
         \wellNE \ebase_1[e] : \tau_1}
      @N-S-inversion
    }
    @tr-step{
      @${\wellNE \ebase_1[e'] : \tau_1}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{v_0}{\ebase_1[e']} : \tau}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@tr-lemma[#:key "N-D-hole-subst" @elem{@${\langN} dynamic hole substitution}]{
  If @${\wellNE \ebase[{e}]} and @${\wellNE e'} then @${\wellNE \ebase[{e'}]}
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
      @${\wellNE \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \ebase_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{\ebase_0[e']}{e_1}}
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
      @${\wellNE \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ebase_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \vpair{v_0}{\ebase_1[e']}}
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
      @${\wellNE \ebase_0[e]~e_1}
    }
    @tr-step{
      @${\wellNE \ebase_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebase_0[e']~e_1}
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
      @${\wellNE v_0~\ebase_1[e]}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ebase_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE v_0~\ebase_1[e']}
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
      @${\wellNE \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellNE \ebase_0[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \eunop{\ebase_0[e']}}
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
      @${\wellNE \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \ebase_0[e]
         @tr-and[]
         \wellNE e_1}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_0[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{\ebase_0[e']}{e_1}}
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
      @${\wellNE \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellNE v_0
         @tr-and[]
         \wellNE \ebase_1[e]}
      @|N-D-inversion|
    }
    @tr-step{
      @${\wellNE \ebase_1[e']}
      @elem{@tr-IH (3)}
    }
    @tr-step{
      @${\wellNE \ebinop{v_0}{\ebase_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }
}

@tr-lemma[#:key "N-hole-subst" @elem{@${\langN} hole substitution}]{
  @itemlist[
  @item{
    If @${\wellNE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellNE e : \tau'} and @${\wellNE e' : \tau'} then @${\wellNE \ctxE{e'} : \tau}.
  }
  @item{
    If @${\wellNE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellNE e} and @${\wellNE e'} then @${\wellNE \ctxE{e'} : \tau}.
  }
  @item{
    If @${\wellNE \ctxE{e}} and the derivation contains a sub-term
     @${\wellNE e : \tau'} and @${\wellNE e' : \tau'} then @${\wellNE \ctxE{e'}}.
  }
  @item{
    If @${\wellNE \ctxE{e}} and the derivation contains a sub-term
     @${\wellNE e} and @${\wellNE e'} then @${\wellNE \ctxE{e'}}.
  }
  ]
}@tr-proof{
  By the following four lemmas:
   @|N-DS-hole-subst|, @|N-DD-hole-subst|, @|N-SS-hole-subst|, and @|N-SD-hole-subst|.
}


@tr-lemma[#:key "N-DS-hole-subst" @elem{@${\langN} dynamic context static hole substitution}]{
  If @${\wellNE \ctxE{e}}
   and contains @${\wellNE e : \tau'},
   and furthermore @${\wellNE e' : \tau'},
   then @${\wellNE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellNE \ctxE{e}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-D-inversion|
    }
    @tr-qed{
      by @|N-SS-hole-subst| (2)
    }
  }
}

@tr-lemma[#:key "N-DD-hole-subst" @elem{@${\langN} dynamic context dynamic hole substitution}]{
  If @${\wellNE \ctxE{e}}
   and contains @${\wellNE e},
   and furthermore @${\wellNE e'},
   then @${\wellNE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|N-D-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-D-inversion|
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
      @${\wellNE \esd_1[e]}
      @|N-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-D-inversion|
    }
    @tr-qed{
      by @|N-SD-hole-subst| (2)
    }
  }
}

@tr-lemma[#:key "N-SS-hole-subst" @elem{@${\langN} static context static hole substitution}]{
  If @${\wellNE \ctxE{e} : \tau}
   and contains @${\wellNE e : \tau'},
   and furthermore @${\wellNE e' : \tau'},
   then @${\wellNE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|N-S-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-S-inversion|
    }
    @tr-qed{
      by @|N-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{e} : \tau}
    }
  }
}

@tr-lemma[#:key "N-SD-hole-subst" @elem{@${\langN} static context dynamic hole substitution}]{
  If @${\wellNE \ctxE{e} : \tau}
   and contains @${\wellNE e},
   and furthermore @${\wellNE e'},
   then @${\wellNE \ctxE{e'} : \tau}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellNE \ctxE{e} : \tau} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e] : \tau_0}
      @|N-S-inversion|
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
      @${\wellNE \esd_1[e] : \tau_1}
      @|N-S-inversion|
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
      @${\wellNE \esd_0[e]}
      @|N-S-inversion|
    }
    @tr-qed{
      by @|N-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxE{e} : \tau}
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
      If @${\Gamma \wellNE \eapp{e_0}{e_1} : \tau_c}
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
    by the definition of @${\Gamma \wellNE e : \tau}
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
      If @${\Gamma \wellNE \eapp{e_0}{e_1}}
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
  then @${\wellNE \delta(\vbinop, v_0, v_1) : \tau}.
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
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
        @tr-qed{
          by @${\wellNE \boundaryerror : \tau}
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
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
        @tr-qed{
          by @${\wellNE \boundaryerror : \tau}
        }
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
      If @${\wellNE v} and @${\delta(\vunop, v) = e} then @${\wellNE e}
    }
    @item{
      If @${\wellNE v_0} and @${\wellNE v_1} and @${\delta(\vbinop, v_0, v_1) = e}
       then @${\wellNE e}
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

  @tr-case[@${\delta(\vunop, v) = \boundaryerror}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsum, v_0, v_1) = v_0 + v_1}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \floorof{v_0 / v_1}}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------

@tr-lemma[#:key "N-subst" @elem{@${\langN} substitution}]{
  @itemlist[
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellNE e}
    and @${\wellNE v : \tau_x}
    then @${\Gamma \wellNE \vsubst{e}{x}{v}}
  }
  @item{
    If @${x,\Gamma \wellNE e}
    and @${\wellNE v}
    then @${\Gamma \wellNE \vsubst{e}{x}{v}}
  }
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellNE e : \tau}
    and @${\wellNE v : \tau_x}
    then @${\Gamma \wellNE \vsubst{e}{x}{v} : \tau}
  }
  @item{
    If @${x,\Gamma \wellNE e : \tau}
    and @${\wellNE v}
    then @${\Gamma \wellNE \vsubst{e}{x}{v} : \tau}
  }
  ]
}@tr-proof{
  By the following four lemmas:
    @|N-DS-subst|, @|N-DD-subst|, @|N-SS-subst|, and @|N-SD-subst|.
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

  @tr-case[@${e = \eapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
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
      @${\Gamma \wellNE \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
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

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      @${\eerr = \vsubst{\eerr}{x}{v}}
    }
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

  @tr-case[@${e = \eapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
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
      @${\Gamma \wellNE \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
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

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      @${\eerr = \vsubst{\eerr}{x}{v}}
    }
  }
}

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

  @tr-case[@${e = \eapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
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
      @${\Gamma \wellNE \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
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

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      by @${\eerr = \vsubst{\eerr}{x}{v}}
    }
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

  @tr-case[@${e = \eapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}}
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
      @${\Gamma \wellNE \eapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : \tau}
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

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      by @${\eerr = \vsubst{\eerr}{x}{v}}
    }
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
  @itemize[
    @item{
      @tr-step{
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellNE e
           @tr-or[]
           \Gamma \wellNE e : \tau}
      }
      @tr-qed{
        @${x} is unused in the derivation
      }
    }
  ]
}

