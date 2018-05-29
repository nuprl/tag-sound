#lang gf-icfp-2018
@require{techreport.rkt}

@; TODO use inversion to conclude (e0 e1) : Any, etc ?

@appendix-title++{Locally-Defensive Embedding}

@; -----------------------------------------------------------------------------
@section{@${\langK} Definitions}
@exact{\input{fig:locally-defensive-embedding.tex}}

@; -----------------------------------------------------------------------------
@|clearpage|
@section{@${\langK} Properties}

@(begin ;; ALL DEFINITIONS
  (define K-S-progress @tr-ref[#:key "K-S-progress"]{static progress})
  (define K-D-progress @tr-ref[#:key "K-D-progress"]{dynamic progress})
  (define K-S-preservation @tr-ref[#:key "K-S-preservation"]{static preservation})
  (define K-D-preservation @tr-ref[#:key "K-D-preservation"]{dynamic preservation})

  (define K-check @tr-ref[#:key "K-check"]{check soundness})

  (define K-S-completion @tr-ref[#:key "K-S-completion"]{@${\carrow} static soundness})
  (define K-D-completion @tr-ref[#:key "K-D-completion"]{@${\carrow} dynamic soundness})

  (define K-S-canonical @tr-ref[#:key "K-S-canonical"]{canonical forms})

  (define K-S-inversion @tr-ref[#:key "K-S-inversion"]{inversion})
  (define K-D-inversion @tr-ref[#:key "K-D-inversion"]{inversion})

  (define K-S-value-inversion @tr-ref[#:key "K-S-value-inversion"]{static value inversion})
  (define K-D-value-inversion @tr-ref[#:key "K-D-value-inversion"]{dynamic value inversion})

  (define K-S-hole-typing @tr-ref[#:key "K-S-hole-typing"]{static hole typing})
  (define K-D-hole-typing @tr-ref[#:key "K-D-hole-typing"]{dynamic hole typing})
  (define K-S-hole-subst @tr-ref[#:key "K-S-hole-subst"]{static hole substitution})
  (define K-D-hole-subst @tr-ref[#:key "K-D-hole-subst"]{dynamic hole substitution})

  (define K-subt-preservation @tr-ref[#:key "K-subt-preservation"]{subtype preservation})

  (define K-DD-subst @tr-ref[#:key "K-DD-subst"]{substitution})
  (define K-DS-subst @tr-ref[#:key "K-DS-subst"]{substitution})
  (define K-SS-subst @tr-ref[#:key "K-SS-subst"]{substitution})
  (define K-SD-subst @tr-ref[#:key "K-SD-subst"]{substitution})

  (define K-Delta-soundness @tr-ref[#:key "K-Delta-soundness"]{@${\Delta} tag soundness})
  (define K-Delta-inversion @tr-ref[#:key "K-Delta-inversion"]{@${\Delta} inversion})
  (define K-Delta-preservation @tr-ref[#:key "K-Delta-tag-preservation"]{@${\Delta} tag preservation})

  (define K-delta-preservation @tr-ref[#:key "K-delta-preservation"]{@${\delta} preservation})

  (define K-S-uec @tr-ref[#:key "K-S-uec"]{unique evaluation contexts})
  (define K-D-uec @tr-ref[#:key "K-D-uec"]{unique evaluation contexts})

  (define K-finite-subtyping @tr-ref[#:key "K-finite-subtyping"]{@${\subk} finite})
  (define K-weakening @tr-ref[#:key "K-weakening"]{weakening})

  (define M-uec @tr-ref[#:key "KM-uec"]{@${\langM} unique static evaluation contexts})
)

@tr-theorem[#:key "K-soundness" @elem{@${\langK} type-tag soundness}]{
  If @${\wellM e : \tau}
   and @${\tagof{\tau} = K}, then
   @${\wellM e : \tau \carrow e^+}
   and
   @${\wellKE e^+ : K}
   and either:
@itemlist[
  @item{ @${e^+ \rrKSstar v} and @${\wellKE v : K} }
  @item{ @${e^+ \rrKSstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccKD \tagerror} }
  @item{ @${e^+ \rrKSstar \boundaryerror} }
  @item{ @${e^+} diverges }
]}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellKE e : \tau \carrow e^+
         @tr-and[]
         \wellKE e^+ : K}
      @|K-S-completion|
    }}
    @item{@tr-qed{
      by @|K-S-progress| and @|K-S-preservation|
    }}
  ]
}

@tr-theorem[#:key "K-pure-static" @elem{@${\langK} static soundness}]{
  If @${\wellM e : \tau} and @${e} is purely static then either:
  @itemlist[
    @item{ @${e \rrKSstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrKSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  By @tr-ref[#:key "K-pure-static-progress"]{progress}
  and @tr-ref[#:key "K-pure-static-preservation"]{preservation} lemmas for
  @${\rrKSstar} and @${\wellM}.
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-completion" @elem{@${\carrow} static soundness}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \vdash e : \tau \carrow e'}
   and @${\Gamma \wellKE e' : \tagof{\tau}}.
}@tr-proof{
  By induction on the structure of @${\Gamma \wellM e : \tau}.

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau} \in \Gamma
              }{
                \Gamma \wellM x : \tau
              }}]{
    @tr-step{
      @${\Gamma \vdash x \carrow x}
    }
    @tr-step{
      @${\Gamma \wellKE x : \tagof{\tau}}
      @${\tann{x}{\tau} \in \Gamma}
    }
    @tr-qed[]
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tau_d \tarrow \tau_c
              }}]{
    @tr-step{
      @${\Gamma \vdash e : \tau_c \carrow e'
         @tr-and[]
         \tann{x}{\tau_d},\Gamma \vdash e' : \tagof{\tau_c}}
      @|tr-IH|
    }
    @tr-step{
      @${\tann{x}{\tau_d},\Gamma \vdash e' : \kany}
      @${\tagof{\tau_c} \subk \kany}
    }
    @tr-step{
      @${\vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c} \carrow \vlam{\tann{x}{\tau_d}}{e'}}
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{\tann{x}{\tau_d}}{e'} : \kfun}
      (2)
    }
    @tr-qed{
      (3, 4)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                i \in \naturals
              }{
                \Gamma \wellM i : \tnat
              }}]{
    @tr-step{
      @${\Gamma \vdash i : \tnat \carrow i}
    }
    @tr-qed{
      by @${\Gamma \wellKE i : \knat}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i : \tint
              }}]{
    @tr-step{
      @${\Gamma \vdash i : \tint \carrow i}
    }
    @tr-qed{
      by @${\Gamma \wellKE i : \kint}
    }
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
      @${\Gamma \wellM e_0 : \tau_0 \carrow e_0'
         @tr-and[]
         \Gamma \wellM e_0' : \tagof{\tau_0}}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 : \tau_1 \carrow e_1'
         @tr-and[]
         \Gamma \wellM e_1' : \tagof{\tau_1}}
      @tr-IH
    }
    @tr-step{
      @${\Gamma \wellKE e_0 : \kany}
      @${\tagof{\tau_0} \subk \kany}
    }
    @tr-step{
      @${\Gamma \wellKE e_1 : \kany}
      @${\tagof{\tau_1} \subk \kany}
    }
    @tr-step{
      @${\Gamma \wellM \vpair{e_0}{e_1} : \tau \carrow \vpair{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{e_0'}{e_1'} : \kpair}
      (3, 4)
    }
    @tr-qed{
      by (5, 6)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_d \tarrow \tau_c
                \\
                \Gamma \wellM e_1 : \tau_d
              }{
                \Gamma \wellM \vapp{e_0}{e_1} : \tau_c
              }}]{
    @tr-step{
      @${\Gamma \wellM e_0 : \tarr{\tau_d}{\tau_c} \carrow e_0'
         @tr-and[]
         \Gamma \wellKE e_0' : \tagof{\tarr{\tau_d}{\tau_c}}}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 : \tau_d \carrow e_1'
         @tr-and[]
         \Gamma \wellKE e_1' : \tagof{\tau_c}}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellKE e_0' : \kfun}
      @${\tagof{\tarr{\tau_d}{\tau_c}} = \kfun}
    }
    @tr-step{
      @${\Gamma \wellKE e_1' : \kany}
      @${\tagof{\tau_c} \subk \kany}
    }
    @tr-step{
      @${\Gamma \wellM e_0~e_1 : \tau_c \carrow \echk{\tagof{\tau_c}}{(e_0'~e_1')}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \echk{\tagof{\tau_c}}{(e_0'~e_1')} : \tagof{\tau_c}}
      (3, 4)
    }
    @tr-qed{
      by (5, 6)
    }
  }

  @tr-case[#:box? #true
           #:itemize? #false
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0
                \\
                \Delta(\vunop, \tau_0) = \tau
              }{
                \Gamma \wellM \vunop~e_0 : \tau
              }}]{
    @tr-if[@${\vunop = \vfst}]{
      @tr-step{
        @${\Delta(\vfst, \tau_0) = \tau}
      }
      @tr-step{
        @${\tau_0 = \tpair{\tau}{\tau'}}
        @|K-Delta-inversion|
      }
      @tr-step{
        @${\Gamma \wellM e_0 : \tpair{\tau}{\tau'} \carrow e_0'
           @tr-and[]
           \Gamma \wellKE e_0' : \tagof{\tpair{\tau}{\tau'}}}
        @|tr-IH|
      }
      @tr-step{
        @${\Gamma \wellKE e_0' : \kpair}
        @${\tagof{\tpair{\tau}{\tau'}} = \kpair}
      }
      @tr-step{
        @${\Gamma \wellM \efst{e_0} : \tau \carrow \echk{\tagof{\tau}}{(\efst{e_0'})}}
        (2)
      }
      @tr-step{
        @${\Gamma \wellKE \echk{\tagof{\tau}}{(\efst{e_0'})} : \tagof{\tau}}
        (3)
      }
      @tr-qed{
        by 4,5
      }
    }
    @tr-else[@${\vunop = \vsnd}]{
      @tr-step{
        @${\Delta(\vsnd, \tau_0) = \tau}
      }
      @tr-step{
        @${\tau_0 = \tpair{\tau'}{\tau}}
        @|K-Delta-inversion|
      }
      @tr-step{
        @${\Gamma \wellM e_0 : \tpair{\tau'}{\tau} \carrow e_0'
           @tr-and[]
           \Gamma \wellKE e_0' : \tagof{\tpair{\tau'}{\tau}}}
        @|tr-IH|
      }
      @tr-step{
        @${\Gamma \wellKE e_0' : \kpair}
        @${\tagof{\tpair{\tau'}{\tau}} = \kpair}
      }
      @tr-step{
        @${\Gamma \wellM \esnd{e_0} : \tau \carrow \echk{\tagof{\tau}}{(\esnd{e_0'})}}
        (2)
      }
      @tr-step{
        @${\Gamma \wellKE \echk{\tagof{\tau}}{(\esnd{e_0'})} : \tagof{\tau}}
        (3)
      }
      @tr-qed{
        by 4,5
      }
    }
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
      @${\Gamma \wellM e_0 : \tau_0 \carrow e_0'
         @tr-and[]
         \Gamma \wellKE e_0' : \tagof{\tau_0}}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 : \tau_1 \carrow e_1'
         @tr-and[]
         \Gamma \wellKE e_1' : \tagof{\tau_1}}
      @|tr-IH|
    }
    @tr-step{
      @${\Delta(\vbinop, \tagof{\tau_0}, \tagof{\tau_1}) = \tagof{\tau}}
      @|K-Delta-preservation|
    }
    @tr-step{
      @${\Gamma \wellM \ebinop{e_0}{e_1} : \tau \carrow \ebinop{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{e_0'}{e_1'} : \tagof{\tau}}
      (1, 2, 3)
    }
    @tr-qed{
      by (5, 6)
    }
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
      @${\Gamma \wellM e : \tau' \carrow e'
         @tr-and[]
         \Gamma \wellKE e' : \tagof{\tau'}}
      @|tr-IH|
    }
    @tr-step{
      @${\tagof{\tau'} \subkeq \tagof{\tau}}
      @|K-subt-preservation|
    }
    @tr-step{
      @${\Gamma \wellKE e' : \tagof{\tau}}
      (2)
    }
    @tr-qed{
      by (1, 3)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                 \Gamma \wellM e
               }{
                 \Gamma \wellM \edyn{\tau}{e} : \tau
               }}]{
    @tr-step{
      @${\Gamma \wellM e \carrow e'
         @tr-and[]
         \Gamma \wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${\Gamma \wellM \edyn{\tau}{e} : \tau \carrow \edyn{\tau}{e'}}
      (1)
    }
    @tr-step{
      @${\Gamma \wellKE \edyn{\tau}{e'} : \tagof{\tau}}
      (1)
    }
    @tr-qed{
      by (2, 3)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-completion" @elem{@${\carrow} dynamic soundness}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellM e \carrow e'} and @${\Gamma \wellKE e'}
}@tr-proof{
  By induction on the structure of @${\Gamma \wellM e}.

  @tr-case[#:box? #true
           @${\inferrule*{
                x \in \Gamma
              }{
                \Gamma \wellM x
              }}]{
    @tr-step{
      @${\Gamma \wellM x \carrow x}
    }
    @tr-step{
      @${\Gamma \wellKE x}
      @${x \in \Gamma}
    }
    @tr-qed{
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e
              }{
                \Gamma \wellM \vlam{x}{e}
              }}]{
    @tr-step{
      @${x,\Gamma \wellM e \carrow e'
         @tr-and[]
         x,\Gamma \wellKE e'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM \vlam{x}{e} \carrow \vlam{x}{e'}}
      (1)
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{x}{e'}}
      (1)
    }
    @tr-case{
      by (2, 3)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i
              }}]{
    @tr-step{
      @${\Gamma \wellM i \carrow i}
    }
    @tr-step{
      @${\Gamma \wellKE i}
    }
    @tr-qed{
    }
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
      @${\Gamma \wellM e_0 \carrow e_0'
         @tr-and[]
         \Gamma \wellKE e_0'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 \carrow e_1'
         @tr-and[]
         \Gamma \wellKE e_1'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM \vpair{e_0}{e_1} \carrow \vpair{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-qed{
      by (3, 4)
    }
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
      @${\Gamma \wellM e_0 \carrow e_0'
         @tr-and[]
         \Gamma \wellKE e_0'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 \carrow e_1'
         @tr-and[]
         \Gamma \wellKE e_1'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM \vapp{e_0}{e_1} \carrow \vapp{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \vapp{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-qed{
      by (3, 4)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e
              }{
                \Gamma \wellM \vunop~e
              }}]{
    @tr-step{
      @${\Gamma \wellM e \carrow e'
         @tr-and[]
         \Gamma \wellKE e'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM \eunop{e} \carrow \eunop{e'}}
      (1)
    }
    @tr-step{
      @${\Gamma \wellKE \eunop{e'}}
      (1)
    }
    @tr-qed{
      by (2, 3)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0
                \\
                \Gamma \wellM e_1
              }{
                \Gamma \wellM \vbinop~e_0~e_1
              }}]{
    @tr-step{
      @${\Gamma \wellM e_0 \carrow e_0'
         @tr-and[]
         \Gamma \wellKE e_0'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM e_1 \carrow e_1'
         @tr-and[]
         \Gamma \wellKE e_1'}
      @|tr-IH|
    }
    @tr-step{
      @${\Gamma \wellM \ebinop{e_0}{e_1} \carrow \ebinop{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{e_0'}{e_1'}}
      (1, 2)
    }
    @tr-qed{
      by 3,4
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau
              }{
                \Gamma \wellM \esta{\tau}{e}
              }}]{
    @tr-step{
      @${\Gamma \wellM e : \tau \carrow e'
         @tr-and[]
         \Gamma \wellKE e' : \tagof{\tau}}
      @|K-S-completion|
    }
    @tr-step{
      @${\Gamma \wellM \esta{\tau}{e} \carrow \esta{\tau}{e'}}
      (1)
    }
    @tr-step{
      @${\Gamma \wellKE \esta{\tau}{e}}
      (1)
    }
    @tr-qed{
      by 2,3
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-progress" @elem{@${\langK} static progress}]{
  If @${\wellKE e : K} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccKS e'} }
    @item{ @${e \ccKS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccKD \tagerror} }
]}@tr-proof{
  By the @|K-S-uec| lemma,
   there are seven cases.

  @tr-case[@${e \eeq v}]{
    @tr-qed{}
  }

  @tr-case[@${e \eeq \ctxE{v_0~v_1}}]{
    @tr-step[
      @${\wellKE v_0~v_1 : K'}
      @|K-S-hole-typing|]
    @tr-step{
      @${\wellKE v_0 : \kfun}
      @|K-S-inversion| (1)}
    @tr-step{
      @${v_0 \eeq \vlam{x}{e'} @tr-or[] v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}}
      @|K-S-canonical| (2)}
    @list[
      @tr-if[@${v_0 \eeq \vlam{x}{e'}}]{
        @tr-step[
          @${e \ccKS \ctxE{\edyn{\kany}{(\vsubst{e'}{x}{v_1})}}}
          @${\vapp{(\vlam{x}{e'})}{v_1} \rrKS (\edyn{\kany}{(\vsubst{e'}{x}{v_1})})}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}
                @tr-and[2]
                \mchk{\tagof{\tau_d}}{v_1} = v_1}]{
        @tr-step[
          @${e \ccKS \ctxE{\vsubst{e'}{x}{v_1}}}
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}
                  @tr-and[4]
                  \mchk{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccKS \boundaryerror}
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \boundaryerror}]
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\eunop{v}}}]{
    @${\vunop \eeq \vfst @tr-or[] \vunop \eeq \vsnd}
    @tr-step[
      @${\wellKE \eunop{v} : K'}
      @|K-S-hole-typing|]
    @tr-step{
      @${\wellKE v : \kpair}
      @|K-S-inversion| (2)}
    @tr-step{
      @${v \eeq \vpair{v_0}{v_1}}
      @|K-S-canonical| (3)}
    @tr-step{
      @${\delta(\vunop, v) = v_i \mbox{ where } i \in \{0,1\}}
      (1, 3)}
    @tr-step{
      @${e \ccKS \ctxE{v_i}}
      @${(\eunop{v}) \rrKS v_i}}
    @tr-qed[]
  }

  @tr-case[@${e \eeq \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-step{
      @${\wellKE \ebinop{v_0}{v_1} : K'}
      @|K-S-hole-typing|}
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[] \wellKE v_1 : K_1
         @tr-and[] \Delta(\vbinop, K_0, K_1) = K_2}
      @|K-S-inversion| (1)}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = A}
      @|K-Delta-soundness|}
    @tr-qed{
      by @${e \ccKS \ctxE{A}} if @${A \in e}
      @linebreak[]
      and by @${e \ccKS A} otherwise}
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\tau}{e'}}}
           #:itemize? #false ]{
    @tr-if[@${e' \in v}
           #:itemize? #false ]{
      @tr-if[@${\mchk{\tagof{\tau}}{e'} = e'}]{
        @tr-step[
          @${e \ccKS \ctxE{e'}}
          @${(\edyn{\tau}{e'}) \rrKS e'}]
        @tr-qed[]
      }
      @tr-else[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @tr-step[
          @${e \ccKS \boundaryerror}
          @${(\edyn{\tau}{e'}) \rrKS \boundaryerror}]
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccKD A}
        @|K-D-progress|
      ]
      @tr-qed{
        by @${e \ccKS \ctxE{\edyn{\tau}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccKS A} otherwise}
    }
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\kany}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v}]{
      @tr-step[
        @${e \ccKS \ctxE{v}}
        @${(\edyn{\kany}{v}) \rrKS v}]
      @tr-qed[]}
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccKD A}
        @|K-D-progress|]
      @tr-qed{
        by @${e \ccKS \ctxE{\edyn{\kany}{A}}} if @${A \in e}
        @linebreak[]
        and by @${e \ccKS A} otherwise}
    }
  }

  @tr-case[@${e \eeq \ctxE{\echk{K}{v}}} #:itemize? #f]{
    @tr-if[@${\mchk{K}{v} = v}]{
      @tr-step[
        @${e \ccKS \ctxE{v}}
        @${(\echk{K}{v}) \rrKS v}]
      @tr-qed[]
    }
    @tr-else[@${\mchk{K}{v} = \boundaryerror}]{
      @tr-step[
        @${e \ccKS \boundaryerror}
        @${(\echk{K}{v}) \rrKS \boundaryerror}]
      @tr-qed[]
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-progress" @elem{@${\langK} dynamic progress}]{
  If @${\wellKE e} then either @${e} is a value or @${e \ccKD A}.
}@tr-proof{
  By the @|K-D-uec| lemma, there are six cases.

  @tr-case[@${e \eeq v}]{
    @tr-qed[]
  }

  @tr-case[@${e \eeq \ctxE{v_0~v_1}}]{
    @tr-if[@${v_0 \eeq \vlam{x}{e_0}}]{
      @tr-step[
        @${e \ccKD \ctxE{\vsubst{e_0}{x}{v_1}}}
        @${(\vlam{x}{e_0})~v_1 \rrKD \vsubst{e_0}{x}{v_1}}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e_0}
              @tr-and[2]
              \mchk{\tagof{\tau_d}}{v_1} = v_1}]{
      @tr-step[
        @${e \ccKD \ctxE{\esta{\kany}{(\vsubst{e_0}{x}{v_1})}}}
        @${(\vlam{\tann{x}{\tau_d}}{e_0})~v_1 \rrKD (\esta{\kany}{\vsubst{e_0}{x}{v_1}})}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e_0}
              @tr-and[2]
              \mchk{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
      @tr-step[
        @${e \ccKD \boundaryerror}
        @${(\vlam{\tann{x}{\tau_d}}{e_0})~v_1 \rrKD \boundaryerror}]
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step[
        @${e \ccKD \tagerror}
        @${v_0~v_1 \rrKD \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}} #:itemize? #f]{
    @tr-if[@${\delta(\vunop, v) = v'}]{
      @tr-step[
        @${e \ccKD \ctxE{v'}}
        @${(\eunop{v}) \rrKD v'}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step[
        @${e \ccKD \tagerror}
        @${(\eunop{v}) \rrKD \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = A}]{
      @tr-qed{
        by @${e \ccKD \ctxE{A}} if @${A \in e}
        and by @${e \ccKD A} otherwise}
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step[
        @${e \ccKD \tagerror}
        @${(\ebinop{v_0}{v_1}) \rrKD \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e \eeq \ctxE{\esta{\tau}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v} #:itemize? #f]{
      @tr-if[@${\mchk{\tagof{\tau}}{e'} = e'}]{
        @tr-step[
          @${e \ccKD \ctxE{e'}}
          @${(\esta{\tau}{e'}) \rrKD e'}]
        @tr-qed[]
      }
      @tr-else[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @tr-step[
          @${e \ccKD \boundaryerror}
          @${(\esta{\tau}{e'}) \rrKD \boundaryerror}]
        @tr-qed[]
      }
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccKS A}
        @|K-S-progress|]
      @tr-qed{by @${e \ccKD \ctxE{\esta{\tau}{A}}} if @${A \in e}
        @linebreak[] and by @${e' \ccKD A} otherwise}
    }
  }

  @tr-case[@${e \eeq \ctxE{\esta{\kany}{e'}}} #:itemize? #f]{
    @tr-if[@${e' \in v}]{
      @tr-step[
        @${e \ccKD \ctxE{e'}}
        @${(\esta{\kany}{e'}) \rrKD e'}
      ]
      @tr-qed[]
    }
    @tr-else[@${e' \not\in v}]{
      @tr-step[
        @${e' \ccKS A}
        @|K-S-progress|]
      @tr-qed{by @${e \ccKD \ctxE{\esta{\kany}{A}}} if @${A \in e}
        @linebreak[] and by @${e \ccKD A} otherwise}
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-preservation" @elem{@${\langK} static preservation}]{
  If @${\wellKE e : K} and @${e \ccKS e'} then @${\wellKE e' : K}
}@tr-proof{
  By the @|K-S-uec| lemma, there are six cases to consider.

  @tr-case[@${e = \ctxE{v_0~v_1}}]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccKS \ctxE{\edyn{\kany}{\vsubst{e'}{x}{v_1}}}}]{
      @tr-step{
        @${\wellKE v_0~v_1 : \kany}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\wellKE v_0 : \kfun @tr-and[] \wellKE v_1 : \kany}
        @|K-S-inversion|
      }
      @tr-step{
        @${x \wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE v_1}
        @|K-S-value-inversion| (2)
      }
      @tr-step{
        @${\wellKE \vsubst{e'}{x}{v_1}}
        @|K-DD-subst| (3, 4)
      }
      @tr-step{
        @${\wellKE \edyn{\kany}{(\vsubst{e'}{x}{v_1})} : \kany}
        (5)
      }
      @tr-qed{
        by @|K-S-hole-subst|
      }
    }
    @tr-else[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
                @tr-and[4]
                e \ccKS \ctxE{\vsubst{e'}{x}{\mchk{\tagof{\tau}}{v_1}}}}]{
      @tr-step{
        @${\wellKE v_0~v_1 : \kany}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\wellKE v_0 : \kfun @tr-and[] \wellKE v_1 : \kany}
        @|K-S-inversion| (1)
      }
      @tr-step{
        @${\tann{x}{\tau} \wellKE e' : \kany}
        @|K-S-inversion| (2)}
      @tr-step{
        @${\wellKE \mchk{\tagof{\tau}}{v_1} : \tagof{\tau}}
        @|K-check| (2)}
      @tr-step{
        @${\wellKE \vsubst{e}{x}{\mchk{\tagof{\tau}}{v_1}} : \kany}
        @|K-SS-subst| (3, 4)}
      @tr-qed{
        by @|K-S-hole-subst|
      }
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}
              @tr-and[4]
              \delta(\vunop, v) = v'
              @tr-and[4]
              e \ccKS \ctxE{v'}}]{
    @tr-step{
      @${\wellKE \eunop{v} : \kany}
      @|K-S-hole-typing|
    }
    @tr-step{
      @${\wellKE v : \kpair}
      @|K-S-inversion|
    }
    @tr-step{
      @${v = \vpair{v_0}{v_1}}
      @|K-S-canonical|
    }
    @tr-step{
      @${\wellKE v_0 : \kany @tr-and[] \wellKE v_1 : \kany}
      @|K-S-inversion| (2, 3)
    }
    @tr-step{
      @${v' = v_0 @tr-or[] v' = v_1}
      @${\delta(\vfst, v) = v_0 @tr-and[] \delta(\vsnd, v) = v_1}
    }
    @tr-qed{
      by @|K-S-hole-subst| (5)
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v
              @tr-and[4]
              e \ccKS \ctxE{v}}]{
    @tr-step{
      @${\wellKE \ebinop{v_0}{v_1} : K'}
      @|K-S-hole-typing|
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE v_1 : K_1
         @tr-and[]
         \Delta(\vbinop, K_0, K_1) = K''
         @tr-and[]
         K'' \subk K'}
      @|K-S-inversion| (1)
    }
    @tr-step{
      @${\wellKE v : K''}
      @|K-Delta-soundness| (3)
    }
    @tr-step{
      @${\wellKE v : K'}
      (2, 3)
    }
    @tr-qed{
      by @|K-S-hole-subst| (4)
    }
  }

  @tr-case[@${e = \ctxE{\edyn{\tau}{e'}}} #:itemize? #f]{
    @tr-if[@${\ctxE{\edyn{\tau}{e'}} \ccKS \ctxE{\edyn{\tau}{e''}}}]{
      @tr-step[
        @${\wellKE \edyn{\tau}{e'} : K'}
        @|K-S-hole-typing|]
      @tr-step[
        @${\wellKE e'
           @tr-and[]
           \tagof{\tau} \subkeq K'}
        @|K-S-inversion|]
      @tr-step[
        @${\wellKE e''}
        @|K-D-preservation|]
      @tr-step{
        @${\wellKE \edyn{\tau}{e''} : K'}
        (2, 3)}
      @tr-qed{
        by @|K-S-hole-subst|}
    }
    @tr-else[@${\ctxE{\edyn{\tau}{v}} \ccKS \ctxE{v}
                @tr-and[]
                \mchk{\tagof{\tau}}{v} = v}]{
      @tr-step{
        @${\wellKE \edyn{\tau}{v} : K'}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\tagof{\tau} \subk K'}
        @|K-S-inversion|
      }
      @tr-step{
        @${\wellKE v : \tagof{\tau}}
        @${\mchk{\tagof{\tau}}{v} = v}
      }
      @tr-qed{
        by (2, 3, @|K-S-hole-subst|)
      }
    }
  }

  @tr-case[@${e = \ctxE{\edyn{\kany}{e'}}} #:itemize? #f]{
    @tr-if[@${\ctxE{\edyn{\kany}{e'}} \ccKS \ctxE{\edyn{\kany}{e''}}}]{
      @tr-step{
        @${\wellKE \edyn{\kany}{e'} : \kany}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion|
      }
      @tr-step{
        @${\wellKE e''}
        @|K-D-preservation|
      }
      @tr-step{
        @${\wellKE \edyn{\kany}{e''} : \kany}
        (3)
      }
      @tr-qed{
        by (4, @|K-S-hole-subst|)
      }
    }
    @tr-else[@${\ctxE{\edyn{\kany}{v}} \ccKS \ctxE{v}}]{
      @tr-step{
        @${\wellKE \edyn{\kany}{v} : \kany}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\wellKE v}
        @|K-S-inversion|
      }
      @tr-step{
        @${\wellKE v : \kany}
        @|K-D-value-inversion|
      }
      @tr-qed{
        by @|K-S-hole-subst|}
    }
  }

  @tr-case[@${e = \ctxE{\echk{K'}{v}}}]{
    @tr-step{
      @${\ctxE{\echk{K'}{v}} \ccKS \ctxE{v}}
    }
    @tr-step{
      @${\wellKE \echk{K'}{v} : K''}
      @|K-S-hole-typing|
    }
    @tr-step{
      @${K' \subkeq K''}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE v : K'}
      @${\mchk{K'}{v} = v}
    }
    @tr-qed{
      by (3, 4, @|K-S-hole-subst|)
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-preservation" @elem{@${\langK} dynamic preservation}]{
  If @${\wellKE e} and @${e \ccKD e'} then @${\wellKE e'}
}@tr-proof{
  By @|K-D-uec| there are five cases.

  @tr-case[@${e = \ctxE{v_0~v_1}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}
              @tr-and[2]
              e \ccKD \ctxE{\vsubst{e'}{x}{v_1}}}]{
      @tr-step{
        @${\wellKE v_0~v_1}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE v_0
           @tr-and[]
           \wellKE v_1}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${x \wellKE e'}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE \vsubst{e'}{x}{v_1}}
        @|K-DD-subst| (2, 3)
      }
      @tr-qed{
        by @|K-D-hole-subst|
      }
    }

    @tr-else[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
                @tr-and[4]
                e \ccKD \ctxE{\esta{\kany}{(\vsubst{e'}{x}{\mchk{\tagof{\tau}}{v_1}})}}}]{
      @tr-step{
        @${\wellKE v_0~v_1}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE v_0
           @tr-and[]
           \wellKE v_1}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${\tann{x}{\tau} \wellKE e : \kany}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE \mchk{\tagof{\tau}}{v_1} : \tagof{\tau}}
        @|K-check| (2)}
      @tr-step{
        @${\wellKE \vsubst{e}{x}{\mchk{\tagof{\tau}}{v_1}} : \kany}
        @|K-SS-subst| (3, 4)
      }
      @tr-step{
        @${\wellKE \esta{\kany}{(\vsubst{e}{x}{\mchk{\tagof{\tau}}{v_1}})}}
        (5)
      }
      @tr-qed{
        by @|K-D-hole-subst| (6)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eunop{v}}
              @tr-and[4]
              \delta(\vunop, v) = v'
              @tr-and[4]
              e \ccKD \ctxE{v'}}]{
    @tr-step{
      @${\wellKE \eunop{v}}
      @|K-D-hole-typing|
    }
    @tr-step{
      @${\wellKE v}
      @|K-D-inversion| (1)
    }
    @tr-step{
      @${\wellKE v'}
      @|K-delta-preservation| (2)
    }
    @tr-qed{
      by @|K-D-hole-subst| (3)
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = v'
              @tr-and[4]
              e \ccKD \ctxE{v'}}]{
    @tr-step{
      @${\wellKE \ebinop{v_0}{v_1}}
      @|K-D-hole-typing|
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE v_1}
      @|K-D-inversion| (1)
    }
    @tr-step{
      @${\wellKE v'}
      @|K-delta-preservation| (2)
    }
    @tr-qed{
      by @|K-D-hole-subst| (3)
    }
  }

  @tr-case[@${e = \ctxE{\esta{\tau}{e'}}} #:itemize? #false]{
    @tr-if[@${\ctxE{\esta{\tau}{e'}} \ccKD \ctxE{\esta{\tau}{e''}}}]{
      @tr-step{
        @${\wellKE \esta{\tau}{e'}}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE e' : \tagof{\tau}}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${\wellKE e'' : \tagof{\tau}}
        @|K-S-preservation| (2)
      }
      @tr-step{
        @${\wellKE \esta{\tau}{e''}}
        (3)
      }
      @tr-qed{
        by @|K-D-hole-subst| (4)
      }
    }

    @tr-else[@${\ctxE{\esta{\tau}{v}} \ccKD \ctxE{v}}]{
      @tr-step{
        @${\wellKE \esta{\tau}{v}}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE v : \tagof{\tau}}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${\wellKE v}
        @|K-S-value-inversion| (2)
      }
      @tr-qed{
        by @|K-D-hole-subst| (3)
      }
    }
  }

  @tr-case[@${e = \ctxE{\esta{\kany}{e'}}} #:itemize? #f]{
    @tr-if[@${\ctxE{\esta{\kany}{e'}} \ccKD \ctxE{\esta{\kany}{e''}}}]{
      @tr-step{
        @${\wellKE \esta{\kany}{e'}}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${\wellKE e'' : \kany}
        @|K-S-preservation| (2)
      }
      @tr-step{
        @${\wellKE \esta{\kany}{e''}}
        (3)
      }
      @tr-qed{
        by @|K-D-hole-subst| (4)
      }
    }

    @tr-else[@${\ctxE{\esta{\kany}{v}} \ccKD v}]{
      @tr-step{
        @${\wellKE \esta{\kany}{v}}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE v : \kany}
        @|K-D-inversion| (1)
      }
      @tr-step{
        @${\wellKE v}
        @|K-S-value-inversion| (2)
      }
      @tr-qed{
        by @|K-D-hole-subst| (3)
      }
    }
  }

}

@; -----------------------------------------------------------------------------

@tr-lemma[#:key "K-pure-static-progress" @elem{pure static progress}]{
  If @${\wellM e : \tau} and @${e} is purely static, then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccKS e'} }
    @item{ @${e \ccKS \boundaryerror} }
  ]
}@tr-proof{
  By the @|M-uec| lemma, there are five cases.

  @tr-case[@${e \eeq v}]{
    @tr-qed{}
  }

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau'}}{e'}}]{
      @tr-step[
        @${e \ccKS \ctxE{\vsubst{e'}{x}{v_1}}}
        @${\vapp{v_0}{v_1} \rrKS \vsubst{e'}{x}{v_1}}]
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
        @${e \ccKS \ctxE{v'}}
        @${(\eunop{v}) \rrKS v'}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = v'}]{
      @tr-step[
        @${e \ccKS \ctxE{v'}}
        @${(\ebinop{v_0}{v_1}) \rrKS v'}]
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step[
        @${e \ccKS \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrKS \boundaryerror}]
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e \eeq \ctxE{\edyn{\tau}{e'}}}]{
    @tr-contradiction{@${e} is purely static}
  }

}

@tr-lemma[#:key "K-pure-static-preservation" @elem{@${\langK} pure static preservation}]{
  If @${\wellM e : \tau} and @${e} is purely static and @${e \ccKS e'}
  then @${\wellM e' : \tau} and @${e'} is purely static.
}@tr-proof{
  By the @|M-uec| lemma, there are four cases.

  @tr-case[@${e = \ctxE{\vapp{v_0}{v_1}}}]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_d}}{e'}}]{
      @tr-step[
        @${\ctxE{v_0~v_1} \ccKS \ctxE{\vsubst{e'}{x}{v_1}}}]
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
      @${\ctxE{\eunop{v}} \ccKS \ctxE{v'}
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
      @${\ctxE{\ebinop{v_0}{v_1}} \ccKS \ctxE{v'}
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

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-check" @elem{@${\mchk{\cdot}{\cdot}} soundness}]{
  If @${\mchk{K}{v} = v}
   @linebreak[]
   then @${\wellKE v : K}
}@tr-proof{
  @tr-qed{by definition of @${\mchk{K}{v}}}
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-uec" @elem{@${\langK} unique static evaluation contexts}]{
  If @${\wellKE e : K} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{e'}}} }
    @item{ @${e = \ctxE{\edyn{\kany}{e'}}} }
    @item{ @${e = \ctxE{\echk{K}{v}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction[@${\wellKE e : K}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @tr-qed{@${e} is a value}
  }

  @tr-case[@${e = \esta{\tau}{e'}
              @tr-or[4]
              e = \esta{\kany}{e'}}]{
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

  @tr-case[@${e = \edyn{\kany}{e_0}}]{
    @${\ED = \ehole}
    @tr-qed{
      @${e = \ctxE{\edyn{\kany}{e_0}}}
    }
  }

  @tr-case[@${e = \echk{K}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \echk{K}{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{@${e = \ctxE{\echk{K}{e_0}}}}
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-uec" @elem{@${\langK} unique dynamic evaluation contexts}]{
  If @${\wellKE e} then either:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\esta{\tau}{e'}}} }
    @item{ @${e = \ctxE{\esta{\kany}{e'}}} }
  ]
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-contradiction[@${\wellKE e}]
  }

  @tr-case[@${e = i
              @tr-or[4]
              e = \vlam{x}{e'}
              @tr-or[4]
              e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @tr-qed{@${e} is a value}
  }

  @tr-case[@${e = \edyn{\tau}{e'}
              @tr-or[4]
              e = \edyn{\kany}{e'}
              @tr-or[4]
              e = \echk{K}{e'}}]{
    @tr-contradiction[@${\wellKE e}]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
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
      @tr-step{@${\ED = \ehole}}
      @tr-qed{@${e = \ctxE{\vpair{e_0}{e_1}}}}
    }
  }

  @tr-case[@${e = e_0~e_1} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
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
      @tr-qed{
        @${e = \ctxE{e_1'}}
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

  @tr-case[@${e = \esta{\tau}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
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
      @tr-qed{
        @${e = \ctxE{\esta{\tau}{e_0}}}
      }
    }
  }

  @tr-case[@${e = \esta{\kany}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ED = \esta{\kany}{\ED_0}}
      }
      @tr-qed{
        @${e = \ctxE{e_0'}}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ED = \ehole}
      @tr-qed{
        @${e = \ctxE{\esta{\kany}{e_0}}}
      }
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-hole-typing" @elem{@${\langK} static hole typing}]{
  If @${\wellKE \ctxE{e} : K} then the typing derivation contains a sub-term
   @${\wellKE e : K'} for some @${K'}.
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
      @${\wellKE \ED_0[e] : \kfun}
      @|K-S-inversion|
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
      @${\wellKE \ED_1[e] : \kany}
      @|K-S-inversion|
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
      @${\wellKE \ED_0[e] : \kany}
      @|K-S-inversion|
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
      @${\wellKE \ED_1[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \eunop{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : \kpair}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellKE \ED_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \echk{K}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \echk{K}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-hole-typing" @elem{@${\langK} dynamic hole typing}]{
  If @${\wellKE \ctxE{e}} then the derivation contains a sub-term @${\wellKE e}
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
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = v_0~\ED_1}]{
    @tr-step{
      @${\ctxE{e} = v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vpair{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \vpair{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \eunop{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @tr-step{
      @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ED = \echk{K}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \echk{K}{\ED_0[e]}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-hole-subst" @elem{@${\langK} static hole substitution}]{
  If @${\wellKE \ctxE{e} : K} and contains @${\wellKE e : K'}, and furthermore @${\wellKE e' : K'},
  then @${\wellKE \ctxE{e'} : K}
}@tr-proof{
  By induction on the structure of @${\ED}.

  @tr-case[@${\ED = \ehole}]{
    @tr-step{
      @${\ctxE{e} = e
         @tr-and[]
         \ctxE{e'} = e'}
    }
    @tr-step{
      @${\wellKE e : K}
      (1)
    }
    @tr-step{
      @${K' = K}
    }
    @tr-qed{ }
  }

  @tr-case[@${\ED = \vpair{\ED_0}{e_1}}]{
    @tr-step{
      @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}
        @tr-and[]
        \ctxE{e'} = \vpair{\ED_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellKE \vpair{\ED_0[e]}{e_1} : K}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{\ED_0[e']}{e_1} : K}
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
      @${\wellKE \vpair{v_0}{\ED_1[e]} : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ED_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ED_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{v_0}{\ED_1[e']} : K}
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
      @${\wellKE \ED_0[e]~e_1 : K}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ED_0[e']~e_1 : K}
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
      @${\wellKE v_0~\ED_1[e] : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ED_1[e] : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ED_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE v_0~\ED_1[e'] : K}
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
      @${\wellKE \eunop{\ED_0[e]} : K}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \eunop{\ED_0[e']} : K}
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
      @${\wellKE \ebinop{\ED_0[e]}{e_1} : K}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ED_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{\ED_0[e']}{e_1} : K}
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
      @${\wellKE \ebinop{v_0}{\ED_1[e]} : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ED_1[e] : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ED_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{v_0}{\ED_1[e']} : K}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \echk{K_c}{\ED_0}}]{
    @tr-step{
      @${\ctxE{e} = \echk{K_c}{\ED_0[e]}
        @tr-and[]
        \ctxE{e'} = \echk{K_c}{\ED_0[e']}}
    }
    @tr-step{
      @${\wellKE \echk{K_c}{\ED_0[e]} : K}
    }
    @tr-step{
      @${\wellKE \ED_0[e] : K_0}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ED_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \echk{K_c}{\ED_0[e']} : K}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-hole-subst" @elem{@${\langK} dynamic hole substitution}]{
  If @${\wellKE \ctxE{e}} and @${\wellKE e'} then @${\wellKE \ctxE{e'}}
}
@tr-proof{
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
      @${\wellKE \vpair{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{\ED_0[e']}{e_1}}
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
      @${\wellKE \vpair{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{v_0}{\ED_1[e']}}
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
      @${\wellKE \ED_0[e]~e_1}
    }
    @tr-step{
      @${\wellKE \ED_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ED_0[e']~e_1}
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
      @${\wellKE v_0~\ED_1[e]}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE v_0~\ED_1[e']}
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
      @${\wellKE \eunop{\ED_0[e]}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \eunop{\ED_0[e']}}
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
      @${\wellKE \ebinop{\ED_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ED_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{\ED_0[e']}{e_1}}
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
      @${\wellKE \ebinop{v_0}{\ED_1[e]}}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ED_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ED_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{v_0}{\ED_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ED = \echk{K_c}{\ED_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e}}
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-inversion" @elem{@${\langK} static inversion}]{
  @itemlist[
    @item{
      If @${\wellKE \vpair{e_0}{e_1} : K} then
       @${\wellKE e_0 : \kany} and
       @${\wellKE e_1 : \kany}
    }
    @item{
      If @${\wellKE \vlam{x}{e} : K} then
       @${x \wellKE e}
    }
    @item{
      If @${\wellKE \vlam{\tann{x}{\tau}}{e} : K} then
       @${\tann{x}{\tau} \wellKE e : \kany}
    }
    @item{
      If @${\wellKE e_0~e_1 : K} then
       @${K = \kany} and
       @${\wellKE e_0 : \kfun} and
       @${\wellKE e_1 : \kany}
    }
    @item{
      If @${\wellKE \eunop{e_0} : K} then
       @${K = \kany} and
       @${\wellKE e_0 : \kpair}
    }
    @item{
      If @${\wellKE \ebinop{e_0}{e_1} : K} then
       @${\wellKE e_0 : K_0} and
       @${\wellKE e_1 : K_1} and
       @${\Delta(\vbinop, K_0, K_1) = K'} and
       @${K' \subk K}
    }
    @item{
      If @${\wellKE \edyn{\tau}{e} : K} then
       @${\wellKE e} and
       @${\tagof{\tau} \subkeq K}
    }
    @item{
      If @${\wellKE \echk{K'}{e_0} : K} then
       @${\wellKE e_0 : \kany} and
       @${K' \subkeq K}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellKE e : \tau} and by @|K-finite-subtyping|
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-inversion" @elem{@${\langK} dynamic inversion}]{
  @itemlist[
    @item{
      If @${\wellKE \vpair{e_0}{e_1}} then
       @${\wellKE e_0} and
       @${\wellKE e_1}
    }
    @item{
      If @${\wellKE \vlam{x}{e}} then
       @${x \wellKE e}
    }
    @item{
      If @${\wellKE \vlam{\tann{x}{\tau}}{e}} then
       @${\tann{x}{\tau} \wellKE e : \kany}
    }
    @item{
      If @${\wellKE e_0~e_1} then
       @${\wellKE e_0} and
       @${\wellKE e_1}
    }
    @item{
      If @${\wellKE \eunop{e_0}} then
       @${\wellKE e_0}
    }
    @item{
      If @${\wellKE \ebinop{e_0}{e_1}} then
       @${\wellKE e_0} and
       @${\wellKE e_1}
    }
    @item{
      If @${\wellKE \esta{\tau}{e}} then
       @${\wellKE e : \tagof{\tau}}
    }
    @item{
      If @${\wellKE \esta{\kany}{e}} then
       @${\wellKE e : \kany}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\wellKE e}.
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-canonical" @elem{@${\langK} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellKE v : \kpair}
      then @${v \eeq \vpair{v_0}{v_1}}
    }
    @item{
      If @${\wellKE v : \kfun}
      then @${v \eeq \vlam{x}{e'} \mbox{ or } v \eeq \vlam{\tann{x}{\tau_d}}{e'}}
    }
    @item{
      If @${\wellKE v : \kint}
      then @${v \eeq i}
    }
    @item{
      If @${\wellKE v : \knat}
      then @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellKE \cdot : K}
  }

  @; more like ... if you look at all the rules for wellKE
  @;  then you see there's only one that applies for each value form,
  @;  and the premises of that rule establish what we want to know
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-Delta-soundness" @elem{@${\Delta} tag soundness}]{
  If @${\wellKE v_0 : K_0 \mbox{ and }
        \wellKE v_1 : K_1 \mbox{ and }
        \Delta(\vbinop, K_0, K_1) = K}
  then either:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellKE v : K}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof{
  By case analysis on @${\Delta}.

  @tr-case[@${\Delta(\vsum, \knat, \knat) = \knat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|K-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 \in \naturals}
    }
    @tr-qed{ }
  }

  @tr-case[@${\Delta(\vsum, \kint, \kint) = \kint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|K-S-canonical|
    }
    @tr-step{
      @${\delta(\vsum, i_0, i_1) = i_0 + i_1 \in i}
    }
    @tr-qed{ }
  }

  @tr-case[@${\Delta(\vquotient, \knat, \knat) = \knat}]{
    @tr-step{
      @${v_0 = i_0, i_0 \in \naturals
         @tr-and[]
         v_1 = i_1, i_1 \in \naturals}
      @|K-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1} \in \naturals }}
        @tr-qed{}
      }
    ]
  }

  @tr-case[@${\Delta(\vquotient, \kint, \kint) = \kint}]{
    @tr-step{
      @${v_0 = i_0
         @tr-and[]
         v_1 = i_1}
      @|K-S-canonical|
    }
    @list[
      @tr-if[@${i_1 = 0}]{
        @tr-qed{
          by @${\delta(\vquotient, i_0, i_1) = \boundaryerror} }
      }
      @tr-else[@${i_1 \neq 0}]{
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \floorof{i_0 / i_1}} \in i }
        @tr-qed{}
      }
    ]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellKE v} and @${\delta(\vunop, v) = v'} then @${\wellKE v'}
    }
    @item{
      If @${\wellKE v_0} and @${\wellKE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellKE v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellKE v_0}
      @|K-D-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellKE v_1}
      @|K-D-inversion|
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
@; TODO better name ... was thinking "preserve/reflect"
@tr-lemma[#:key "K-Delta-tag-preservation" @elem{@${\Delta} preservation}]{
  If @${\Delta(\vbinop, \tau_0, \tau_1) = \tau} then
     @${\Delta(\vbinop, \tagof{\tau_0}, \tagof{\tau_1}) = \tagof{\tau}}.
}@tr-proof{
  By case analysis on the definition of @${\Delta}

  @tr-case[@${\Delta(\vbinop, \tnat, \tnat) = \tnat}]{
    @tr-qed{
      by @${\tagof{\tnat} = \tnat}
    }
  }

  @tr-case[@${\Delta(\vbinop, \tint, \tint) = \tint}]{
    @tr-qed{
      by @${\tagof{\tint} = \tint}
    }
  }
}

@tr-lemma[#:key "K-Delta-inversion" @elem{@${\Delta} inversion}]{
  @itemlist[
    @item{
      If @${\Delta(\vfst, \tau) = \tau'} then @${\tau = \tpair{\tau_0}{\tau_1}} and @${\tau' = \tau_0}
    }
    @item{
      If @${\Delta(\vsnd, \tau) = \tau'} then @${\tau = \tpair{\tau_0}{\tau_1}} and @${\tau' = \tau_1}
    }
  ]
}@tr-proof{
  @tr-qed{by the definition of @${\Delta}}
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-subt-preservation" @elem{@${\subk} preservation}]{
  If @${\tau \subt \tau'} then
   @${\tagof{\tau} \subkeq \tagof{\tau'}}
}@tr-proof{
  By case analysis on the last rule used to show @${\tau \subt \tau'}.

  @tr-case[@${\tnat \subt \tint}]{
    @tr-qed[@${\tagof{\tnat} \subk \tagof{\tint}}]
  }

  @tr-case[@${\tarr{\tau_d}{\tau_c} \subt \tarr{\tau_d'}{\tau_c'}}]{
    @tr-step{
      @${\tagof{\tarr{\tau_d}{\tau_c}} = \kfun
         @tr-and[]
         \tagof{\tarr{\tau_d'}{\tau_c'}} = \kfun}
    }
    @tr-qed[]
  }

  @tr-case[@${\tpair{\tau_0}{\tau_1} \subt \tpair{\tau_0'}{\tau_1'}}]{
    @tr-step{
      @${\tagof{\tpair{\tau_0}{\tau_1}} = \kpair
         @tr-and[]
         \tagof{\tpair{\tau_0'}{\tau_1'}} = \kpair}
    }
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-value-inversion" @elem{@${\langK} static value inversion}]{
  If @${\wellKE v : \kany} then @${\wellKE v}
}@tr-proof{
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
@tr-lemma[#:key "K-D-value-inversion" @elem{@${\langK} dynamic value inversion}]{
  If @${\wellKE v} then @${\wellKE v : \kany}
}@tr-proof{
  By induction on the structure of @${v}.

  @tr-case[@${v = i}]{
    @tr-step{
      @${\wellKE v : \kint}
    }
    @tr-qed{
      by @${\kint \subk \kany}
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
      by @${\kpair \subk \kany}
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
      by @${\kfun \subk \kany}
    }
  }

  @tr-case[@${v = \vlam{\tann{x}{\tau}}{e}}]{
    @tr-step{
      @${\tann{x}{\tau} \wellKE e : \kany}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \vlam{\tann{x}{\tau}}{e} : \kfun}
      (1)
    }
    @tr-qed{
      by @${\kfun \subk \kany}
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-SS-subst" @elem{@${\langK} static-static substitution}]{
  If @${\tann{x}{\tau},\Gamma \wellKE e : K}
  and @${\wellKE v : \tagof{\tau}}
  then @${\Gamma \wellKE \vsubst{e}{x}{v} : K}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\tagof{\tau} \subkeq K}
      @${\tann{x}{\tau},\Gamma \wellKE x : K}
    }
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\wellKE v : K}
      (1)
    }
    @tr-step{
      @${\Gamma \wellKE v : K}
      @|K-weakening| (3)
    }
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

  @tr-case[@${e = \vlam{x}{e'}}]{
    @tr-qed{
      by @${\vsubst{(\vlam{x}{e'})}{x}{v} = \vlam{x}{e'}}
    }
  }

  @tr-case[@${e = \vlam{x'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{x'}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${x',\tann{x}{\tau},\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${x',\Gamma \wellKE \vsubst{e'}{x}{v}}
      @|K-DS-subst|
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{x'}{\vsubst{e'}{x}{v}} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},\tann{x}{\tau},\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})} : K}
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0 : \kany
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1 : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : \kany
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : \kany}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0 : K_0
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1 : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : K_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0 : K_0}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \eunop{\vsubst{e_0}{x}{v}} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0 : K_0
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1 : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : K_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e'}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v}}
      @K-DS-subst (2)
    }
    @tr-step{
      @${\Gamma \wellKE \edyn{\tau'}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \edyn{\kany}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\kany}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e'}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v}}
      @K-DS-subst (2)
    }
    @tr-step{
      @${\Gamma \wellKE \edyn{\kany}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \echk{K'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \echk{K'}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e' : \kany}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \echk{K'}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed{
    }
  }

  @tr-case[@${e = \esta{\tau'}{e'}
              @tr-or[4]
              e = \esta{\kany}{e'}}]{
    @tr-contradiction{
      @${\Gamma \wellKE e : K}
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-SD-subst" @elem{@${\langK} static-dynamic substitution}]{
  If @${x,\Gamma \wellKE e : K}
  and @${\wellKE v}
  then @${\Gamma \wellKE \vsubst{e}{x}{v} : K}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${K = \kany}
      @${x,\Gamma \wellKE x : K}
    }
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\wellKE v : K}
      @|K-D-value-inversion|
    }
    @tr-step{
      @${\wellKE v : \kany}
      @${K \subteq \kany}
    }
    @tr-step{
      @${\Gamma \wellKE v : \kany}
      @|K-weakening| (3)
    }
    @tr-qed{
    }
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
      @${x',x,\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${x',\Gamma \wellKE \vsubst{e'}{x}{v}}
      @|K-DD-subst|
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{x'}{\vsubst{e'}{x}{v}} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @|K-SD-subst|
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})} : K}
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0 : \kany
         @tr-and[]
         x,\Gamma \wellKE e_1 : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : \kany
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : \kany}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0 : K_0
         @tr-and[]
         x,\Gamma \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : K_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0 : K_0}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \eunop{\vsubst{e_0}{x}{v}} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0 : K_0
         @tr-and[]
         x,\Gamma \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v} : K_0
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v} : K_1}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v}}
      @|K-DD-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \edyn{\tau'}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\kany}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edyn{\kany}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v}}
      @|K-DD-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \edyn{\kany}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \echk{K'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \echk{K'}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \echk{K'}{(\vsubst{e'}{x}{v})} : K}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\tau'}{e'}
                @tr-or[4]
                e = \esta{\kany}{e'}}]{
    @tr-contradiction{@${\Gamma \wellKE e : K}}
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-DS-subst" @elem{@${\langK} dynamic-static substitution}]{
      If @${\tann{x}{\tau},\Gamma \wellKE e}
      and @${\wellKE v : \tagof{\tau}}
      then @${\Gamma \wellKE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\wellKE v : \kany}
      @${\tagof{\tau} \subk \kany}
    }
    @tr-step{
      @${\wellKE v}
      @elem{@|K-S-value-inversion| (2)}
    }
    @tr-step{
      @${\Gamma \wellKE v}
      @elem{@|K-weakening| (3)}
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
      @${x',\tann{x}{\tau},\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${x',\Gamma \wellKE \vsubst{e'}{x}{v}}
      @K-DS-subst
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{x'}{\vsubst{e'}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},\tann{x}{\tau},\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @|K-SS-subst|
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e_0
         @tr-and[]
         \tann{x}{\tau},\Gamma \wellKE e_1}
      @K-S-inversion
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}
                @tr-or[4]
                e = \edyn{\kany}{e'}
                @tr-or[4]
                e = \echk{K'}{e'}
               }]{
    @tr-contradiction{
      @${\tann{x}{\tau},\Gamma \wellKE e}
    }
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e' : \tagof{\tau'}}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \tagof{\tau'}}
      @|K-SS-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \esta{\tau'}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\kany}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\kany}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${\tann{x}{\tau},\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @|K-SS-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \esta{\kany}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-DD-subst" @elem{@${\langK} dynamic-dynamic substitution}]{
  If @${x,\Gamma \wellKE e}
  and @${\wellKE v}
  then @${\Gamma \wellKE \vsubst{e}{x}{v}}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\Gamma \wellKE v}
      @|K-weakening| (3)
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
      @${x',x,\Gamma \wellKE e'}
      @|K-S-inversion|
    }
    @tr-step{
      @${x',\Gamma \wellKE \vsubst{e'}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{x'}{\vsubst{e'}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @|K-SD-subst|
    }
    @tr-step{
      @${\Gamma \wellKE \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0
         @tr-and[]
         x,\Gamma \wellKE e_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0
         @tr-and[]
         x,\Gamma \wellKE e_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e_0
         @tr-and[]
         x,\Gamma \wellKE e_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellKE \vsubst{e_1}{x}{v}}
      @tr-IH (2)
    }
    @tr-step{
      @${\Gamma \wellKE \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \edyn{\tau'}{e'}
                @tr-or[4]
                e = \edyn{\kany}{e'}
                @tr-or[4]
                e = \echk{K'}{e'}
               }]{
    @tr-contradiction{
      @${\Gamma \wellKE e}
    }
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\tau'}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e' : \tagof{\tau'}}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \tagof{\tau'}}
      @|K-SD-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \esta{\tau'}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \esta{\kany}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \esta{\kany}{\vsubst{e'}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellKE e' : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellKE \vsubst{e'}{x}{v} : \kany}
      @|K-SD-subst| (2)
    }
    @tr-step{
      @${\Gamma \wellKE \esta{\kany}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-finite-subtyping" @elem{@${K \subk K} finite}]{
  All chains @${K_0 \subk \cdots \subk K_{n-1}} are finite.
}@tr-proof{
  @tr-qed{
    by definition; the longest chain is
    @${\knat \subk \kint \subk \kany}.
  }
}

@tr-lemma[#:key "K-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellKE e} then @${x,\Gamma \wellKE e}
    }
    @item{
      If @${\Gamma \wellKE e : \tau} then @${\tann{x}{\tau'},\Gamma \wellKE e : \tau}
    }
  ]
}@tr-proof{
  @; TODO good enough?
  @itemize[
    @item{
      @tr-step[
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellKE e
           @tr-or[]
           \Gamma \wellKE e : \tau}
      ]
    }
  ]
}

@tr-lemma[#:key "KM-uec" @elem{@${\langM} unique static evaluation contexts}]{
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

@tr-definition[#:key "boundary-types" @elem{boundary types @${B(e)}}]{
  Let @${B(e)} be the set of type annotations on boundary term in @${e},
   namely, @${\{\tau \mid \edyn{\tau}{e'} \in e \vee \esta{\tau}{e'} \in e\}}.
}

@tr-definition[#:key "bisimilar-reduction" @elem{bisimilar reduction}]{
  @${(e_0, \rightarrow_0)} and @${(e_1, \rightarrow_1)} are bisimilar if there
   exists a relation @${R} such that @${(e_0, e_1) \in R} and either:
  @itemlist[
  @item{
    @${e_0 \rightarrow_0 e_0'} and @${e_1 \rightarrow_1 e_1'}
    and @${(e_0', \rightarrow_0)} and @${(e_1', \rightarrow_1)} are bisimilar;
  }
  @item{
    @${e_0 \rightarrow_0 e_0'}
    and @${(e_0', \rightarrow_0)} and @${(e_1, \rightarrow_1)} are bisimilar;
  }
  @item{
    @${e_1 \rightarrow_1 e_1'}
    and @${(e_0, \rightarrow_0)} and @${(e_1', \rightarrow_1)} are bisimilar.
  }
  ]
}

@tr-theorem[#:key "NK-base-type" @elem{@${\langN}/@${\langK} base type equivalence}]{
  If @${\wellM e : \tau} and @${B(e) \subseteq \{\tint, \tnat\}}
  and @${\wellM e : \tau \carrow e''}, then
  @${(e, \ccNS)} and @${(e'', \ccKS)} are bisimilar.
}
@tr-proof[#:sketch? #true]{
  The boundary terms of base type have the same semantics in both embeddings.
}

@; TODO do the proof, but should be easy
@; - D(t,v) = D(t, v) and S(t,v) = S(t,v) across embeddings
@; - stuttering simulation because of chk terms
@; - all checks pass in the LD term ... because every value is "actually typed"


@|clearpage|
