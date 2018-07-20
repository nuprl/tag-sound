#lang gf-icfp-2018
@require[
  "techreport.rkt"
  (only-in "supplement-model-n.scrbl"
    N-S-preservation
    N-D-preservation
    N-S-canonical
    N-S-inversion
    N-D-inversion)
  (only-in "supplement-model-k.scrbl"
    K-S-completion
    K-D-completion
    K-S-factor
    K-S-hole-typing
    K-S-inversion
    K-D-inversion)]

@appendix-title++{Simulation Lemmas}


@section{Definitions}

@(begin
   (define KE-approximation @tr-ref[#:key "KE-approximation"]{@${\langK}--@${\langE} approximation})
   (define KE-simulation @tr-ref[#:key "KE-simulation"]{@${\langK}--@${\langE} simulation})
   (define KE-S-refl @tr-ref[#:key "KE-S-refl"]{@${\langK}--@${\langE} static reflexivity})
   (define KE-D-refl @tr-ref[#:key "KE-D-refl"]{@${\langK}--@${\langE} dynamic reflexivity})
   (define KE-ctx @tr-ref[#:key "KE-ctx"]{@${\langK}--@${\langE} context factoring})
   (define KE-step @tr-ref[#:key "KE-step"]{@${\langK}--@${\langE} step})
   (define KE-hole-subst @tr-ref[#:key "KE-hole-subst"]{@${\langK}--@${\langE} hole substitution})
   (define KE-inversion @tr-ref[#:key "KE-inversion"]{@${\langK}--@${\langE} inversion})
   (define KE-subst @tr-ref[#:key "KE-subst"]{@${\langK}--@${\langE} substitution})

   (define NK-approximation @tr-ref[#:key "NK-approximation"]{@${\langN}--@${\langK} approximation})
   (define NK-simulation @tr-ref[#:key "NK-simulation"]{@${\langN}--@${\langK} simulation})
   (define NK-S-refl @tr-ref[#:key "NK-S-refl"]{@${\langN}--@${\langK} static reflexivity})
   (define NK-D-refl @tr-ref[#:key "NK-D-refl"]{@${\langN}--@${\langK} dynamic reflexivity})
   (define NK-S-type @tr-ref[#:key "NK-S-type"]{@${\langN}--@${\langK} static hole typing})
   (define NK-D-type @tr-ref[#:key "NK-D-type"]{@${\langN}--@${\langK} dynamic hole typing})
   (define NK-value @tr-ref[#:key "NK-value"]{@${\langN}--@${\langK} hole substitution})
   (define NK-hole-subst @tr-ref[#:key "NK-hole-subst"]{@${\langN}--@${\langK} hole substitution})
   (define NK-subst @tr-ref[#:key "NK-subst"]{@${\langN}--@${\langK} substitution})
   (define NK-check @tr-ref[#:key "NK-check"]{@${\langN}--@${\langK} boundary checking})
   (define NK-S-check @tr-ref[#:key "NK-S-check"]{@${\langN}--@${\langK} @${\vsta} checking})
   (define NK-D-check @tr-ref[#:key "NK-D-check"]{@${\langN}--@${\langK} @${\vdyn} checking})
   (define NK-S-stutter @tr-ref[#:key "NK-S-stutter"]{@${\langN}--@${\langK} static value stutter})
   (define NK-D-stutter @tr-ref[#:key "NK-D-stutter"]{@${\langN}--@${\langK} dynamic value stutter})
   (define NK-inversion @tr-ref[#:key "NK-inversion"]{@${\langN}--@${\langK} inversion})
)

@exact{\input{fig:simulation.tex}}


@|clearpage|
@section{Theorems}

@tr-theorem[#:key "error-simulation" @elem{@${\eerr} approximation}]{
  If @${e \in \exprsta} and @${\wellM e : \tau} then the following statements hold:
  @itemlist[
  @item{
    if @${e \rrESstar \eerr} then @${e \rrKSstar \eerr}
  }
  @item{
    if @${e \rrKSstar \eerr} then @${e \rrNSstar \eerr}
  }
  ]
}@tr-proof[]{
  @tr-qed{
    by @|KE-approximation| and @|NK-approximation|.
  }
}

@exact{\newpage}
@section{Lemmas}

@tr-lemma[#:key "KE-approximation" @elem{@${\langK}--@${\langE} approximation}]{
  If @${e \in \exprsta} and @${\wellM e : \tau}
  and @${e \rrESstar \eerr} then:
  @itemlist[
  @item{
    @${\wellKE e : \tagof{\tau} \carrow e''}
  }
  @item{
    @${e'' \rrKSstar \eerr}
  }
  ]
}@tr-proof{
  @itemlist[
    @item{@tr-step{
      @${e'' \kerel e}
      @|KE-S-refl|
    }}
    @item{@tr-qed{
      by @|KE-simulation|
    }}
  ]
}


@tr-lemma[#:key "KE-S-refl" @elem{@${\langK}--@${\langE} static reflexivity}]{
  If @${\Gamma \wellM e : \tau} and @${\Gamma \wellKE e : \tagof{\tau} \carrow e''} then
  @${e'' \kerel e}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellKE e : \tagof{\tau} \carrow e''}
   judgment.

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i : \tnat \carrow i
              } }]{
    @tr-qed{
      @${i \kerel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i : \tint \carrow i
              } }]{
    @tr-qed{
      @${i \kerel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0 \carrow e_0'
                \\
                \Gamma \wellM e_1 : \tau_1 \carrow e_1'
              }{
                \Gamma \wellM \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1} \carrow \vpair{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tau_0}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_1}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c \carrow e'
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c} \carrow \vlam{\tann{x}{\tau_d}}{e'}
              } }]{
    @tr-step{
      @${\wellKE e' \tagof{\tau_c}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM x : \tau \carrow x
              } }]{
    @tr-qed{
      @${x \kerel x}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tarr{\tau_d}{\tau_c} \carrow e_0'
                \\
                \Gamma \wellM e_1 : \tau_d \carrow e_1'
                \\
                \tagof{\tau_c} = K
              }{
                \Gamma \wellM \eapp{e_0}{e_1} : \tau_c \carrow \echk{K}{(\eapp{e_0'}{e_1'})}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tarr{\tau_d}{\tau_c}}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_d}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-step{
      @${\eapp{e_0'}{e_1'} \kerel \eapp{e_0}{e_1}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\eapp{e_0'}{e_1'}} \kerel \eapp{e_0}{e_1}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tpair{\tau_0}{\tau_1} \carrow e'
                \\
                \tagof{\tau_0} = K
              }{
                \Gamma \wellM \efst{e} : \tau_0 \carrow \echk{K}{(\efst{e'})}
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tpair{\tau_0}{\tau_1}}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-step{
      @${\efst{e'} \kerel \efst{e}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\efst{e'}} \kerel \efst{e}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tpair{\tau_0}{\tau_1} \carrow e'
                \\
                \tagof{\tau_1} = K
              }{
                \Gamma \wellM \esnd{e} : \tau_1 \carrow \echk{K}{(\esnd{e'})}
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tpair{\tau_0}{\tau_1}}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-step{
      @${\esnd{e'} \kerel \esnd{e}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\esnd{e'}} \kerel \esnd{e}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 : \tau_1 \carrow e_1'
                %\\\\
                %\Delta(\vbinop, \tau_0, \tau_1) = \tau
              }{
                \Gamma \wellM \ebinop{e_0}{e_1} : \tau \carrow \ebinop{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tau_0}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_1}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau' \carrow e'
                \\\\
                \tau' \subteq \tau
              }{
                \Gamma \wellM e : \tau \carrow e'
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tau'}}
      @|K-S-completion|
    }
    @tr-qed{
      @tr-IH (1)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr : \tau \carrow \eerr
              } }]{
    @tr-qed{
      @${\eerr \kerel \eerr}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \edyn{\tau}{e} : \tau \carrow \edyn{\tau}{e'}
              } }]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }
}

@tr-lemma[#:key "KE-D-refl" @elem{@${\langK}--@${\langE} dynamic reflexivity}]{
  If @${\Gamma \wellM e} and @${\Gamma \wellKE e \carrow e''} then
  @${e'' \kerel e}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellKE e \carrow e''} judgment.

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i \carrow i
              }}]{
    @tr-qed{
      @${i \kerel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
             \Gamma \wellM e_0 \carrow e_0'
             \\\\
             \Gamma \wellM e_1 \carrow e_1'
           }{
             \Gamma \wellM \vpair{e_0}{e_1} \carrow \vpair{e_0'}{e_1'}
           }}]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \vlam{x}{e} \carrow \vlam{x}{e'}
              }}]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM x \carrow x
              } }]{
    @tr-qed{
      @${x \kerel x}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 \carrow e_1'
              }{
                \Gamma \wellM \eapp{e_0}{e_1} \carrow \eapp{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \eunop{e} \carrow \eunop{e'}
              }}]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 \carrow e_1'
              }{
                \Gamma \wellM \ebinop{e_0}{e_1} \carrow \ebinop{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr \carrow \eerr
              } }]{
    @tr-qed{
      @${\eerr \kerel \eerr}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau \carrow e'
              }{
                \Gamma \wellM \esta{\tau}{e} \carrow \esta{\tau}{e'}
              }
              }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tau}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \kerel e}
      @|KE-S-refl| (1)
    }
    @tr-qed{
      (2)
    }
  }

}

@tr-lemma[#:key "KE-simulation" @elem{@${\langK}--@${\langE} simulation}]{
  If @${\exprk_0 \kerel \expre_0} and @${\expre_0 \ccES \expre_1}
  and @${\exprk_0} does not contain a subterm of the form @${\eerr} then:
  @itemlist[
    @item{
      @${\exprk_0 \ccKS \ldots \ccKS \exprk_n}
    }
    @item{
      @${\forall i \in \{1 .. n \mhyphen 1\}.\, \exprk_i \kerel \expre_0}
    }
    @item{
      @${\exprk_n \kerel \expre_1}
    }
  ]
}@tr-proof{
  @itemize[#:style 'ordered
    @item{@tr-step{
      @${\expre_0 = \ctxe[\expre_{0'}]
         @tr-and[]
         \expre_{0'} \rrES \expre_{1'}
         @tr-and[]
         \expre_1 = \ctxe[\expre_{1'}]}
      definition @${\ccES}
    }}
    @item{@tr-step{
      @${\exprk_0 = \ctxk[\exprk_{0'}]
         @tr-and[]
         \ctxk \kerel \ctxe
         @tr-and[]
         \exprk_{0'} \kerel \expre_{0'}}
      @|KE-ctx|
    }}
    @item{@list[
      @tr-if[@${\exprk_{0'} = \echk{K}{v_0}
                @tr-and[2]
                \efromany{K}{v_0} = \boundaryerror}]{
        @tr-step{
          @${\boundaryerror \kerel \expre_{1'}}
        }
        @tr-step{
          @${\ctxk[\exprk_{0'}] \ccKS \ctxk[\boundaryerror] \ccKS \boundaryerror}
        }
        @tr-step{
          @${\boundaryerror \kerel \ctxe[\expre_{1'}]}
        }
        @tr-qed{
        }
      }
      @tr-if[@${\exprk_{0'} = \echk{K}{v_0}
                @tr-and[2]
                \efromany{K}{v_0} = v_0}]{
        @tr-step{
          @${v_0 \kerel \expre_{0'}}
          @${\echk{K}{v_0} \kerel \expre_{0'}}
        }
        @tr-step{
          @${\ctxk[\exprk_{0'}] \ccKS \ctxk[v_0]}
        }
        @tr-step{
          @${\ctxk[v_0] \kerel \ctxe[\expre_{0'}]}
          @|KE-hole-subst|
        }
        @elem{repeat from step (2) with the smaller expression @${\ctxk[v_0]}}
      }
      @tr-if[@${\exprk_{0'} = \edynfake{v_0}}]{
        @tr-step{
          @${v_0 \kerel \expre_{0'}}
          @${\edynfake{v_0} \kerel \expre_{0'}}
        }
        @tr-step{
          @${\ctxk[\exprk_{0'}] \ccKS \ctxk[v_0]}
        }
        @tr-step{
          @${\ctxk[v_0] \kerel \ctxe[\expre_{0'}]}
          @|KE-hole-subst|
        }
        @elem{repeat from step (2) with the smaller expression @${\ctxk[v_0]}}
      }
      @tr-if[@${\exprk_{0'} = \estafake{v_0}}]{
        @tr-step{
          @${v_0 \kerel \expre_{0'}}
          @${\estafake{v_0} \kerel \expre_{0'}}
        }
        @tr-step{
          @${\ctxk[\exprk_{0'}] \ccKD \ctxk[v_0]}
        }
        @tr-step{
          @${\ctxk[v_0] \kerel \ctxe[\expre_{0'}]}
          @|KE-hole-subst|
        }
        @elem{repeat from step (2) with the smaller expression @${\ctxk[v_0]}}
      }
      @tr-else[@${\exprk_{0'} \neq \echk{K}{v_0}
                  @tr-and[4]
                  \exprk_{0'} \neq \edynfake{v_0}
                  @tr-and[4]
                  \exprk_{0'} \neq \estafake{v_0}
                  @tr-and[4]
                  \exprk_{0'} \not\in \eerr}]{
        @tr-step{
          @${\ctxk[\exprk_{0'}] \ccKS \ctxk[\exprk_{1'}]
             @tr-and[]
             \exprk_{1'} \kerel \expre_{1'}}
          @|KE-step|
        }
        @tr-qed{
          by @|KE-hole-subst| if @${\expre_{1'} \not\in \eerr} and by @${\ctxk[\exprk_{0'}] \ccKS \ctxk[\eerr] \ccKS \eerr} otherwise.
        }
      }
    ]}
  ]
}

@tr-lemma[#:key "KE-ctx" @elem{@${\langK}--@${\langE} context factoring}]{
  If @${\ctxk[\exprk] \kerel \ctxe[\expre]} and @${\ctxk[\exprk]} does not
   contain a subterm of the form @${\eerr} then:
  @itemlist[
    @item{
      @${\ctxk_0 \kerel \ctxe_0}
    }
    @item{
      @${\exprk_{0'} \kerel \expre_{0'}}
    }
  ]
}@tr-proof{
  By structural induction on @${\ctxk[\exprk]}.

  @tr-case[@${\ctxk[\exprk] = x}]{
    @tr-step{
      @${\ctxk = \ehole
         @tr-and[]
         \exprk = x}
    }
    @tr-step{
      @${\ctxe[\expre] = x}
      @${\ctxk[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxe = \ehole
         @tr-and[]
         \expre = x}
      (2)
    }
    @tr-step{
      @${\ehole \kerel \ehole
         @tr-and[]
         x \kerel x}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\ctxk[\exprk] = i}]{
    @tr-step{
      @${\ctxk = \ehole
         @tr-and[]
         \exprk = i}
    }
    @tr-step{
      @${\ctxe[\expre] = i}
      @${\ctxk[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxe = \ehole
         @tr-and[]
         \expre = i}
      (2)
    }
    @tr-step{
      @${\ehole \kerel \ehole
         @tr-and[]
         i \kerel i}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\ctxk[\exprk] = \vlam{x}{\exprk_0}}]{
    @tr-step{
      @${\ctxk = \ehole
         @tr-and[]
         \exprk = \vlam{x}{\exprk_0}}
    }
    @tr-step{
      @${\ctxe[\expre] = \vlam{x}{\exprk_0}}
      @${\ctxk[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxe = \ehole
         @tr-and[]
         \expre = \vlam{x}{\exprk_0}}
      (2)
    }
    @tr-step{
      @${\ehole \kerel \ehole
         @tr-and[]
         \vlam{x}{\exprk_0} \kerel \vlam{x}{\exprk_0}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\ctxk[\exprk] = \vlam{\tann{x}{\tau}}{\exprk_0}}]{
    @tr-step{
      @${\ctxk = \ehole
         @tr-and[]
         \exprk = \vlam{\tann{x}{\tau}}{\exprk_0}}
    }
    @tr-step{
      @${\ctxe[\expre] = \vlam{\tann{x}{\tau}}{\exprk_0}}
      @${\ctxk[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxe = \ehole
         @tr-and[]
         \expre = \vlam{\tann{x}{\tau}}{\exprk_0}}
      (2)
    }
    @tr-step{
      @${\ehole \kerel \ehole
         @tr-and[]
         \vlam{\tann{x}{\tau}}{\exprk_0} \kerel \vlam{\tann{x}{\tau}}{\exprk_0}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\ctxk[\exprk] = \vmonfun{\tau}{v}}]{
    @tr-contradiction{
      @${\ctxk[\exprk] \kerel \ctxe[\expre]}
    }
  }

  @tr-case[@${\ctxk[\exprk] = \vpair{\ctxk_0[\exprk_0]}{\ctxk_1[\exprk_1]}}]{
    @tr-step{
      @${\ctxe[\expre] = \vpair{\ctxe_0[\expre_0]}{\ctxe_1[\expre_1]}
         @tr-and[]
         {\ctxk_0[\exprk_0]} \kerel {\ctxe_0[\expre_0]}
         @tr-and[]
         {\ctxk_1[\exprk_1]} \kerel {\ctxe_1[\expre_1]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      @tr-IH
    }
    @list[
      @tr-if[@${\ctxk_1 = \ehole}]{
        @tr-step{
          @${\ctxk = \vpair{\ctxk_0}{\exprk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_0}
        }
        @tr-step{
          @${\ctxe_1 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_0}
        }
        @tr-step{
          @${\ctxe = \vpair{\ctxe_0}{\expre_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
      @tr-else[@${\ctxk_0 = \ehole}]{
        @tr-step{
          @${\ctxk = \vpair{\exprk_0}{\ctxk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_1}
        }
        @tr-step{
          @${\ctxe_0 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_1}
        }
        @tr-step{
          @${\ctxe = \vpair{\expre_0}{\ctxe_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
    ]
  }

  @tr-case[@${\ctxk[\exprk] = \eapp{\ctxk_0[\exprk_0]}{\ctxk_1[\exprk_1]}}]{
    @tr-step{
      @${\ctxe[\expre] = \eapp{\ctxe_0[\expre_0]}{\ctxe_1[\expre_1]}
         @tr-and[]
         {\ctxk_0[\exprk_0]} \kerel {\ctxe_0[\expre_0]}
         @tr-and[]
         {\ctxk_1[\exprk_1]} \kerel {\ctxe_1[\expre_1]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      @tr-IH
    }
    @list[
      @tr-if[@${\ctxk_1 = \ehole}]{
        @tr-step{
          @${\ctxk = \eapp{\ctxk_0}{\exprk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_0}
        }
        @tr-step{
          @${\ctxe_1 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_0}
        }
        @tr-step{
          @${\ctxe = \eapp{\ctxe_0}{\expre_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
      @tr-else[@${\ctxk_0 = \ehole}]{
        @tr-step{
          @${\ctxk = \eapp{\exprk_0}{\ctxk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_1}
        }
        @tr-step{
          @${\ctxe_0 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_1}
        }
        @tr-step{
          @${\ctxe = \eapp{\expre_0}{\ctxe_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
    ]
  }

  @tr-case[@${\ctxk[\exprk] = \eunop{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxe[\expre] = \eunop{\ctxe_0[\expre]}
         @tr-and[]
         {\ctxk_0[\exprk]} \kerel {\ctxe_0[\expre]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \eunop{\ctxk_0}}
    }
    @tr-step{
      @${\ctxe = \eunop{\ctxe_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk[\exprk] = \ebinop{\ctxk_0[\exprk_0]}{\ctxk_1[\exprk_1]}}]{
    @tr-step{
      @${\ctxe[\expre] = \ebinop{\ctxe_0[\expre_0]}{\ctxe_1[\expre_1]}
         @tr-and[]
         {\ctxk_0[\exprk_0]} \kerel {\ctxe_0[\expre_0]}
         @tr-and[]
         {\ctxk_1[\exprk_1]} \kerel {\ctxe_1[\expre_1]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      @tr-IH
    }
    @list[
      @tr-if[@${\ctxk_1 = \ehole}]{
        @tr-step{
          @${\ctxk = \ebinop{\ctxk_0}{\exprk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_0}
        }
        @tr-step{
          @${\ctxe_1 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_0}
        }
        @tr-step{
          @${\ctxe = \ebinop{\ctxe_0}{\expre_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
      @tr-else[@${\ctxk_0 = \ehole}]{
        @tr-step{
          @${\ctxk = \ebinop{\exprk_0}{\ctxk_1}}
        }
        @tr-step{
          @${\exprk = \exprk_1}
        }
        @tr-step{
          @${\ctxe_0 = \ehole}
          (2)
        }
        @tr-step{
          @${\expre = \expre_1}
        }
        @tr-step{
          @${\ctxe = \ebinop{\expre_0}{\ctxe_1}}
        }
        @tr-step{
          @${\ctxk \kerel \ctxe}
          (2)
        }
        @tr-qed{}
      }
    ]
  }

  @tr-case[@${\ctxk[\exprk] = \edyn{\tau}{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxe[\expre] = \edyn{\tau}{\ctxe_0[\expre]}
         @tr-and[]
         {\ctxk_0[\exprk]} \kerel {\ctxe_0[\expre]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \edyn{\tau}{\ctxk_0}}
    }
    @tr-step{
      @${\ctxe = \edyn{\tau}{\ctxe_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk[\exprk] = \esta{\tau}{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxe[\expre] = \esta{\tau}{\ctxe_0[\expre]}
         @tr-and[]
         {\ctxk_0[\exprk]} \kerel {\ctxe_0[\expre]}}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \esta{\tau}{\ctxk_0}}
    }
    @tr-step{
      @${\ctxe = \esta{\tau}{\ctxe_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk[\exprk] = \echk{K}{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \echk{K}{\ctxk_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk[\exprk] = \edynfake{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \edynfake{\ctxk_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk[\exprk] = \estafake{\ctxk_0[\exprk]}}]{
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
    }
    @tr-step{
      @${\ctxk_0 \kerel \ctxe
         @tr-and[]
         \exprk \kerel \expre}
      @tr-IH
    }
    @tr-step{
      @${\ctxk = \estafake{\ctxk_0}}
    }
    @tr-step{
      @${\ctxk \kerel \ctxe}
    }
    @tr-qed{}
  }
}

@tr-lemma[#:key "KE-step" @elem{@${\langK}--@${\langE} step}]{
  If @${\ctxk[\exprk] \kerel \ctxe[\expre]
        @tr-and[]
        \exprk \kerel \expre
        @tr-and[]
        \expre \rrES \expre_1
        @tr-and[]
        \exists \tau\,.~ \wellKE \ctxk[\exprk] : \tagof{\tau}
        @tr-and[]
        \exprk \neq \echk{K}{e}
        @tr-and[]
        \exprk \neq \edynfake{e}
        @tr-and[]
        \exprk \neq \estafake{e}
        @tr-and[]
        \exprk \neq \eerr}
  @linebreak[]
  then:
  @itemlist[
    @item{
      @${\ctxk[\exprk] \ccKS \ctxk[\exprk_1]}
    }
    @item{
      @${\exprk_1 \kerel \expre_1}
    }
  ]
}@tr-proof{
  Proceed by case analysis on @${\exprk \kerel \expre}.

  @tr-case[@${\eerr \kerel \expre}]{
    @tr-contradiction[@${\exprk \neq \eerr}]
  }

  @tr-case[@${\echk{K}{v} \kerel \expre}]{
    @tr-contradiction[@${\exprk \neq \echk{K}{v}}]
  }

  @tr-case[@${\edynfake{v} \kerel \expre}]{
    @tr-contradiction[@${\exprk \neq \edynfake{v}}]
  }

  @tr-case[@${\estafake{v} \kerel \expre}]{
    @tr-contradiction[@${\exprk \neq \estafake{v}}]
  }

  @tr-case[@${x \kerel x}]{
    @tr-contradiction[@${\expre \rrES \expre_1}]
  }

  @tr-case[@${i \kerel i}]{
    @tr-contradiction[@${\expre \rrES \expre_1}]
  }

  @tr-case[@${\vlam{x}{\exprk} \kerel \vlam{x}{\expre}}]{
    @tr-contradiction[@${\expre \rrES \expre_1}]
  }

  @tr-case[@${\vlam{\tann{x}{\tau}}{\exprk} \kerel \vlam{\tann{x}{\tau}}{\expre}}]{
    @tr-contradiction[@${\expre \rrES \expre_1}]
  }

  @tr-case[@${\eapp{\valk_0}{\valk_1} \kerel \eapp{\vale_0}{\vale_1}} #:itemize? #false]{
    @tr-if[@${\vale_0 = i
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1} : K}]{
      @tr-step{
        @${\valk_0 = i}
        @|KE-inversion|
      }
      @tr-contradiction{
        @${\wellKE \eapp{\valk_0}{\valk_1} : K}
      }
    }
    @tr-if[@${\vale_0 = i
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1}}]{
      @tr-step{
        @${\valk_0 = i}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \tagerror}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKD \tagerror}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\tagerror]}
        (3)
      }
      @tr-qed{
        @${\tagerror \kerel \tagerror}
      }
    }
    @tr-if[@${\vale_0 \in \vpair{v}{v}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1} : K}]{
      @tr-step{
        @${\valk_0 \in \vpair{v}{v}}
        @|KE-inversion|
      }
      @tr-contradiction{
        @${\wellKE \eapp{\valk_0}{\valk_1} : K}
      }
    }
    @tr-if[@${\vale_0 \in \vpair{v}{v}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1}}]{
      @tr-step{
        @${\valk_0 \in \vpair{v}{v}}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \tagerror}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKD \tagerror}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\tagerror]}
        (3)
      }
      @tr-qed{
        @${\tagerror \kerel \tagerror}
      }
    }
    @tr-if[@${\vale_0 = \vlam{x}{\expre}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1} : K}]{
      @tr-step{
        @${\valk_0 = \vlam{x}{\expre}}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \vsubst{\expre}{x}{\vale_1}}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKS \vsubst{\exprk}{x}{\valk_1}}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\vsubst{\exprk}{x}{\valk_1}]}
        (3)
      }
      @tr-step{
        @${\valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
        @|KE-subst|
      }
      @tr-qed{}
    }
    @tr-if[@${\vale_0 = \vlam{x}{\expre}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1}}]{
      @tr-step{
        @${\valk_0 = \vlam{x}{\expre}}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \vsubst{\expre}{x}{\vale_1}}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKD \vsubst{\exprk}{x}{\valk_1}}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\vsubst{\exprk}{x}{\valk_1}]}
        (3)
      }
      @tr-step{
        @${\valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
        @|KE-subst|
      }
      @tr-qed{}
    }
    @tr-if[@${\vale_0 = \vlam{\tann{x}{\tau}}{\expre}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1} : K}]{
      @tr-step{
        @${\valk_0 = \vlam{\tann{x}{\tau}}{\expre}}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \vsubst{\expre}{x}{\vale_1}}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKS \vsubst{\exprk}{x}{\valk_1}}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\vsubst{\exprk}{x}{\valk_1}]}
        (3)
      }
      @tr-step{
        @${\valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
        @|KE-subst|
      }
      @tr-qed{}
    }
    @tr-if[@${\vale_0 = \vlam{\tann{x}{\tau}}{\expre}
              @tr-and[2]
              \wellKE \eapp{\valk_0}{\valk_1}}]{
      @tr-step{
        @${\valk_0 = \vlam{\tann{x}{\tau}}{\expre}}
        @|KE-inversion|
      }
      @tr-step{
        @${\eapp{\vale_0}{\vale_1} \rrES \vsubst{\expre}{x}{\vale_1}}
      }
      @tr-step{
        @${\eapp{\valk_0}{\valk_1} \rrKD \vsubst{\exprk}{x}{\valk_1}}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\vsubst{\exprk}{x}{\valk_1}]}
        (3)
      }
      @tr-step{
        @${\valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
        @|KE-subst|
      }
      @tr-qed{}
    }
    @tr-else[@${\vale_0 = \vmonfun{\tau}{\vale}}]{
      @tr-contradiction[@${\expre \rrES \expre_1}]
    }
  }

  @tr-case[@${\vpair{\valk_0}{\valk_1} \kerel \vpair{\vale_0}{\vale_1}}]{
    @tr-contradiction[@${\expre \rrES \expre_1}]
  }

  @tr-case[@${\eunop{\valk} \kerel \eunop{\vale}} #:itemize? #false]{
    @tr-if[@${\vale = \vpair{\vale_0}{\vale_1}
              @tr-and[2]
              \vunop = \vfst}]{
      @tr-step{
        @${\valk = \vpair{\valk_0}{\valk_1}
           @tr-and[]
           \valk_0 \kerel \vale_0
           @tr-and[]
           \valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\eunop{\vale} \rrES \vale_0}
      }
      @tr-step{
        @${\eunop{\valk} \rrKS \valk_0
           @tr-or[]
           \eunop{\valk} \rrKD \valk_0}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\valk_0]}
        (3)
      }
      @tr-qed{
        (1)
      }
    }
    @tr-if[@${\vale = \vpair{\vale_0}{\vale_1}
              @tr-and[2]
              \vunop = \vsnd}]{
      @tr-step{
        @${\valk = \vpair{\valk_0}{\valk_1}
           @tr-and[]
           \valk_0 \kerel \vale_0
           @tr-and[]
           \valk_1 \kerel \vale_1}
        @|KE-inversion|
      }
      @tr-step{
        @${\eunop{\vale} \rrES \vale_1}
      }
      @tr-step{
        @${\eunop{\valk} \rrKS \valk_1
           @tr-or[]
           \eunop{\valk} \rrKD \valk_1}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\valk_1]}
        (3)
      }
      @tr-qed{
        (1)
      }
    }
    @tr-else[""]{
      @tr-step{
        @${\eunop{\vale} \rrES \tagerror}
      }
      @tr-qed{
        either @${\eunop{\valk} \rrKD \tagerror}
        or the case is impossible by @${\wellKE \eunop{\valk} : K}
      }
    }
  }

  @tr-case[@${\ebinop{\valk_0}{\valk_1} \kerel \ebinop{\vale_0}{\vale_1}} #:itemize? #false]{
    @tr-if[@${\vale_0 = i_0
              @tr-and[2]
              \vale_1 = i_1
              @tr-and[2]
              \vbinop = \vsum}]{
      @tr-step{
        @${\valk_0 \kerel \vale_0 @tr-and[] \valk_1 \kerel \vale_1}
      }
      @tr-step{
        @${\valk_0 = i_0 @tr-and[] \valk_1 = i_1}
        @|KE-inversion| (1)
      }
      @tr-step{
        @${\ebinop{\vale_0}{\vale_1} \rrES i_0 + i_1}
      }
      @tr-step{
        @${\ebinop{\valk_0}{\valk_1} \rrKS i_0 + i_1
           @tr-or[]
           \ebinop{\valk_0}{\valk_1} \rrKD i_0 + i_1}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[i_0 + i_1]}
        (4)
      }
      @tr-qed{
        @${i_0 + i_1 \kerel i_0 + i_1}
      }
    }
    @tr-if[@${\vale_0 = i_0
              @tr-and[2]
              \vale_1 = i_1
              @tr-and[2]
              i_1 \neq 0
              @tr-and[2]
              \vbinop = \vquotient}]{
      @tr-step{
        @${\valk_0 \kerel \vale_0 @tr-and[] \valk_1 \kerel \vale_1}
      }
      @tr-step{
        @${\valk_0 = i_0 @tr-and[] \valk_1 = i_1}
        @|KE-inversion| (1)
      }
      @tr-step{
        @${\ebinop{\vale_0}{\vale_1} \rrES \floorof{i_0 / i_1}}
      }
      @tr-step{
        @${\ebinop{\valk_0}{\valk_1} \rrKS \floorof{i_0 / i_1}
           @tr-or[]
           \ebinop{\valk_0}{\valk_1} \rrKD \floorof{i_0 / i_1}}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\floorof{i_0 / i_1}]}
        (4)
      }
      @tr-qed{
        @${\floorof{i_0 / i_1} \kerel \floorof{i_0 / i_1}}
      }
    }
    @tr-if[@${\vale_0 = i_0
              @tr-and[2]
              \vale_1 = i_1
              @tr-and[2]
              i_1 = 0
              @tr-and[2]
              \vbinop = \vquotient}]{
      @tr-step{
        @${\valk_0 \kerel \vale_0 @tr-and[] \valk_1 \kerel \vale_1}
      }
      @tr-step{
        @${\valk_0 = i_0 @tr-and[] \valk_1 = i_1}
        @|KE-inversion| (1)
      }
      @tr-step{
        @${\ebinop{\vale_0}{\vale_1} \rrES \boundaryerror}
      }
      @tr-step{
        @${\ebinop{\valk_0}{\valk_1} \rrKS \boundaryerror
           @tr-or[]
           \ebinop{\valk_0}{\valk_1} \rrKD \boundaryerror}
      }
      @tr-step{
        @${\ctxk[\exprk] \ccKS \ctxk[\boundaryerror]}
        (4)
      }
      @tr-qed{
        @${\boundaryerror \kerel \boundaryerror}
      }
    }
    @tr-else[""]{
      @tr-step{
        @${\ebinop{\vale_0}{\vale_1} \rrES \tagerror}
      }
      @tr-qed{
        either @${\ebinop{\valk_0}{\valk_1} \rrKD \tagerror}
        or the case is impossible by @${\wellKE \ebinop{\valk_0}{\valk_1} : K}
      }
    }
  }

  @tr-case[@${\edyn{\tau}{\valk_0} \kerel \edyn{\tau}{\vale_0}}]{
    @tr-step{
      @${\valk_0 \kerel \vale_0}
    }
    @tr-step{
      @${\expre \rrES \vale_0}
    }
    @list[
      @tr-if[@${\efromany{\tagof{\tau}}{\valk_0} = \boundaryerror}]{
        @tr-step{
          @${\ctxk[\exprk] \ccKS \ctxk[\boundaryerror]}
        }
        @tr-qed{
          @${\boundaryerror \kerel \vale_1}
        }
      }
      @tr-else[@${\efromany{\tagof{\tau}}{\valk_0} = \valk_0}]{
        @tr-step{
          @${\ctxk[\edyn{\tau}{\valk_0}] \ccKS \ctxk[\valk_0]}
        }
        @tr-qed{
          by (1, 2, a)
        }
    }]
  }

  @tr-case[@${\esta{\tau}{\valk_0} \kerel \esta{\tau}{\vale_0}}]{
    @tr-step{
      @${\valk_0 \kerel \vale_0}
    }
    @tr-step{
      @${\expre \rrES \vale_0}
    }
    @tr-step{
      @${\esta{\tau}{\valk_0} \rrKD \valk_0}
    }
    @tr-step{
      @${\ctxk[\exprk] \ccKS \ctxk[\valk_0]}
      (3)
    }
    @tr-qed{
      by (1)
    }
  }

  @tr-case[@${\eerr \kerel \eerr}]{
    @tr-contradiction[@${\exprk \neq \eerr}]
  }

}

@tr-lemma[#:key "KE-hole-subst" @elem{@${\langK}--@${\langE} hole substitution}]{
  If @${\exprk \kerel \expre} and @${\ctxk \kerel \ctxe}
  then @${\ctxk[\exprk] \kerel \ctxe[\expre]}
}@tr-proof{
  By induction on the structure of @${\ctxk}.

  @tr-case[@${\ctxk = \ehole}]{
    @tr-step{
      @${\expre = \ehole}
    }
    @tr-step{
      @${\ctxk[\exprk] = \exprk
         @tr-and[]
         \ctxe[\expre] = \expre}
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxk = \eapp{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxe = \eapp{\ctxe_0}{\expre_1}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \eapp{\ctxk_0[\exprk_0]}{\exprk_1}}
    }
    @tr-step{
      @${\ctxe[\expre] = \eapp{\ctxe_0[\expre_0]}{\expre_1}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \eapp{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxe = \eapp{\expre_0}{\ctxe_1}
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_1[\exprk] \kerel \ctxe_1[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \eapp{\exprk_0}{\ctxk_1[\exprk_1]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \eapp{\expre_0}{\ctxe_1[\expre_1]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \vpair{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxe = \vpair{\ctxe_0}{\expre_1}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \vpair{\ctxk_0[\exprk_0]}{\exprk_1}}
    }
    @tr-step{
      @${\ctxe[\expre] = \vpair{\ctxe_0[\expre_0]}{\expre_1}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \vpair{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxe = \vpair{\expre_0}{\ctxe_1}
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_1[\exprk] \kerel \ctxe_1[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \vpair{\exprk_0}{\ctxk_1[\exprk_1]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \vpair{\expre_0}{\ctxe_1[\expre_1]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \eunop{\ctxk_0}}]{
    @tr-step{
      @${\ctxe = \eunop{\ctxe_0}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \eunop{\ctxk_0[\exprk_0]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \eunop{\ctxe_0[\expre_0]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }


  @tr-case[@${\ctxk = \ebinop{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxe = \ebinop{\ctxe_0}{\expre_1}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0
         @tr-and[]
         \exprk_1 \kerel \expre_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \ebinop{\ctxk_0[\exprk_0]}{\exprk_1}}
    }
    @tr-step{
      @${\ctxe[\expre] = \ebinop{\ctxe_0[\expre_0]}{\expre_1}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \ebinop{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxe = \ebinop{\expre_0}{\ctxe_1}
         @tr-and[]
         \exprk_0 \kerel \expre_0
         @tr-and[]
         \ctxk_1 \kerel \ctxe_1}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_1[\exprk] \kerel \ctxe_1[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \ebinop{\exprk_0}{\ctxk_1[\exprk_1]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \ebinop{\expre_0}{\ctxe_1[\expre_1]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \edyn{\tau}{\ctxk_0}}]{
    @tr-step{
      @${\ctxe = \edyn{\tau}{\ctxe_0}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \edyn{\tau}{\ctxk_0[\exprk_0]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \edyn{\tau}{\ctxe_0[\expre_0]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \esta{\tau}{\ctxk_0}}]{
    @tr-step{
      @${\ctxe = \esta{\tau}{\ctxe_0}
         @tr-and[]
         \ctxk_0 \kerel \ctxe_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe_0[\expre]}
      @tr-IH
    }
    @tr-step{
      @${\ctxk[\exprk] = \esta{\tau}{\ctxk_0[\exprk_0]}}
    }
    @tr-step{
      @${\ctxe[\expre] = \esta{\tau}{\ctxe_0[\expre_0]}}
    }
    @tr-qed{
      by (1, 2)
    }
  }

  @tr-case[@${\ctxk = \echk{K}{\ctxk_0}}]{
    @tr-step{
      @${\ctxk_0 \kerel \ctxe}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
      @tr-IH (1)
    }
    @tr-step{
      @${\ctxk[\exprk] = \echk{K}{\ctxk_0[\exprk]}}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\ctxk = \edynfake{\ctxk_0}}]{
    @tr-step{
      @${\ctxk_0 \kerel \ctxe}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
      @tr-IH (1)
    }
    @tr-step{
      @${\ctxk[\exprk] = \edynfake{\ctxk_0[\exprk]}}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\ctxk = \estafake{\ctxk_0}}]{
    @tr-step{
      @${\ctxk_0 \kerel \ctxe}
    }
    @tr-step{
      @${\ctxk_0[\exprk] \kerel \ctxe[\expre]}
      @tr-IH (1)
    }
    @tr-step{
      @${\ctxk[\exprk] = \estafake{\ctxk_0[\exprk]}}
    }
    @tr-qed{
      (2)
    }
  }

}

@tr-lemma[#:key "KE-inversion" @elem{@${\langK}--@${\langE} inversion}]{
  @itemlist[
    @item{
      if @${\valk \kerel i} then @${\valk = i}
    }
    @item{
      if @${\valk \kerel \vpair{\vale_0}{\vale_1}} then @${\valk = \vpair{\valk_0}{\valk_1}} and @${\valk_0 \kerel \vale_0} and @${\valk_1 \kerel \vale_1}
    }
    @item{
      if @${\valk \kerel \vlam{x}{\expre}} then @${\valk = \vlam{x}{\exprk}} and @${\exprk \kerel \expre}
    }
    @item{
      if @${\valk \kerel \vlam{\tann{x}{\tau}}{\expre}} then @${\valk = \vlam{\tann{x}{\tau}}{\exprk}} and @${\exprk \kerel \expre}
    }
  ]
}@tr-proof{
  By the definition of @${\kerel}
}

@tr-lemma[#:key "KE-subst" @elem{@${\langK}--@${\langE} substitution}]{
  If @${\exprk \kerel \expre} and @${\valk \kerel \vale}
  then @${\vsubst{\exprk}{x}{\valk} \kerel \vsubst{\expre}{x}{\vale}}
}@tr-proof{
  By induction on the structure of @${\exprk}.

  @tr-case[@${\exprk = x}]{
    @tr-step{
      @${\expre = x}
      @${\exprk \kerel \expre}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \valk
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vale}
    }
    @tr-qed{}
  }

  @tr-case[@${\exprk = y}]{
    @tr-step{
      @${\expre = y}
      @${\exprk \kerel \expre}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = y
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = y}
    }
    @tr-qed{(1)}
  }

  @tr-case[@${\exprk = i}]{
    @tr-step{
      @${\expre = i}
      definition @${\kerel}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = i
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = i}
    }
    @tr-qed{}
  }

  @tr-case[@${\exprk = \vlam{x}{\exprk_0}}]{
    @tr-step{
      @${\expre = \vlam{x}{\expre_0}
         @tr-and[]
         \exprk_0 \kerel \expre_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \vlam{x}{\exprk_0}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vlam{x}{\expre_0}}
    }
    @tr-qed{}
  }

  @tr-case[@${\exprk = \vlam{\tann{x}{\tau}}{\exprk_0}}]{
    @tr-step{
      @${\expre = \vlam{\tann{x}{\tau}}{\expre_0}
         @tr-and[]
         \exprk_0 \kerel \expre_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \vlam{\tann{x}{\tau}}{\exprk_0}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vlam{\tann{x}{\tau}}{\expre_0}}
    }
    @tr-qed{}
  }

  @tr-case[@${\exprk = \vlam{y}{\exprk_0}}]{
    @tr-step{
      @${\expre = \vlam{y}{\expre_0}
         @tr-and[]
         \exprk_0 \kerel \expre_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}}
      @tr-IH (1)
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \vlam{y}{\vsubst{\exprk_0}{x}{\vale}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vlam{y}{\vsubst{\expre_0}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \vlam{\tann{y}{\tau}}{\exprk_0}}]{
    @tr-step{
      @${\expre = \vlam{\tann{y}{\tau}}{\expre_0}
         @tr-and[]
         \exprk_0 \kerel \expre_0}
      definition @${\kerel}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}}
      @tr-IH (1)
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \vlam{\tann{y}{\tau}}{\vsubst{\exprk_0}{x}{\vale}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vlam{\tann{y}{\tau}}{\vsubst{\expre_0}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \vmonfun{\tau}{\valk_0}}]{
    @tr-contradiction{
      @${\exprk \kerel \expre}
    }
  }

  @tr-case[@${\exprk = \vpair{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\expre = \vpair{\expre_0}{\expre_1}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}
         @tr-and[]
         \vsubst{\exprk_1}{x}{\valk} \kerel \vsubst{\expre_1}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \vpair{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \vpair{\vsubst{\expre_0}{x}{\vale}}{\vsubst{\expre_1}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \eapp{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\expre = \eapp{\expre_0}{\expre_1}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}
         @tr-and[]
         \vsubst{\exprk_1}{x}{\valk} \kerel \vsubst{\expre_1}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \eapp{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \eapp{\vsubst{\expre_0}{x}{\vale}}{\vsubst{\expre_1}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \eunop{\exprk_0}}]{
    @tr-step{
      @${\expre = \eunop{\expre_0}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \eunop{\vsubst{\exprk_0}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \eunop{\vsubst{\expre_0}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \ebinop{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\expre = \ebinop{\expre_0}{\expre_1}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}
         @tr-and[]
         \vsubst{\exprk_1}{x}{\valk} \kerel \vsubst{\expre_1}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \ebinop{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \ebinop{\vsubst{\expre_0}{x}{\vale}}{\vsubst{\expre_1}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \edyn{\tau}{\exprk_0}}]{
    @tr-step{
      @${\expre = \edyn{\tau}{\expre_0}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \edyn{\tau}{\vsubst{\exprk_0}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \edyn{\tau}{\vsubst{\expre_0}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \esta{\tau}{\exprk_0}}]{
    @tr-step{
      @${\expre = \esta{\tau}{\expre_0}}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre_0}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \esta{\tau}{\vsubst{\exprk_0}{x}{\valk}}
         @tr-and[]
         \vsubst{\expre}{x}{\vale} = \esta{\tau}{\vsubst{\expre_0}{x}{\vale}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \eerr}]{
    @tr-qed{
      @${\vsubst{\exprk}{x}{\valk} = \eerr}
    }
  }

  @tr-case[@${\exprk = \echk{K}{\exprk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \expre}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \echk{K}{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \edynfake{\exprk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \expre}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \edynfake{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

  @tr-case[@${\exprk = \estafake{\exprk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \expre}
    }
    @tr-step{
      @${\vsubst{\exprk_0}{x}{\valk} \kerel \vsubst{\expre}{x}{\vale}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk} = \estafake{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
      (2, 3)
    }
  }

}


@exact{\newpage}
@; -----------------------------------------------------------------------------

@tr-lemma[#:key "NK-approximation" @elem{@${\langN}--@${\langK} approximation}]{
  If @${e \in \exprsta} and @${\wellM e : \tau}
  and @${\wellKE e : \tagof{\tau} \carrow e''}
  and @${e'' \rrKSstar \eerr}
  then @${e \rrNSstar \eerr}
}@tr-proof{
  @itemlist[
    @item{@tr-step{
      @${e \nkrel e''}
      @|NK-S-refl|
    }}
    @item{@tr-qed{
      by @|NK-simulation|
    }}
  ]
}


@tr-lemma[#:key "NK-S-refl" @elem{@${\langN}--@${\langK} static reflexivity}]{
  If @${\Gamma \wellM e : \tau
        @tr-and[]
        \Gamma \wellKE e : \tagof{\tau} \carrow e''}
  @linebreak[]
  then @${e \nkrel e''}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellKE e : \tagof{\tau} \carrow e''} judgment.

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i : \tnat \carrow i
              } }]{
    @tr-qed{
      @${i \nkrel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i : \tint \carrow i
              } }]{
    @tr-qed{
      @${i \nkrel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0 \carrow e_0'
                \\
                \Gamma \wellM e_1 : \tau_1 \carrow e_1'
              }{
                \Gamma \wellM \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1} \carrow \vpair{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tau_0}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_1}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c \carrow e'
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c} \carrow \vlam{\tann{x}{\tau_d}}{e'}
              } }]{
    @tr-step{
      @${\wellKE e' \tagof{\tau_c}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM x : \tau \carrow x
              } }]{
    @tr-qed{
      @${x \nkrel x}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tarr{\tau_d}{\tau_c} \carrow e_0'
                \\
                \Gamma \wellM e_1 : \tau_d \carrow e_1'
                \\
                \tagof{\tau_c} = K
              }{
                \Gamma \wellM \eapp{e_0}{e_1} : \tau_c \carrow \echk{K}{(\eapp{e_0'}{e_1'})}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tarr{\tau_d}{\tau_c}}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_d}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-step{
      @${\eapp{e_0'}{e_1'} \nkrel \eapp{e_0}{e_1}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\eapp{e_0'}{e_1'}} \nkrel \eapp{e_0}{e_1}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tpair{\tau_0}{\tau_1} \carrow e'
                \\
                \tagof{\tau_0} = K
              }{
                \Gamma \wellM \efst{e} : \tau_0 \carrow \echk{K}{(\efst{e'})}
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tpair{\tau_0}{\tau_1}}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-step{
      @${\efst{e'} \nkrel \efst{e}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\efst{e'}} \nkrel \efst{e}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tpair{\tau_0}{\tau_1} \carrow e'
                \\
                \tagof{\tau_1} = K
              }{
                \Gamma \wellM \esnd{e} : \tau_1 \carrow \echk{K}{(\esnd{e'})}
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tpair{\tau_0}{\tau_1}}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-step{
      @${\esnd{e'} \nkrel \esnd{e}}
      (2)
    }
    @tr-qed{
      @${\echk{K}{\esnd{e'}} \nkrel \esnd{e}}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 : \tau_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 : \tau_1 \carrow e_1'
                %\\\\
                %\Delta(\vbinop, \tau_0, \tau_1) = \tau
              }{
                \Gamma \wellM \ebinop{e_0}{e_1} : \tau \carrow \ebinop{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0' : \tagof{\tau_0}
         @tr-and[]
         \wellKE e_1' : \tagof{\tau_1}}
      @|K-S-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau' \carrow e'
                \\\\
                \tau' \subteq \tau
              }{
                \Gamma \wellM e : \tau \carrow e'
              } }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tau'}}
      @|K-S-completion|
    }
    @tr-qed{
      @tr-IH (1)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr : \tau \carrow \eerr
              } }]{
    @tr-qed{
      @${\eerr \nkrel \eerr}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \edyn{\tau}{e} : \tau \carrow \edyn{\tau}{e'}
              } }]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }
}

@tr-lemma[#:key "NK-D-refl" @elem{@${\langN}--@${\langK} dynamic reflexivity}]{
  If @${\Gamma \wellM e
        @tr-and[]
        \Gamma \wellKE e \carrow e''}
  @linebreak[]
  then @${e \nkrel e''}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellKE e \carrow e''} judgment.

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM i \carrow i
              }}]{
    @tr-qed{
      @${i \nkrel i}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
             \Gamma \wellM e_0 \carrow e_0'
             \\\\
             \Gamma \wellM e_1 \carrow e_1'
           }{
             \Gamma \wellM \vpair{e_0}{e_1} \carrow \vpair{e_0'}{e_1'}
           }}]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \vlam{x}{e} \carrow \vlam{x}{e'}
              }}]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM x \carrow x
              } }]{
    @tr-qed{
      @${x \nkrel x}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 \carrow e_1'
              }{
                \Gamma \wellM \eapp{e_0}{e_1} \carrow \eapp{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \eunop{e} \carrow \eunop{e'}
              }}]{
    @tr-step{
      @${\wellKE e'}
      @|K-D-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e_0 \carrow e_0'
                \\\\
                \Gamma \wellM e_1 \carrow e_1'
              }{
                \Gamma \wellM \ebinop{e_0}{e_1} \carrow \ebinop{e_0'}{e_1'}
              } }]{
    @tr-step{
      @${\wellKE e_0'
         @tr-and[]
         \wellKE e_1'}
      @|K-D-completion|
    }
    @tr-step{
      @${e_0' \nkrel e_0
         @tr-and[]
         e_1' \nkrel e_1}
      @tr-IH (1)
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
              }{
                \Gamma \wellM \eerr \carrow \eerr
              } }]{
    @tr-qed{
      @${\eerr \nkrel \eerr}
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e : \tau \carrow e'
              }{
                \Gamma \wellM \esta{\tau}{e} \carrow \esta{\tau}{e'}
              }
              }]{
    @tr-step{
      @${\wellKE e' : \tagof{\tau}}
      @|K-S-completion|
    }
    @tr-step{
      @${e' \nkrel e}
      @|KE-S-refl| (1)
    }
    @tr-qed{
      (2)
    }
  }

}

@tr-lemma[#:key "NK-simulation" @elem{@${\langN}--@${\langK} simulation}]{
  If @${\wellNE \ctxn[\exprn_0] : \tau
         @tr-and[]
         \wellKE \ctxk[\exprk_0] : \tagof{\tau}
         @tr-and[]
         \ctxn[\exprn_0] \nkrel \ctxk[\exprk_0]
         @tr-and[]
         \ctxk[\exprk_0] \ccKS \ctxk[\exprk_1]
         @tr-and[]
         \ctxn[\exprn_0] \mbox{ does not contain a subterm of the form} \eerr}
  @linebreak[]
  then @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_n]}
  and @${\ctxn[\exprn_n] \nkrel \ctxk[\exprk_1]}
}@tr-proof{
  By case analysis on @${\ctxk[\exprk_0] \ccKS \ctxk[\exprk_1]}

  TODO 
  - get all the cases
  - for each, LHS might not be a value so use the stutter lemmas
  - 


  @tr-case[@${\ctxk[\edynfake{\valk}] \ccKS \ctxk[\valk]}]{
  }

  @tr-case[@${\ctxk[\estafake{\valk}] \ccKS \ctxk[\valk]}]{
  }

@;  @tr-case[""]{
@;  }
}

@tr-lemma[#:key "NK-S-stutter" @elem{@${\langN}--@${\langK} static value stutter}]{
  If @${\exprn \nkrel \valk} and @${\wellNE \exprn : \tau}
  then one of the following holds:
  @itemlist[
    @item{
      @${\exprn \rrNSstar \valn} and @${\valn \nkrel \valk}
    }
    @item{
      @${\exprn \rrNSstar \boundaryerror}
    }
  ]
}@tr-proof{
  By induction on the number of boundary terms in @${\exprn},
   and case analysis on @${\exprn \nkrel \valk}.

  @tr-case[@${\exprn \mbox{ is a value}}]{
    @tr-qed{}
  }

  @tr-case[@${\exprn = \edyn{\tau}{(\esta{\tau'}{\exprn_2})}}]{
    @tr-step{
      @${\exprn_2 \nkrel \valk}
      @|NK-inversion|
    }
    @tr-step{
      @${\wellNE \esta{\tau'}{\exprn_2}
         @tr-and[]
         \wellNE \exprn_2 : \tau'}
      @|N-S-inversion| and @|N-D-inversion|
    }
    @tr-step{
      @${\exprn_2 \rrNSstar \valn_2
         @tr-and[]
         \valn_2 \nkrel \valk}
      @tr-IH (1, 2)
    }
    @tr-step{
      @${\wellNE \esta{\tau'}{\valn_2}}
      @|N-S-preservation| (2, 3)
    }
    @tr-step{
      @${\esta{\tau'}{\valn_2} \rrNSstar \valn_3 \mbox{ and } \valn_3 \nkrel \valk
         @tr-or[]
         \esta{\tau'}{\valn_2} \rrNSstar \boundaryerror}
      @|NK-check| (4)
    }
    @list[
      @tr-if[@${\esta{\tau'}{\valn_2} \rrNSstar \valn_3}]{
        @tr-step{
          @${\wellNE \edyn{\tau}{\valn_3} : \tau}
          @|N-S-preservation| (5)
        }
        @tr-step{
          @${\edyn{\tau}{\valn_3} \rrNSstar \valn_4 \mbox{ and } \valn_4 \nkrel \valk
             @tr-or[]
             \edyn{\tau}{\valn_3} \rrNSstar \boundaryerror}
          @|NK-check| (a)
        }
        @tr-qed{
          (b)
        }
      }
      @tr-else[@${\esta{\tau'}{\valn_2} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\edyn{\tau}{(\esta{\tau'}{\exprn_2})} \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\exprn = \esta{\tau}{(\edyn{\tau'}{\exprn_2})}}]{
    @tr-contradiction{
      @${\wellNE \exprn : \tau}
    }
  }

}

@tr-lemma[#:key "NK-D-stutter" @elem{@${\langN}--@${\langK} dynamic value stutter}]{
  If @${\exprn \nkrel \valk} and @${\wellNE \exprn}
  then one of the following holds:
  @itemlist[
    @item{
      @${\exprn \rrNDstar \valn} and @${\valn \nkrel \valk}
    }
    @item{
      @${\exprn \rrNDstar \boundaryerror}
    }
  ]
}@tr-proof{
  By induction on the number of boundary terms in @${\exprn},
   and case analysis on @${\exprn \nkrel \valk}.

  @tr-case[@${\exprn \mbox{ is a value}}]{
    @tr-qed{}
  }

  @tr-case[@${\exprn = \edyn{\tau}{(\esta{\tau'}{\exprn_2})}}]{
    @tr-contradiction{
      @${\wellNE \exprn : \tau}
    }
  }

  @tr-case[@${\exprn = \esta{\tau}{(\edyn{\tau'}{\exprn_2})}}]{
    @tr-step{
      @${\exprn_2 \nkrel \valk}
      @|NK-inversion|
    }
    @tr-step{
      @${\wellNE \edyn{\tau'}{\exprn_2} : \tau'
         @tr-and[]
         \wellNE \exprn_2}
      @|N-S-inversion| and @|N-D-inversion|
    }
    @tr-step{
      @${\exprn_2 \rrNDstar \valn_2
         @tr-and[]
         \valn_2 \nkrel \valk}
      @tr-IH (1, 2)
    }
    @tr-step{
      @${\wellNE \edyn{\tau'}{\valn_2}}
      @|N-S-preservation| (2, 3)
    }
    @tr-step{
      @${\edyn{\tau'}{\valn_2} \rrNSstar \valn_3 \mbox{ and } \valn_3 \nkrel \valk
         @tr-or[]
         \edyn{\tau'}{\valn_2} \rrNSstar \boundaryerror}
      @|NK-check| (4)
    }
    @list[
      @tr-if[@${\edyn{\tau'}{\valn_2} \rrNSstar \valn_3}]{
        @tr-step{
          @${\wellNE \esta{\tau}{\valn_3} : \tau}
          @|N-S-preservation| (5)
        }
        @tr-step{
          @${\esta{\tau}{\valn_3} \rrNSstar \valn_4 \mbox{ and } \valn_4 \nkrel \valk
             @tr-or[]
             \esta{\tau}{\valn_3} \rrNSstar \boundaryerror}
          @|NK-check| (a)
        }
        @tr-qed{
          (b)
        }
      }
      @tr-else[@${\edyn{\tau'}{\valn_2} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\esta{\tau}{(\edyn{\tau'}{\exprn_2})} \rrNSstar \boundaryerror}
        }
      }
    ]
  }

}

@tr-lemma[#:key "NK-S-type" @elem{@${\langN}--@${\langK} static hole typing}]{
  If @${\wellNE \ctxn[\exprn] : \tau
        @tr-and[]
        \wellKE \ctxk[\exprk] : \tagof{\tau}
        @tr-and[]
        \ctxn[\exprn] \nkrel \ctxk[\exprk]}
  @linebreak[]
  then one of the following holds:
  @itemlist[
    @item{
      @${\wellNE \exprn : \tau' @tr-and[] \wellKE \exprk : K @tr-and[] \tagof{\tau'} \subt K}

    }
    @item{
      @${\wellNE \exprn @tr-and[] \wellKE \exprk}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\ctxk}.

  TODO
}

@tr-lemma[#:key "NK-D-type" @elem{@${\langN}--@${\langK} dynamic hole typing}]{
  If @${\wellNE \ctxn[\exprn]
        @tr-and[]
        \wellKE \ctxk[\exprk]
        @tr-and[]
        \ctxn[\exprn] \nkrel \ctxk[\exprk]}
  @linebreak[]
  then one of the following holds:
  @itemlist[
    @item{
      @${\wellNE \exprn : \tau' @tr-and[] \wellKE \exprk : K @tr-and[] \tagof{\tau'} \subt K}
    }
    @item{
      @${\wellNE \exprn @tr-and[] \wellKE \exprk}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\ctxk}.

  TODO
}

@tr-lemma[#:key "NK-value" @elem{@${\langN}--@${\langK} value inversion}]{
  If @${\wellNE \exprn : \tau
        @tr-and[]
        \exprn \not\in \eerr
        @tr-and[]
        \exprn \nkrel \valk}
  @linebreak[]
  then @${\wellKE \valk : \tagof{\tau}}
}@tr-proof{
  By case analysis on @${\exprn \nkrel \valk}.

  TODO
}

@tr-lemma[#:key "NK-check" @elem{@${\langN}--@${\langK} boundary checking}]{
  @itemlist[
    @item{
      If @${\wellNE \esta{\tau}{\valn} \mbox{ and } \valn \nkrel \valk}
      then
          @${\esta{\tau}{\valn} \rrKDstar \valn_1
             @tr-and[]
             \valn_1 \nkrel \valk}
    }
    @item{
      If @${\wellNE \edyn{\tau}{\valn} : \tau
            \mbox{ and }
            \valn \nkrel \valk}
      then one of the following holds:
      @itemlist[
        @item{
          @${\edyn{\tau}{\valn} \rrKSstar \boundaryerror}
        }
        @item{
          @${\edyn{\tau}{\valn} \rrKSstar \valn_1
             @tr-and[]
             \valn_1 \nkrel \valk}
        }
      ]
    }
  ]
}@tr-proof{
  By the following two lemmas: @|NK-S-check| and @|NK-D-check|.
}

@tr-lemma[#:key "NK-S-check" @elem{@${\langN}--@${\langK} @${\vsta} checking}]{
  If @${\wellNE \esta{\tau}{\valn}
        @tr-and[]
        \valn \nkrel \valk}
  @linebreak[]
  then
      @${\esta{\tau}{\valn} \rrKDstar \valn_1
         @tr-and[]
         \valn_1 \nkrel \valk}
}@tr-proof{
  By induction on the structure of @${\tau}.

  @tr-case[@${\tau = \tnat}]{
    @tr-step{
      @${\esta{\tau}{\valn} \rrND \valn}
      definition @${\rrND}
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tint}]{
    @tr-step{
      @${\esta{\tau}{\valn} \rrND \valn}
      definition @${\rrND}
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tpair{\tau_0}{\tau_1}}]{
    @tr-step{
      @${\valn = \vpair{\valn_0}{\valn_1}}
      @|N-D-inversion| and @|N-S-canonical|
    }
    @tr-step{
      @${\valk = \vpair{\valk_0}{\valk_1}
         @tr-and[]
         \valn_0 \nkrel \valk_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @|NK-inversion|
    }
    @tr-step{
      @${\esta{\tau}{\valn} \rrND \vpair{\esta{\tau_0}{\valn_0}}{\esta{\tau_1}{\valn_1}}}
      definition @${\rrND}
    }
    @tr-step{
      @${\wellNE \esta{\tau_0}{\valn_0}
         @tr-and[]
         \wellNE \esta{\tau_1}{\valn_1}}
      @|N-S-preservation| and @|N-S-inversion|
    }
    @tr-step{
      @${\esta{\tau_0}{\valn_0} \rrKDstar \valn_{0'}
         @tr-and[]
         \valn_{0'} \nkrel \valk_0
         @tr-and[]
         \esta{\tau_1}{\valn_1} \rrKDstar \valn_{1'}
         @tr-and[]
         \valn_{1'} \nkrel \valk_1}
      @tr-IH (2, 4)
    }
    @tr-step{
      @${\esta{\tau}{\valn} \rrNDstar \vpair{\valn_{0'}}{\valn_{1'}}
         @tr-and[]
         \vpair{\valn_{0'}}{\valn_{1'}} \nkrel \valk}
      (5)
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tarr{\tau_d}{\tau_c}}]{
    @tr-step{
      @${\esta{\tau}{\valn} \rrND \vmonfun{\tau}{\valn}}
    }
    @tr-step{
      @${\vmonfun{\tau}{\valn} \nkrel \valk}
      @${\valn \nkrel \valk}
    }
    @tr-qed{}
  }
}

@tr-lemma[#:key "NK-D-check" @elem{@${\langN}--@${\langK} @${\vdyn} checking}]{
  If @${\wellNE \edyn{\tau}{\valn} : \tau
        @tr-and[]
        \valn \nkrel \valk}
  @linebreak[]
  then one of the following holds:
  @itemlist[
    @item{
      @${\edyn{\tau}{\valn} \rrKSstar \boundaryerror}
    }
    @item{
      @${\edyn{\tau}{\valn} \rrKSstar \valn_1
         @tr-and[]
         \valn_1 \nkrel \valk}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\tau}.

  @tr-case[@${\tau = \tnat} #:itemize? #false]{
    @tr-if[@${\valn \in \natural}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \valn}
        definition @${\rrNS}
      }
      @tr-qed{}
    }
    @tr-else[@${\valn \not\in \natural}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \boundaryerror}
      }
      @tr-qed{}
    }
  }

  @tr-case[@${\tau = \tint} #:itemize? #false]{
    @tr-if[@${\valn \in \integers}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \valn}
        definition @${\rrNS}
      }
      @tr-qed{}
    }
    @tr-else[@${\valn \not\in \integers}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \boundaryerror}
      }
      @tr-qed{}
    }
  }

  @tr-case[@${\tau = \tpair{\tau_0}{\tau_1}} #:itemize? #false]{
    @tr-if[@${\valn = \vpair{\valn_0}{\valn_1}}]{
      @tr-step{
        @${\valk = \vpair{\valk_0}{\valk_1}
           @tr-and[]
           \valn_0 \nkrel \valk_0
           @tr-and[]
           \valn_1 \nkrel \valk_1}
        @|NK-inversion|
      }
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \vpair{\edyn{\tau_0}{\valn_0}}{\edyn{\tau_1}{\valn_1}}}
        definition @${\rrNS}
      }
      @tr-step{
        @${\wellNE \edyn{\tau_0}{\valn_0} : \tau_0
           @tr-and[]
           \wellNE \edyn{\tau_1}{\valn_1} : \tau_1}
        @|N-S-preservation| and @|N-S-inversion|
      }
      @tr-step{
        @${\edyn{\tau_0}{\valn_0} \rrKDstar \exprn_0
           @tr-and[]
           \exprn_0 \nkrel \valk_0
           @tr-and[]
           \exprn_0 = \valn_{0'} \mbox{ or } \exprn_0 = \boundaryerror
           @tr-and[]
           \edyn{\tau_1}{\valn_1} \rrKDstar \exprn_1
           @tr-and[]
           \exprn_1 \nkrel \valk_1
           \exprn_1 = \valn_{1'} \mbox{ or } \exprn_1 = \boundaryerror}
        @tr-IH (2, 4)
      }
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNSstar \boundaryerror
           @tr-or[]
           \edyn{\tau}{\valn} \rrNSstar \vpair{\valn_{0'}}{\valn_{1'}}
           \mbox{ and }
           \vpair{\valn_{0'}}{\valn_{1'}} \nkrel \valk}
        (5)
      }
      @tr-qed{
      }
    }
    @tr-else[@${\valn \not\in \vpair{v}{v}}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \boundaryerror}
      }
      @tr-qed{}
    }
  }

  @tr-case[@${\tau = \tarr{\tau_d}{\tau_c}} #:itemize? #false]{
    @tr-if[@${\valn = \vlam{x}{\exprn}}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \vmonfun{\tau}{\valn}}
      }
      @tr-step{
        @${\vmonfun{\tau}{\valn} \nkrel \valk}
        @${\valn \nkrel \valk}
      }
      @tr-qed{}
    }
    @tr-if[@${\valn = \vmonfun{\tau_0}{\valn_0}}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \vmonfun{\tau}{\valn}}
      }
      @tr-step{
        @${\vmonfun{\tau}{\valn} \nkrel \valk}
        @${\valn \nkrel \valk}
      }
      @tr-qed{}
    }
    @tr-else[@${\valn \in i \vee \valn \in \vpair{v}{v}}]{
      @tr-step{
        @${\edyn{\tau}{\valn} \rrNS \boundaryerror}
      }
      @tr-qed{}
    }
  }
}

@tr-lemma[#:key "NK-hole-subst" @elem{@${\langN}--@${\langK} hole substitution}]{
  If @${\ctxn \nkrel \ctxk
        @tr-and[]
        \exprn \nkrel \exprk}
  @linebreak[]
  then @${\ctxn[\exprn] \nkrel \ctxk[\exprk]}
}@tr-proof{
  By induction on the structure of @${\ctxk}.

  TODO
}

@tr-lemma[#:key "NK-subst" @elem{@${\langN}--@${\langK} substitution}]{
  If @${\exprn \nkrel \exprk} and @${\valn \kerel \valk}
  then @${\vsubst{\exprn}{x}{\valn} \kerel \vsubst{\exprk}{x}{\valk}}
}@tr-proof{
  By induction on the structure of @${\exprk}.

  TODO
}

@tr-lemma[#:key "NK-inversion" @elem{@${\langN}--@${\langK} inversion}]{
  @itemlist[
    @item{
      If @${\edyn{\tau}{(\esta{\tau'}{\exprn})} \nkrel \exprk}
      then @${\exprn \nkrel \exprk}
    }
    @item{
      If @${\vpair{\valn_0}{\valn_1} \nkrel \valk}
      then @${\valk = \vpair{\valk_0}{\valk_1}}
    }
  ]
}@tr-proof{
  By the definition of @${\nkrel}.
}
