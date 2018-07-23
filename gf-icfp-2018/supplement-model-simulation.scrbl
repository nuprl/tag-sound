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
    K-S-preservation
    K-S-factor
    K-S-hole-typing
    K-subt-preservation
    K-S-inversion
    K-D-inversion)]

@appendix-title++{Simulation Lemmas}

@section{Definitions}

@(begin
   (define KE-approximation @tr-ref[#:key "KE-approximation"]{@${\langK}--@${\langE} approximation})
   (define KE-simulation @tr-ref[#:key "KE-simulation"]{@${\langK}--@${\langE} simulation})
   (define KE-S-refl @tr-ref[#:key "KE-S-refl"]{@${\langK}--@${\langE} static reflexivity})
   (define KE-D-refl @tr-ref[#:key "KE-D-refl"]{@${\langK}--@${\langE} dynamic reflexivity})
   (define KE-S-stutter @tr-ref[#:key "KE-S-stutter"]{@${\langK}--@${\langE} static value stutter})
   (define KE-D-stutter @tr-ref[#:key "KE-D-stutter"]{@${\langK}--@${\langE} dynamic value stutter})
   (define KE-hole-subst @tr-ref[#:key "KE-hole-subst"]{@${\langK}--@${\langE} hole substitution})
   (define KE-inversion @tr-ref[#:key "KE-inversion"]{@${\langK}--@${\langE} inversion})
   (define KE-subst @tr-ref[#:key "KE-subst"]{@${\langK}--@${\langE} substitution})
   (define KE-delta @tr-ref[#:key "KE-delta"]{@${\langK}--@${\langE} delta})

   (define NK-approximation @tr-ref[#:key "NK-approximation"]{@${\langN}--@${\langK} approximation})
   (define NK-simulation @tr-ref[#:key "NK-simulation"]{@${\langN}--@${\langK} simulation})
   (define NK-S-refl @tr-ref[#:key "NK-S-refl"]{@${\langN}--@${\langK} static reflexivity})
   (define NK-D-refl @tr-ref[#:key "NK-D-refl"]{@${\langN}--@${\langK} dynamic reflexivity})
   (define NK-S-type @tr-ref[#:key "NK-S-type"]{@${\langN}--@${\langK} static hole typing})
   (define NK-D-type @tr-ref[#:key "NK-D-type"]{@${\langN}--@${\langK} dynamic hole typing})
   (define NK-value @tr-ref[#:key "NK-value"]{@${\langN}--@${\langK} value inversion})
   (define NK-hole-subst @tr-ref[#:key "NK-hole-subst"]{@${\langN}--@${\langK} hole substitution})
   (define NK-subst @tr-ref[#:key "NK-subst"]{@${\langN}--@${\langK} substitution})
   (define NK-check @tr-ref[#:key "NK-check"]{@${\langN}--@${\langK} boundary checking})
   (define NK-S-check @tr-ref[#:key "NK-S-check"]{@${\langN}--@${\langK} @${\vsta} checking})
   (define NK-D-check @tr-ref[#:key "NK-D-check"]{@${\langN}--@${\langK} @${\vdyn} checking})
   (define NK-S-stutter @tr-ref[#:key "NK-S-stutter"]{@${\langN}--@${\langK} static value stutter})
   (define NK-D-stutter @tr-ref[#:key "NK-D-stutter"]{@${\langN}--@${\langK} dynamic value stutter})
   (define NK-fail @tr-ref[#:key "NK-fail"]{@${\vfromany} inversion})
   (define NK-S-app @tr-ref[#:key "NK-S-app"]{@${\langN}--@${\langK} static application})
   (define NK-D-app @tr-ref[#:key "NK-D-app"]{@${\langN}--@${\langK} dynamic application})
   (define NK-delta @tr-ref[#:key "NK-delta"]{@${\langN}--@${\langK} @${\delta}-preservation})
   (define NK-Delta-inversion @tr-ref[#:key "NK-Delta-inversion" @elem{@${\Delta} codomain inversion}])
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
  If @${\Gamma \wellM e : \tau} and @${\Gamma \wellM e : \tau \carrow e''} then
  @${e'' \kerel e}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellM e : \tau \carrow e''}
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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-qed{
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \tann{x}{\tau_d},\Gamma \wellM e : \tau_c \carrow e'
              }{
                \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} : \tarr{\tau_d}{\tau_c} \carrow \vlam{\tann{x}{\tau_d}}{e'}
              } }]{
    @tr-step{
      @${e' \kerel e}
      @tr-IH
    }
    @tr-qed{
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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-step{
      @${\eapp{e_0'}{e_1'} \kerel \eapp{e_0}{e_1}}
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
      @${e' \kerel e}
      @tr-IH
    }
    @tr-step{
      @${\efst{e'} \kerel \efst{e}}
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
      @${e' \kerel e}
      @tr-IH
    }
    @tr-step{
      @${\esnd{e'} \kerel \esnd{e}}
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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-qed{
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
      @${e' \kerel e}
      @tr-IH
    }
    @tr-qed{
    }
  }
}

@tr-lemma[#:key "KE-D-refl" @elem{@${\langK}--@${\langE} dynamic reflexivity}]{
  If @${\Gamma \wellM e} and @${\Gamma \wellM e \carrow e''} then
  @${e'' \kerel e}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellM e \carrow e''} judgment.

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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-qed{
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                x,\Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \vlam{x}{e} \carrow \vlam{x}{e'}
              }}]{
    @tr-step{
      @${e' \kerel e}
      @tr-IH
    }
    @tr-qed{
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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-qed{
    }
  }

  @tr-case[#:box? #true
           @${\inferrule*{
                \Gamma \wellM e \carrow e'
              }{
                \Gamma \wellM \eunop{e} \carrow \eunop{e'}
              }}]{
    @tr-step{
      @${e' \kerel e}
      @tr-IH
    }
    @tr-qed{
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
      @${e_0' \kerel e_0
         @tr-and[]
         e_1' \kerel e_1}
      @tr-IH
    }
    @tr-qed{
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
  If @${\ctxk[\exprk_0] \kerel \ctxe[\expre_0]}
  and @${\ctxe[\expre_0] \ccES \ctxe[\expre_1]}
  @linebreak[]
  then @${\ctxk[\exprk_0] \rrKSstar \ctxk[\exprk_1]}
  and @${\ctxk[\exprk_1] \kerel \ctxe[\expre_1]}
}@tr-proof{
  By case analysis on @${\expre_0 \rrES \expre_1}.

  @tr-case[@${\edyn{\tau_0}{\vale_0} \rrES \vale_0}]{
    @tr-step{
      @${\exprk_0 = \edyn{\tau_0}{\exprk_{0'}}}
      definition @${\kerel}
    }
    @tr-step{
      @${\exprk_{0'} \kerel \vale_0}
      (1)
    }
    @tr-step{
      @${\wellKE \exprk_{0'}}
      @|K-S-inversion|
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror}
      @|KE-D-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror}]{
        @tr-step{
          @${\exprk_0 \rrKSstar \boundaryerror}
        }
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\expre_1]}
          @|KE-hole-subst|
        }
      }
      @tr-else[@${\exprk_{0'} \rrKDstar \valk_{0}}]{
        @tr-step{
          @${\exprk_0 \rrKSstar \valk_0}
        }
        @tr-qed{
          @${\ctxk[\valk_0] \kerel \ctxe[\vale_0]}
          @|KE-hole-subst|
        }
      }
    ]
  }

  @tr-case[@${\esta{\tau_0}{\vale_0} \rrES \vale_0}]{
    @tr-step{
      @${\exprk_0 = \esta{\tau_0}{\exprk_{0'}}}
      definition @${\kerel}
    }
    @tr-step{
      @${\exprk_{0'} \kerel \vale_0}
      (1)
    }
    @tr-step{
      @${\wellKE \exprk_{0'} : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-step{
      @${\exprk_{0'} \rrKSstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-D-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKSstar \boundaryerror}]{
        @tr-step{
          @${\exprk_0 \rrKDstar \boundaryerror}
        }
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\expre_1]}
          @|KE-hole-subst|
        }
      }
      @tr-else[@${\exprk_{0'} \rrKSstar \valk_{0}}]{
        @tr-step{
          @${\exprk_0 \rrKDstar \valk_0}
        }
        @tr-qed{
          @${\ctxk[\valk_0] \kerel \ctxe[\vale_0]}
          @|KE-hole-subst|
        }
      }
    ]
  }

  @tr-case[@${\eapp{\vale_0}{\vale_1} \rrES \tagerror
              @tr-and[4]
              \wellKE \exprk_0 : K_0}]{
    @tr-step{
      @${\exprk_0 = \eapp{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKSstar \valk_{0'} \mbox{ and } \valk_{0'} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-S-stutter|
    }
    @tr-if[@${\exprk_{0'} \rrKSstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKSstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\exprk_{1'} \rrKSstar \valk_{1'} \mbox{ and } \valk_{1'} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKSstar \boundaryerror}
      @|KE-S-stutter|
    }
    @tr-if[@${\exprk_{1'} \rrKSstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKSstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\vale_0 \in \integers @tr-or[] \vale_0 \in \vpair{v}{v'}}
      definition @${\rrES}
    }
    @list[
      @tr-if[@${\vale_0 \in \integers}]{
        @tr-step{
          @${\valk_{0'} \in \integers}
          (2)
        }
        @tr-step{
          @${\wellKE \eapp{\valk_{0'}}{\valk_{1'}} : K_0}
          @|K-S-preservation|
        }
        @tr-contradiction{
          (a, b)
        }
      }
      @tr-else[@${\vale_0 \in \vpair{v}{v'}}]{
        @tr-step{
          @${\valk_{0'} \in \vpair{v}{v'}}
          (2)
        }
        @tr-step{
          @${\wellKE \eapp{\valk_{0'}}{\valk_{1'}} : K_0}
          @|K-S-preservation|
        }
        @tr-contradiction{
          (a, b)
        }
      }
    ]
  }

  @tr-case[@${\eapp{\vale_0}{\vale_1} \rrES \tagerror
              @tr-and[4]
              \wellKE \exprk_0}]{
    @tr-step{
      @${\exprk_0 = \eapp{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0'} \mbox{ and } \valk_{0'} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror}
      @|KE-D-stutter|
    }
    @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\exprk_{1'} \rrKDstar \valk_{1'} \mbox{ and } \valk_{1'} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKDstar \boundaryerror}
      @|KE-S-stutter|
    }
    @tr-if[@${\exprk_{1'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\vale_0 \in \integers @tr-or[] \vale_0 \in \vpair{v}{v'}}
      definition @${\rrES}
    }
    @tr-step{
      @${\valk_{0'} \in \integers @tr-or[] \valk_{0'} \in \vpair{v}{v'}}
      (2)
    }
    @tr-step{
      @${\exprk \rrKDstar \tagerror}
    }
    @tr-qed{
      @${\ctxk[\tagerror] \kerel \ctxe[\tagerror]}
    }
  }

  @tr-case[@${\eapp{(\vlam{x}{\expre})}{\vale_1}
               \rrES \vsubst{\expre}{x}{\vale_1}}]{
    @tr-step{
      @${\exprk_0 = \eapp{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror}
      @|KE-D-stutter|
    }
    @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\exprk_{1'} \rrKDstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKDstar \boundaryerror}
      @|KE-S-stutter|
    }
    @tr-if[@${\exprk_{1'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\valk_0 = \vlam{x}{\exprk} \mbox{ and } \exprk \kerel \expre}
      (2)
    }
    @tr-step{
      @${\eapp{\valk_0}{\valk_1} \rrKD \vsubst{\exprk}{x}{\valk_1}
         @tr-or[]
         \eapp{\valk_0}{\valk_1} \rrKS \vsubst{\exprk}{x}{\valk_1}}
    }
    @tr-step{
      @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
      @|KE-subst|
    }
    @tr-qed{
      @${\ctxk[\vsubst{\exprk}{x}{\valk_1}] \kerel \ctxe[\vsubst{\expre}{x}{\vale_1}]}
      @|KE-hole-subst|
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau}}{\expre_0})}{\vale_1}
               \rrES \vsubst{\expre_0}{x}{\vale_1}}]{
    @tr-step{
      @${\exprk_0 = \eapp{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror}
      @|KE-D-stutter|
    }
    @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\exprk_{1'} \rrKDstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKDstar \boundaryerror}
      @|KE-S-stutter|
    }
    @tr-if[@${\exprk_{1'} \rrKDstar \boundaryerror}]{
      @tr-step{
        @${\exprk \rrKDstar \boundaryerror}
      }
      @tr-qed{
        @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
      }
    }
    @tr-step{
      @${\valk_0 = \vlam{\tann{x}{\tau}}{\exprk} \mbox{ and } \exprk \kerel \expre}
      (2)
    }
    @tr-step{
      @${\eapp{\valk_0}{\valk_1} \rrKD \vsubst{\exprk}{x}{\valk_1}
         @tr-or[]
         \eapp{\valk_0}{\valk_1} \rrKS \boundaryerror \mbox{ and } \efromany{\tagof{\tau}}{\valk_1} = \boundaryerror
         @tr-or[]
         \eapp{\valk_0}{\valk_1} \rrKS \vsubst{\exprk}{x}{\efromany{\tagof{\tau}}{\valk_1}}}
    }
    @list[
      @tr-if[@${\eapp{\valk_0}{\valk_1} \rrKD \vsubst{\exprk}{x}{\valk_1}}]{
        @tr-step{
          @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
          @|KE-subst|
        }
        @tr-qed{
          @${\ctxk[\vsubst{\exprk}{x}{\valk_1}] \kerel \ctxe[\vsubst{\expre}{x}{\vale_1}]}
          @|KE-hole-subst|
        }
      }
      @tr-if[@${\eapp{\valk_0}{\valk_1} \rrKS \boundaryerror}]{
        @tr-step{
          @${\exprk \rrKSstar \boundaryerror}
        }
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\boundaryerror]}
        }
      }
      @tr-else[@${\eapp{\valk_0}{\valk_1} \rrKS \vsubst{\exprk}{x}{\efromany{\tagof{\tau}}{\valk_1}}}]{
        @tr-step{
          @${\efromany{\tagof{\tau}}{\valk_1} = \valk_1}
        }
        @tr-step{
          @${\vsubst{\exprk}{x}{\valk_1} \kerel \vsubst{\expre}{x}{\vale_1}}
          @|KE-subst|
        }
        @tr-qed{
          @${\ctxk[\vsubst{\exprk}{x}{\valk_1}] \kerel \ctxe[\vsubst{\expre}{x}{\vale_1}]}
          @|KE-hole-subst|
        }
      }
    ]
  }

  @tr-case[@${\eunop{\vale_0} \rrES \tagerror}]{
    @tr-step{
      @${\exprk_0 = \eunop{\exprk_{0'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{0'} \rrKSstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKDstar \valk_{0}}]{
        @tr-step{
          @${\vale_0 \not\in \vpair{v}{v}}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \not\in \vpair{v}{v}}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-step{
          @${\eunop{\valk_0} \rrKD \tagerror}
          definition @${\rrKD}
        }
        @tr-qed{
          @${\ctxk[\tagerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror}]{
        @tr-step{
          @${\exprk \rrKDstar \boundaryerror}
        }
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-if[@${\exprk_{0'} \rrKSstar \valk_{0}}]{
        @tr-step{
          @${\wellKE \eunop{\exprk_{0'}} : K_0}
        }
        @tr-step{
          @${\wellKE \eunop{\valk_{0}} : K_0}
          @|K-S-preservation|
        }
        @tr-step{
          @${\vale_0 \not\in \vpair{v}{v}}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \not\in \vpair{v}{v}}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-contradiction{
          (b)
        }
      }
      @tr-else[@${\exprk_{0'} \rrKSstar \boundaryerror}]{
        @tr-step{
          @${\exprk \rrKSstar \boundaryerror}
        }
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
        }
      }
    ]
  }


  @tr-case[@${\eunop{\vale_0} \rrES \delta(\vunop, \vale_0)}]{
    @tr-step{
      @${\exprk_0 = \eunop{\exprk_{0'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{0'} \rrKSstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror
                @tr-or[2]
                \exprk_{0'} \rrKSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-if[@${\exprk_{0'} \rrKDstar \valk_{0}}]{
        @tr-step{
          @${\vale_0 \in \vpair{v}{v}}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \in \vpair{v}{v}}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-step{
          @${\eunop{\valk_0} \rrKD \delta(\vunop, \valk_0)}
          definition @${\rrKD}
        }
        @tr-step{
          @${\delta(\vunop, \valk_0) \kerel \delta(\vunop, \vale_0)}
          @|KE-delta|
        }
        @tr-qed{
          @${\ctxk[\delta(\vunop, \valk_0)] \kerel \ctxe[\delta(\vunop, \vale_0)]}
        }
      }
      @tr-else[@${\exprk_{0'} \rrKSstar \valk_{0}}]{
        @tr-step{
          @${\vale_0 \in \vpair{v}{v}}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \in \vpair{v}{v}}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-step{
          @${\eunop{\valk_0} \rrKS \delta(\vunop, \valk_0)}
          definition @${\rrKS}
        }
        @tr-step{
          @${\delta(\vunop, \valk_0) \kerel \delta(\vunop, \vale_0)}
          @|KE-delta|
        }
        @tr-qed{
          @${\ctxk[\delta(\vunop, \valk_0)] \kerel \ctxe[\delta(\vunop, \vale_0)]}
        }
      }
    ]
  }

  @tr-case[@${\ebinop{\vale_0}{\vale_1} \rrES \tagerror}]{
    @tr-step{
      @${\exprk_0 = \ebinop{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{0'} \rrKSstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @tr-step{
      @${\exprk_{1'} \rrKDstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{1'} \rrKSstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror
                @tr-or[2]
                \exprk_{0'} \rrKSstar \boundaryerror
                @tr-or[2]
                \exprk_{1'} \rrKDstar \boundaryerror
                @tr-or[2]
                \exprk_{1'} \rrKSstar \boundaryerror }]{
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-if[@${\exprk_{0'} \rrKDstar \valk_{0}
                @tr-and[2]
                \exprk_{1'} \rrKDstar \valk_{1}}]{
        @tr-step{
          @${\vale_0 \not\in \integers
             @tr-or[]
             \vale_1 \not\in \integers}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \not\in \integers
             @tr-or[]
             \valk_1 \not\in \integers}
          (a)
        }
        @tr-step{
          @${\ebinop{\valk_0}{\valk_1} \rrKD \tagerror}
          definition @${\rrKD}
        }
        @tr-qed{
          @${\ctxk[\tagerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-else[@${\exprk_{0'} \rrKSstar \valk_{0}
                  @tr-and[2]
                  \expre_{1'} \rrKSstar \valk_{1}}]{
        @tr-step{
          @${\wellKE \ebinop{\exprk_{0'}}{\exprk_{1'}} : K_0}
        }
        @tr-step{
          @${\wellKE \ebinop{\valk_0}{\valk_1} : K_0}
          @|K-S-preservation|
        }
        @tr-step{
          @${\vale_0 \not\in \integers
             @tr-or[]
             \vale_1 \not\in \integers}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \not\in \integers
             @tr-or[]
             \valk_1 \not\in \integers}
          (c)
        }
        @tr-contradiction{
          (b)
        }
      }
    ]
  }

  @tr-case[@${\ebinop{\vale_0}{\vale_1} \rrES \delta(\vbinop, \vale_0, \vale_1)}]{
    @tr-step{
      @${\exprk_0 = \ebinop{\exprk_{0'}}{\exprk_{1'}}}
      @${\exprk_0 \kerel \expre_0}
    }
    @tr-step{
      @${\exprk_{0'} \rrKDstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{0'} \rrKSstar \valk_{0} \mbox{ and } \valk_{0} \kerel \vale_0
         @tr-or[]
         \exprk_{0'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @tr-step{
      @${\exprk_{1'} \rrKDstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKDstar \boundaryerror
         @tr-or[]
         \exprk_{1'} \rrKSstar \valk_{1} \mbox{ and } \valk_{1} \kerel \vale_1
         @tr-or[]
         \exprk_{1'} \rrKSstar \boundaryerror}
      @|KE-D-stutter| or @|KE-S-stutter|
    }
    @list[
      @tr-if[@${\exprk_{0'} \rrKDstar \boundaryerror
                @tr-or[2]
                \exprk_{0'} \rrKSstar \boundaryerror
                @tr-or[2]
                \exprk_{1'} \rrKDstar \boundaryerror
                @tr-or[2]
                \exprk_{1'} \rrKSstar \boundaryerror }]{
        @tr-qed{
          @${\ctxk[\boundaryerror] \kerel \ctxe[\tagerror]}
        }
      }
      @tr-if[@${\exprk_{0'} \rrKDstar \valk_{0}
                @tr-and[2]
                \exprk_{1'} \rrKDstar \valk_{1}}]{
        @tr-step{
          @${\vale_0 \in \integers
             @tr-and[]
             \vale_1 \in \integers}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \in \integers}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-step{
          @${\valk_1 \in \integers}
          @${\valk_1 \kerel \vale_1}
        }
        @tr-step{
          @${\ebinop{\valk_0}{\valk_1} \rrKD \delta(\vbinop, \valk_0, \valk_1)}
          definition @${\rrKD}
        }
        @tr-step{
          @${\delta(\vbinop, \valk_0, \valk_1) \kerel \delta(\vbinop, \vale_0, \vale_1)}
          @|KE-delta|
        }
        @tr-qed{
          @${\ctxk[\delta(\vbinop, \valk_0, \valk_1)] \kerel \ctxe[\delta(\vbinop, \vale_0, \vale_1)]}
        }
      }
      @tr-else[@${\exprk_{0'} \rrKSstar \valk_{0}
                  @tr-and[2]
                  \expre_{1'} \rrKSstar \valk_{1}}]{
        @tr-step{
          @${\vale_0 \in \integers
             @tr-and[]
             \vale_1 \in \integers}
          definition @${\rrES}
        }
        @tr-step{
          @${\valk_0 \in \integers}
          @${\valk_0 \kerel \vale_0}
        }
        @tr-step{
          @${\valk_1 \in \integers}
          @${\valk_1 \kerel \vale_1}
        }
        @tr-step{
          @${\ebinop{\valk_0}{\valk_1} \rrKS \delta(\vbinop, \valk_0, \valk_1)}
          definition @${\rrKS}
        }
        @tr-step{
          @${\delta(\vbinop, \valk_0, \valk_1) \kerel \delta(\vbinop, \vale_0, \vale_1)}
          @|KE-delta|
        }
        @tr-qed{
          @${\ctxk[\delta(\vbinop, \valk_0, \valk_1)] \kerel \ctxe[\delta(\vbinop, \vale_0, \vale_1)]}
        }
      }
    ]
  }

}

@tr-lemma[#:key "KE-S-stutter" @elem{@${\langK}--@${\langE} static value stutter}]{
  If @${\exprk \kerel \vale} and @${\wellKE \exprk : K}
  then one of the following holds:
  @itemlist[
    @item{
      @${\exprk \rrKSstar \valk} and @${\valk \kerel \vale}
    }
    @item{
      @${\exprk \rrKSstar \boundaryerror}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\exprk},
   and case analysis on @${\exprk \kerel \vale}.

  @tr-case[@${\exprk \mbox{ is a value}}]{
    @tr-qed{}
  }

  @tr-case[@${\exprk = \echk{K}{\exprk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \vale}
      definition @${\kerel}
    }
    @tr-step{
      @${\wellKE \exprk_0 : \kany}
    }
    @tr-step{
      @${\exprk_0 \rrKSstar \valk_0 \mbox{ and } \valk_0 \kerel \vale
         @tr-or[]
         \exprk_0 \rrKSstar \boundaryerror}
      @tr-IH
    }
    @list[
      @tr-if[@${\exprk_0 \rrKSstar \boundaryerror}]{
        @tr-qed{
          @${\exprk \rrKSstar \boundaryerror}
        }
      }
      @tr-if[@${\exprk_0 \rrKSstar \valk_0
                @tr-and[2]
                \efromany{K}{\exprk_0} = \boundaryerror}]{
        @tr-qed{
          @${\exprk \rrKSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprk_0 \rrKSstar \valk_0
                @tr-and[2]
                \efromany{K}{\exprk_0} = \valk_0}]{
        @tr-qed{
          @${\exprk \rrKSstar \valk_0}
        }
      }
    ]
  }

  @tr-case[@${\exprk = \edynfake{\exprk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \vale}
      definition @${\kerel}
    }
    @tr-step{
      @${\wellKE \exprk_0}
    }
    @tr-step{
      @${\exprk_0 \rrKDstar \valk_0 \mbox{ and } \valk_0 \kerel \vale
         @tr-or[]
         \exprk_0 \rrKDstar \boundaryerror}
      @|KE-D-stutter|
    }
    @list[
      @tr-if[@${\exprk_0 \rrKDstar \boundaryerror}]{
        @tr-qed{
          @${\exprk \rrKSstar \boundaryerror}
        }
      }
      @tr-else[""]{
        @tr-qed{
          @${\exprk \rrKSstar \valk_0}
        }
      }
    ]
  }

  @tr-case[@${\exprk = \estafake{\valk_0}}]{
    @tr-contradiction{
      @${\wellKE \exprk : K}
    }
  }

}

@tr-lemma[#:key "KE-D-stutter" @elem{@${\langK}--@${\langE} dynamic value stutter}]{
  If @${\exprk \kerel \vale} and @${\wellKE \exprk}
  then one of the following holds:
  @itemlist[
    @item{
      @${\exprk \rrKDstar \valk} and @${\valk \kerel \vale}
    }
    @item{
      @${\exprk \rrKDstar \boundaryerror}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\exprk},
   and case analysis on @${\exprk \kerel \vale}.

  @tr-case[@${\exprk \mbox{ is a value}}]{
    @tr-qed{}
  }

  @tr-case[@${\exprk = \echk{K}{\exprk_0}}]{
    @tr-contradiction{
      @${\wellKE \exprk}
    }
  }

  @tr-case[@${\exprk = \edynfake{\exprk_0}}]{
    @tr-contradiction{
      @${\wellKE \exprk}
    }
  }

  @tr-case[@${\exprk = \estafake{\valk_0}}]{
    @tr-step{
      @${\exprk_0 \kerel \vale}
      definition @${\kerel}
    }
    @tr-step{
      @${\wellKE \exprk_0 : \kany}
    }
    @tr-step{
      @${\exprk_0 \rrKSstar \valk_0 \mbox{ and } \valk_0 \kerel \vale
         @tr-or[]
         \exprk_0 \rrKSstar \boundaryerror}
      @|KE-S-stutter|
    }
    @list[
      @tr-if[@${\exprk_0 \rrKSstar \boundaryerror}]{
        @tr-qed{
          @${\exprk \rrKDstar \boundaryerror}
        }
      }
      @tr-else[""]{
        @tr-qed{
          @${\exprk \rrKDstar \valk_0}
        }
      }
    ]
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

@tr-lemma[#:key "KE-delta" @elem{@${\langK}--@${\langE} @${\delta}-preservation}]{
  @itemlist[
    @item{
      If @${\valk \kerel \vale}
      and @${\delta(\vunop, \valk)} is defined
      then @${\delta(\vunop, \valk) \kerel \delta(\vunop, \vale)}
    }
    @item{
      If @${\valk_0 \kerel \vale_0}
      and @${\valk_1 \kerel \vale_1}
      and @${\delta(\vbinop, \valk_0, \valk_1)} is defined
      then @${\delta(\vbinop, \valk_0, \valk_1) \kerel \delta(\vbinop, \vale_0, \vale_1)}
    }
  ]
}@tr-proof{
  @tr-case[@${\vunop = \vfst}]{
    @tr-step{
      @${\valk = \vpair{\valk_0}{\valk_1}}
      @${\delta(\vfst, \valk)} is defined
    }
    @tr-step{
      @${\vale = \vpair{\vale_0}{\vale_1}
         @tr-and[]
         \valk_0 \kerel \valk_0 \mbox{ and } \valk_1 \kerel \vale_1}
      @${\kerel}
    }
    @tr-step{
      @${\delta(\vfst, \valk) = \valk_0
         @tr-and[]
         \delta(\vfst, \vale) = \vale_0}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\vunop = \vsnd}]{
    @tr-step{
      @${\valk = \vpair{\valk_0}{\valk_1}}
      @${\delta(\vsnd, \valk)} is defined
    }
    @tr-step{
      @${\vale = \vpair{\vale_0}{\vale_1}
         @tr-and[]
         \valk_0 \kerel \vale_0 \mbox{ and } \valk_1 \kerel \vale_1}
      @${\kerel}
    }
    @tr-step{
      @${\delta(\vsnd, \valk) = \valk_1
         @tr-and[]
         \delta(\vsnd, \vale) = \vale_1}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\vbinop = \vsum}]{
    @tr-step{
      @${\valk_0 \in \integers
         @tr-and[]
         \valk_1 \in \integers}
      @${\delta(\vbinop, \valk_0, \valk_1)} is defined
    }
    @tr-step{
      @${\valk_0 = \vale_0
          @tr-and[]
          \valk_1 = \vale_1}
      @${\kerel}
    }
    @tr-qed[]
  }

  @tr-case[@${\vbinop = \vquotient}]{
    @tr-step{
      @${\valk_0 \in \integers
         @tr-and[]
         \valk_1 \in \integers}
      @${\delta(\vbinop, \valk_0, \valk_1)} is defined
    }
    @tr-step{
      @${\valk_0 = \vale_0
          @tr-and[]
          \valk_1 = \vale_1}
      @${\kerel}
    }
    @tr-qed[]
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
      @${e' \nkrel e}
      @tr-IH
    }
    @tr-qed{
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
         \ctxk[\exprk_0] \ccKS \ctxk[\exprk_1]}
  @linebreak[]
  then @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_n]}
  and @${\ctxn[\exprn_n] \nkrel \ctxk[\exprk_1]}
}@tr-proof{
  By case analysis on @${\ctxk[\exprk_0] \ccKS \ctxk[\exprk_1]}

  @tr-case[@${\ctxk[\edynfake{\valk_0}] \ccKS \ctxk[\valk_0]}]{
    @tr-step{
      @${\exprn_0 = \edyn{\tau_0}{\exprn_{0'}}
         @tr-and[]
         \exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'}}
      @${\wellNE \ctxn[\exprn_0] : \tau}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\wellNE \valn_0}
          @|N-S-preservation|
        }
        @tr-step{
          @${\edyn{\tau_0}{\valn_0} \rrNSstar \exprn_{1'}
             @tr-and[]
             \exprn_{1'} \nkrel \valk_0
             @tr-and[]
             \exprn_{1'} \in v \mbox{ or } \exprn_{1} = \boundaryerror}
          @|NK-check|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_{1}]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\estafake{\valk_0}] \ccKS \ctxk[\valk_0]}]{
    @tr-step{
      @${\exprn_0 = \esta{\tau_0}{\exprn_{0'}}
         @tr-and[]
         \exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_0}
      @${\wellNE \ctxn[\exprn_0] : \tau}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\wellNE \valn_0 : \tau_0}
          @|N-D-preservation|
        }
        @tr-step{
          @${\esta{\tau_0}{\valn_0} \rrNDstar \exprn_{1'}
             @tr-and[]
             \exprn_{1'} \nkrel \valk_0
             @tr-and[]
             \exprn_{1'} \in v \mbox{ or } \exprn_{1} = \boundaryerror}
          @|NK-check|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_{1}]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\edyn{\tau_0}{\valk_0}] \ccKS \ctxk[\boundaryerror]}]{
    @tr-step{
      @${\exprn_0 = \edyn{\tau_0}{\exprn_{0'}}
         @tr-and[]
         \exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'}}
      @${\wellNE \ctxn[\exprn_0] : \tau}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\efromany{\tagof{\tau_0}}{\valk_0} = \boundaryerror}
          @${\ctxk[\edyn{\tau_0}{\valk_0}] \ccKS \ctxk[\boundaryerror]}
        }
        @tr-step{
          @${\efromdynN{\tau_0}{\valn_0} = \boundaryerror}
          @|NK-fail|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\edyn{\tau_0}{\valk_0}] \ccKS \ctxk[\valk_0]}]{
    @tr-step{
      @${\exprn_0 = \edyn{\tau_0}{\exprn_{0'}}
         @tr-and[]
         \exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'}}
      @${\wellNE \ctxn[\exprn_0] : \tau}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\wellNE \valn_0}
          @|N-S-preservation|
        }
        @tr-step{
          @${\edyn{\tau_0}{\valn_0} \rrNSstar \exprn_{1'}
             @tr-and[]
             \exprn_{1'} \nkrel \valk_0
             @tr-and[]
             \exprn_{1'} \in v \mbox{ or } \exprn_{1} = \boundaryerror}
          @|NK-check|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_{1}]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\esta{\tau_0}{\valk_0}] \ccKS \ctxk[\valk_0]}]{
    @tr-step{
      @${\exprn_0 = \esta{\tau_0}{\exprn_{0'}}
         @tr-and[]
         \exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_0}
      @${\wellNE \ctxn[\exprn_0] : \tau}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\wellNE \valn_0 : \tau_0}
          @|N-D-preservation|
        }
        @tr-step{
          @${\esta{\tau_0}{\valn_0} \rrNDstar \exprn_{1'}
             @tr-and[]
             \exprn_{1'} \nkrel \valk_0
             @tr-and[]
             \exprn_{1'} \in v \mbox{ or } \exprn_{1} = \boundaryerror}
          @|NK-check|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_{1}]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\echk{K_0}{\valk_0}] \ccKS \ctxk[\boundaryerror]}]{
    @tr-step{
      @${\wellKE \echk{K_0}{\valk_0} : K_0}
      @${\wellKE \ctxk[\exprk_0] : K}
    }
    @tr-step{
      @${\wellNE \exprn_0 : \tau_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_0 \rrNSstar \boundaryerror}
      @|NK-S-stutter| (2)
    }
    @list[
      @tr-if[@${\exprn_0 \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-step{
          @${\wellKE \valk_0 : \tagof{\tau_0}}
          @|NK-value| (2, 3)
        }
        @tr-step{
          @${K_0 = \tagof{\tau_0}}
          @|K-S-completion|, @|NK-S-refl|, @|N-S-preservation|, and @|K-S-preservation|
        }
        @tr-step{
          @${\echk{K_0}{\valk_0} \rrKS \valk_0}
          definition @${\rrKS}
        }
        @tr-contradiction{
          @${\ctxk[\echk{K_0}{\valk_0}] \ccKS \ctxk[\boundaryerror]} (b)
        }
      }
      @tr-else[@${\exprn_0 \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\echk{K_0}{\valk_0}] \ccKS \ctxk[\valk_0]}]{
    @tr-step{
      @${\wellKE \echk{K_0}{\valk_0} : K_0}
      @${\wellKE \ctxk[\exprk_0] : K}
    }
    @tr-step{
      @${\wellNE \exprn_0 : \tau_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_0 \rrNSstar \boundaryerror}
      @|NK-S-stutter| (2)
    }
    @list[
      @tr-if[@${\exprn_0 \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \valn_0}
        }
      }
      @tr-else[@${\exprn_0 \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\eapp{\valk_0}{\valk_1}] \ccKS \ctxk[\exprk_2]
              @tr-and[]
              \wellKE \eapp{\valk_0}{\valk_1} : K'}]{
    @tr-step{
      @${\wellNE \exprn_0 : \tau_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 = \eapp{\exprn_{0'}}{\exprn_{1'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter| (1, 2)
    }
    @tr-step{
      @${\exprn_{1'} \rrNSstar \valn_1 \mbox{ and } \valn_1 \nkrel \valk_1
         @tr-or[]
         \exprn_{1'} \rrNSstar \boundaryerror}
      @|NK-S-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_0
                @tr-and[]
                \exprn_{1'} \rrNSstar \valn_1}]{
        @tr-step{
          @${\eapp{\valn_0}{\valn_1} \rrNSstar \exprn_2
             @tr-and[]
             \exprn_2 \nkrel \exprk_2}
          @|NK-S-app| (1)
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\exprn_2]}
        }
      }
      @tr-if[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{1'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\eapp{\valk_0}{\valk_1}] \ccKS \ctxk[\exprk_2]
              @tr-and[]
              \wellKE \eapp{\valk_0}{\valk_1}}]{
    @tr-step{
      @${\wellNE \exprn_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 = \eapp{\exprn_{0'}}{\exprn_{1'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_0 \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter| (1, 2)
    }
    @tr-step{
      @${\exprn_{1'} \rrNDstar \valn_1 \mbox{ and } \valn_1 \nkrel \valk_1
         @tr-or[]
         \exprn_{1'} \rrNDstar \boundaryerror}
      @|NK-D-stutter| (1, 2)
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_0
                @tr-and[]
                \exprn_{1'} \rrNDstar \valn_1}]{
        @tr-step{
          @${\eapp{\valn_0}{\valn_1} \rrNDstar \exprn_2
             @tr-and[]
             \exprn_2 \nkrel \exprk_2}
          @|NK-D-app| (1)
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNDstar \ctxn[\exprn_2]}
        }
      }
      @tr-if[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{1'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\eunop{\valk_0}] \ccKS \ctxk[\delta(\vunop, \valk_0)]
              @tr-and[]
              \wellKE \eunop{\valk_0} : K_0}]{
    @tr-step{
      @${\wellNE \exprn_0 : \tau_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 = \eunop{\exprn_{0'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_{0'}}
      @|N-S-inversion| (1, 2)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_{0}}]{
        @tr-step{
          @${\eunop{\valn_{0}} \rrNS \delta(\vunop, \valn_0}
          @${\rrNS}
        }
        @tr-step{
          @${\delta(\vunop, \valn_0) \nkrel \delta(\vunop, \valk_0)}
          @|NK-delta|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\delta(\vunop, \valn_0)]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\eunop{\valk_0}] \ccKS \ctxk[\delta(\vunop, \valk_0)]
              @tr-and[]
              \wellKE \eunop{\valk_0}}]{
    @tr-step{
      @${\wellNE \exprn_0}
      @|NK-D-type|
    }
    @tr-step{
      @${\exprn_0 = \eunop{\exprn_{0'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_{0'}}
      @|N-D-inversion| (1, 2)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_{0}}]{
        @tr-step{
          @${\eunop{\valn_{0}} \rrND \delta(\vunop, \valn_0)}
          @${\rrND}
        }
        @tr-step{
          @${\delta(\vunop, \valn_0) \nkrel \delta(\vunop, \valk_0)}
          @|NK-delta|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\delta(\vunop, \valn_0)]}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\eunop{\valk_0}] \ccKS \ctxk[\tagerror]}]{
    @tr-step{
      @${\wellKE \eunop{\valk_0}}
      definition @${\ccKS}
    }
    @tr-step{
      @${\wellNE \exprn_0}
      @|NK-D-type| (1)
    }
    @tr-step{
      @${\exprn_0 = \eunop{\exprn_{0'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_{0'}}
      @|N-D-inversion| (2, 3)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_{0}}]{
        @tr-step{
          @elem{@${\delta(\vunop, \valk_0} is undefined}
          definition @${\rrND}
        }
        @tr-step{
          @${\valk_0 \not\in \vpair{v}{v}}
          (a)
        }
        @tr-step{
          @${\valn_0 \not\in \vpair{v}{v}}
          @${\valn_0 \nkrel \valk_0}
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \tagerror}
        }
      }
      @tr-else[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\ebinop{\valk_0}{\valk_1}] \ccKS \ctxk[\delta(\vbinop, \valk_0, \valk_1)]
              @tr-and[]
              \wellKE \ebinop{\valk_0}{\valk_1} : K_0}]{
    @tr-step{
      @${\wellNE \exprn_0 : \tau_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 = \ebinop{\exprn_{0'}}{\exprn_{1'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_{0'}
         @tr-and[]
         \wellNE \exprn_{1'} : \tau_{1'}}
      @|N-S-inversion| (1, 2)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0
         @tr-and[]
         \exprn_{1'} \nkrel \valk_1}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNSstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNSstar \boundaryerror}
      @|NK-S-stutter|
    }
    @tr-step{
      @${\exprn_{1'} \rrNSstar \valn_{1} \mbox{ and } \valn_1 \nkrel \valk_1
         @tr-or[]
         \exprn_{1'} \rrNSstar \boundaryerror}
      @|NK-S-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNSstar \valn_{0}
                @tr-and[]
                \exprn_{1'} \rrNSstar \valn_1}]{
        @tr-step{
          @${\ebinop{\valn_{0}}{\valn_{1}} \rrNS \delta(\vbinop, \valn_0, \valn_1)}
          @${\rrND}
        }
        @tr-step{
          @${\delta(\vbinop, \valn_0, \valn_1) \nkrel \delta(\vbinop, \valk_0, \valk_1)}
          @|NK-delta|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\delta(\vbinop, \valn_0, \valn_1)]}
        }
      }
      @tr-if[@${\exprn_{0'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{1'} \rrNSstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\ebinop{\valk_0}{\valk_1}] \ccKS \ctxk[\delta(\vbinop, \valk_0, \valk_1)]
              @tr-and[]
              \wellKE \ebinop{\valk_0}{\valk_1}}]{
    @tr-step{
      @${\wellNE \exprn_0}
      @|NK-S-type|
    }
    @tr-step{
      @${\exprn_0 = \ebinop{\exprn_{0'}}{\exprn_{1'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'}
         @tr-and[]
         \wellNE \exprn_{1'}}
      @|N-S-inversion| (1, 2)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0
         @tr-and[]
         \exprn_{1'} \nkrel \valk_1}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @tr-step{
      @${\exprn_{1'} \rrNDstar \valn_{1} \mbox{ and } \valn_1 \nkrel \valk_1
         @tr-or[]
         \exprn_{1'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_{0}
                @tr-and[]
                \exprn_{1'} \rrNDstar \valn_1}]{
        @tr-step{
          @${\ebinop{\valn_{0}}{\valn_{1}} \rrND \delta(\vbinop, \valn_0, \valn_1)}
          @${\rrND}
        }
        @tr-step{
          @${\delta(\vbinop, \valn_0, \valn_1) \nkrel \delta(\vbinop, \valk_0, \valk_1)}
          @|NK-delta|
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \ctxn[\delta(\vbinop, \valn_0, \valn_1)]}
        }
      }
      @tr-if[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{1'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

  @tr-case[@${\ctxk[\ebinop{\valk_0}{\valk_1}] \ccKS \ctxk[\tagerror]}]{
    @tr-step{
      @${\wellKE \ebinop{\valk_0}{\valk_1}}
      definition @${\ccKS}
    }
    @tr-step{
      @${\wellNE \exprn_0}
      @|NK-D-type| (1)
    }
    @tr-step{
      @${\exprn_0 = \ebinop{\exprn_{0'}}{\exprn_{1'}}}
      @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau_{0'}
         @tr-and[]
         \wellNE \exprn_{1'} : \tau_{1'}}
      @|N-D-inversion| (2, 3)
    }
    @tr-step{
      @${\exprn_{0'} \nkrel \valk_0
         @tr-and[]
         \exprn_{1'} \nkrel \valk_1}
      @${\nkrel}
    }
    @tr-step{
      @${\exprn_{0'} \rrNDstar \valn_{0} \mbox{ and } \valn_0 \nkrel \valk_0
         @tr-or[]
         \exprn_{0'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @tr-step{
      @${\exprn_{1'} \rrNDstar \valn_{1} \mbox{ and } \valn_1 \nkrel \valk_1
         @tr-or[]
         \exprn_{1'} \rrNDstar \boundaryerror}
      @|NK-D-stutter|
    }
    @list[
      @tr-if[@${\exprn_{0'} \rrNDstar \valn_{0}
                @tr-and[]
                \exprn_{1'} \rrNDstar \valn_1}]{
        @tr-step{
          @elem{@${\delta(\vbinop, \valk_0, \valk_1} is undefined}
          definition @${\rrND}
        }
        @tr-step{
          @${\valk_0 \not\in \integers
             @tr-and[]
             \valk_1 \not\in \integers}
          (a)
        }
        @tr-step{
          @${\valn_0 \not\in \integers}
          @${\valn_0 \nkrel \valk_0}
        }
        @tr-step{
          @${\valn_1 \not\in \integers}
          @${\valn_1 \nkrel \valk_1}
        }
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \tagerror}
        }
      }
      @tr-if[@${\exprn_{0'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
      @tr-else[@${\exprn_{1'} \rrNDstar \boundaryerror}]{
        @tr-qed{
          @${\ctxn[\exprn_0] \rrNSstar \boundaryerror}
        }
      }
    ]
  }

}

@tr-lemma[#:key "NK-S-app" @elem{@${\langN}--@${\langK} static application}]{
  If @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}
        @tr-and[]
        \wellNE \eapp{\valn_0}{\valn_1} : \tau
        @tr-and[]
        \wellKE \eapp{\valk_0}{\valk_1} : \kany
        @tr-and[]
        \eapp{\valk_0}{\valk_1} \ccKS \exprk_2}
  then @${\eapp{\valn_0}{\valn_1} \rrNSstar \exprn_2}
  and @${\exprn_2 \nkrel \exprk_2}
}@tr-proof{
  By induction on the number of monitors in @${\valn_0},
   proceeding by case analysis on @${\eapp{\valk_0}{\valk_1} \ccKS \exprk_2}.

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKS \boundaryerror
              @tr-and[4]
              \valn_0 = \vlam{\tann{x}{\tau_0}}{\exprn_0}}]{
    @tr-step{
      @${\efromany{\tagof{\tau_0}}{\valk_1} = \boundaryerror}
      definition @${\rrKS}
    }
    @tr-step{
      @${\wellNE \valn_1 : \tau_1
         @tr-and[]
         \tau_1 \subteq \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\wellKE \valk_1 : \tagof{\tau_1}}
      @|NK-value| (3)
    }
    @tr-step{
      @${\wellKE \valk_1 : \tagof{\tau_0}}
      @|K-subt-preservation| (2)
    }
    @tr-step{
      @${\efromany{\tagof{\tau_0}}{\valk_1} = \valk_1}
      (5)
    }
    @tr-contradiction{
      (1, 6)
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKS \boundaryerror
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel \valk_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrNS \edyn{\tau_c}{(\eapp{\valn_{0'}}{(\esta{\tau_d}{\valn_{1}})})}}
      definition @${\rrNS}
    }
    @tr-step{
      @${\wellNE \esta{\tau_d}{\valn_{1}}}
      @|N-S-preservation|
    }
    @tr-step{
      @${\esta{\tau_d}{\valn_1} \rrNDstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1}
      @|NK-check| (1, 3)
    }
    @tr-step{
      @${\valn_{0'} = \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\valn_{0''}} \mbox{ and } \valn_{0''} \nkrel \valk_0
         @tr-or[]
         \valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn} \mbox{ and } \exprn \nkrel \exprk_0}
      (1)
    }
    @tr-if[@${\valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn}}]{
      @tr-contradiction{
        @${\wellNE \eapp{\valn_0}{\valn_1} : \tau}
      }
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrND \esta{\tau_c'}{(\eapp{\valn_{0''}}{(\edyn{\tau_d'}{\valn_{1'}})})}}
    }
    @tr-step{
      @${\edyn{\tau_d'}{\valn_{1'}} \rrNSstar \valn_{1''} \mbox{ and } \valn_{1''} \nkrel \valk_1
         @tr-or[]
         \edyn{\tau_d'}{\valn_{1'}} \rrNSstar \boundaryerror}
      @|NK-check|
    }
    @tr-if[@${\edyn{\tau_d'}{\valn_{1'}} \rrNSstar \boundaryerror}]{
      @tr-qed{
        @${\eapp{\valn_0}{\valn_1} \rrNSstar \boundaryerror}
      }
    }
    @tr-step{
      @${\edyn{\tau_c}{(\esta{\tau_c'}{\ehole})} \nkrel \ehole}
      definition @${\nkrel}
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0''}}{\valn_{1''}} : \tau_c'}
      @|N-S-preservation|
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \rrNSstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \boundaryerror}
      @tr-IH
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNSstar \boundaryerror}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKS \vsubst{\exprk_0}{x}{\efromany{\tagof{\tau_0}}{\valk_1}}
              @tr-and[4]
              \valn_0 = \vlam{\tann{x}{\tau_0}}{\exprn_0}}]{
    @tr-step{
      @${\efromany{\tagof{\tau_0}}{\valk_1} = \valk_1}
      definition @${\rrKS}
    }
    @tr-step{
      @${\wellNE \valn_1 : \tau_1
         @tr-and[]
         \tau_1 \subteq \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\valn_1 \nkrel \valk_1
         @tr-and[]
         \exprn_0 \nkrel \exprk_0}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprn_0})}{\valn_1} \rrNS \vsubst{\exprn_0}{x}{\valn_1}}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn_1} \nkrel \vsubst{\exprk_0}{x}{\valk_1}}
      @|NK-subst|
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNSstar \vsubst{\exprn_0}{x}{\valn_1}}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKS \vsubst{\exprk_0}{x}{\efromany{\tagof{\tau_0}}{\valk_1}}
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel \valk_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrNS \edyn{\tau_c}{(\eapp{\valn_{0'}}{(\esta{\tau_d}{\valn_{1}})})}}
      definition @${\rrNS}
    }
    @tr-step{
      @${\wellNE \esta{\tau_d}{\valn_1}}
      @|N-S-preservation|
    }
    @tr-step{
      @${\esta{\tau_d}{\valn_1} \rrNDstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1}
      @|NK-check| (1, 3)
    }
    @tr-step{
      @${\valn_{0'} = \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\valn_{0''}} \mbox{ and } \valn_{0''} \nkrel \valk_0
         @tr-or[]
         \valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn} \mbox{ and } \exprn \nkrel \exprk_0}
      (1)
    }
    @tr-if[@${\valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn}}]{
      @tr-step{
        @${\wellNE \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}} : \tarr{\tau_d}{\tau_c}}
        @${\wellNE \eapp{\valn_0}{\valn_1} : \tau}
      }
      @tr-step{
        @${\wellNE \valn_{0'}}
        @|N-S-inversion| (a)
      }
      @tr-contradiction{
        @${\wellNE \vlam{\tann{x}{\tau_0}}{\exprn}}
      }
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrND \esta{\tau_c'}{(\eapp{\valn_{0''}}{(\edyn{\tau_d'}{\valn_{1'}})})}}
    }
    @tr-step{
      @${\wellNE \edyn{\tau_d'}{\valn_{1'}} : \tau_d'}
      @|N-D-preservation|
    }
    @tr-step{
      @${\edyn{\tau_d'}{\valn_{1'}} \rrNSstar \valn_{1''} \mbox{ and } \valn_{1''} \nkrel \valk_1
         @tr-or[]
         \edyn{\tau_d'}{\valn_{1'}} \rrNSstar \boundaryerror}
      @|NK-check|
    }
    @tr-if[@${\edyn{\tau_d'}{\valn_{1'}} \rrNSstar \boundaryerror}]{
      @tr-qed{
        @${\eapp{\valn_0}{\valn_1} \rrNSstar \boundaryerror}
      }
    }
    @tr-step{
      @${\edyn{\tau_c}{(\esta{\tau_c'}{\ehole})} \nkrel \ehole}
      definition @${\nkrel}
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0''}}{\valn_{1''}} : \tau_c'}
      @|N-S-preservation|
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \rrNSstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \exprk_2}
      @tr-IH
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNSstar \edyn{\tau_c}{(\esta{\tau_c'}{\exprn_2})}}
    }
  }

  @tr-case[@${\eapp{(\vlam{x}{\exprk_0})}{\valk_1}
                \ccKS \edynfake{\vsubst{\exprk_0}{x}{\valk_1}}
              @tr-and[4]
              \valn_0 = \vlam{x}{\exprn_0}}]{
    @tr-contradiction{
      @${\wellNE \eapp{\valn_0}{\valn_1} : \tau}
    }
  }

  @tr-case[@${\eapp{(\vlam{x}{\exprk_0})}{\valk_1}
                \ccKS \edynfake{\vsubst{\exprk_0}{x}{\valk_1}}
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel (\vlam{x}{\exprk_0})
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrNS \edyn{\tau_c}{(\eapp{\valn_{0'}}{(\esta{\tau_d}{\valn_1})})}}
      definition @${\rrNS}
    }
    @tr-step{
      @${\wellNE \esta{\tau_d}{\valn_1}}
      @|N-S-preservation|
    }
    @tr-step{
      @${\esta{\tau_d}{\valn_1} \rrNDstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1}
      @|NK-check|
    }
    @tr-step{
      @${\edyn{\tau_c}{\ehole} \nkrel \edynfake{\ehole}}
      definition @${\nkrel}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0'}}{\valn_{1'}}}
      @|N-S-preservation| (2, 3)
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrNDstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \exprk_2}
      @|NK-D-app| (6, 7)
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNSstar \edyn{\tau_c}{\exprn_2}
         @tr-and[]
         \edyn{\tau_c}{\exprn_2} \nkrel \edynfake{\exprk_2}}
    }
  }
}

@tr-lemma[#:key "NK-D-app" @elem{@${\langN}--@${\langK} dynamic application}]{
  If @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}
        @tr-and[]
        \wellNE \eapp{\valn_0}{\valn_1}
        @tr-and[]
        \wellKE \eapp{\valk_0}{\valk_1}
        @tr-and[]
        \eapp{\valk_0}{\valk_1} \ccKD \exprk_2}
  then @${\eapp{\valn_0}{\valn_1} \rrNDstar \exprn_2}
  and @${\exprn_2 \nkrel \exprk_2}
}@tr-proof{
  By induction on the number of monitors in @${\valn_0},
   proceeding by case analysis on @${\eapp{\valk_0}{\valk_1} \ccKD \exprk_2}.

  @tr-case[@${\eapp{\valk_0}{\valk_1} \rrKD \tagerror}]{
    @tr-step{
      @${\valk_0 \in \integers
         @tr-or[]
         \valk_0 \in \vpair{v}{v}}
      definition @${\rrKD}
    }
    @tr-step{
      @${\valn_0 \in \integers
         @tr-or[]
         \valn_0 \in \vpair{v}{v}}
      @${\valn_0 \nkrel \valk_0}
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrND \tagerror}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKD \boundaryerror
              @tr-and[4]
              \valn_0 = \vlam{\tann{x}{\tau_0}}{\exprn_0}}]{
    @tr-contradiction{
      @${\wellNE \eapp{\valn_0}{\valn_1}}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKD \boundaryerror
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel \valk_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrND \esta{\tau_c}{(\eapp{\valn_{0'}}{(\edyn{\tau_d}{\valn_{1}})})}}
      definition @${\rrND}
    }
    @tr-step{
      @${\wellNE \edyn{\tau_d}{\valn_1} : \tau_d}
      @|N-D-preservation|
    }
    @tr-step{
      @${\edyn{\tau_d}{\valn_1} \rrNSstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1
         @tr-or[]
         \edyn{\tau_d}{\valn_1} \rrNSstar \boundaryerror}
      @|NK-check| (1, 3)
    }
    @tr-if[@${\edyn{\tau_d}{\valn_1} \rrNSstar \boundaryerror}]{
      @tr-qed{
        @${\eapp{\valn_0}{\valn_1} \rrNDstar \boundaryerror}
      }
    }
    @tr-step{
      @${\valn_{0'} = \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\valn_{0''}} \mbox{ and } \valn_{0''} \nkrel \valk_0
         @tr-or[]
         \valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn} \mbox{ and } \exprn \nkrel \exprk_0}
      (1)
    }
    @tr-if[@${\valn_{0'} = \vlam{\tann{x}{\tau_0}}{\exprn}}]{
      @tr-step{
        @${\efromany{\tagof{\tau_0}}{\valk_1} = \boundaryerror}
        definition @${\rrKD}
      }
      @tr-step{
        @${\wellNE \valn_{1'} : \tau_1
           @tr-and[]
           \tau_1 \subteq \tau_0}
        @|N-S-inversion|
      }
      @tr-step{
        @${\wellKE \valk_1 : \tagof{\tau_1}}
        @|NK-value| (3)
      }
      @tr-step{
        @${\wellKE \valk_1 : \tagof{\tau_0}}
        @|K-subt-preservation| (c)
      }
      @tr-step{
        @${\efromany{\tagof{\tau_0}}{\valk_1} = \valk_1}
        (d)
      }
      @tr-contradiction{
        (a)
      }
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrNS \edyn{\tau_c'}{(\eapp{\valn_{0''}}{(\esta{\tau_d'}{\valn_{1'}})})}}
    }
    @tr-step{
      @${\wellNE \esta{\tau_d'}{\valn_{1'}}}
      @|N-S-preservation|
    }
    @tr-step{
      @${\esta{\tau_d'}{\valn_{1'}} \rrNDstar \valn_{1''} \mbox{ and } \valn_{1''} \nkrel \valk_1}
      @|NK-check|
    }
    @tr-step{
      @${\esta{\tau_c}{(\edyn{\tau_c'}{\ehole})} \nkrel \ehole}
      definition @${\nkrel}
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0''}}{\valn_{1''}}}
      @|N-D-preservation|
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \rrNDstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \boundaryerror}
      @tr-IH
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNDstar \boundaryerror}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKD \estafake{\vsubst{\exprk_0}{x}{\efromany{\tagof{\tau_0}}{\valk_1}}}
              @tr-and[4]
              \valn_0 = \vlam{\tann{x}{\tau_0}}{\exprn_0}}]{
    @tr-step{
      @${\wellNE \valn_0}
      @|N-D-inversion|
    }
    @tr-contradiction{
      @${\wellNE \vlam{\tann{x}{\tau_0}}{\exprn_0}}
    }
  }

  @tr-case[@${\eapp{(\vlam{\tann{x}{\tau_0}}{\exprk_0})}{\valk_1}
                \ccKD \estafake{\vsubst{\exprk_0}{x}{\efromany{\tagof{\tau_0}}{\valk_1}}}
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel \valk_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrND \esta{\tau_c}{(\eapp{\valn_{0'}}{(\edyn{\tau_d}{\valn_{1}})})}}
      definition @${\rrND}
    }
    @tr-step{
      @${\wellNE \edyn{\tau_d}{\valn_1} : \tau_d}
      @|N-D-preservation|
    }
    @tr-step{
      @${\edyn{\tau_d}{\valn_1} \rrNSstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1
         @tr-or[]
         \edyn{\tau_d}{\valn_1} \rrNSstar \boundaryerror}
      @|NK-check| (1, 3)
    }
    @tr-if[@${\edyn{\tau_d}{\valn_1} \rrNSstar \boundaryerror}]{
      @tr-qed{
        @${\eapp{\valn_0}{\valn_1} \rrNDstar \boundaryerror}
      }
    }
    @tr-step{
      @${\esta{\tau_c}{\ehole} \nkrel \estafake{\ehole}}
      definition of @${\nkrel}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0'}}{\valn_{1'}} : \tau_c}
      @|N-D-preservation|
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrNSstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \exprk_2}
      @|NK-S-app| (7, 8)
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNDstar \esta{\tau_c}{\exprn_2}
         @tr-and[]
         \esta{\tau_c}{\exprn_2} \nkrel \estafake{\exprk_2}}
    }
  }

  @tr-case[@${\eapp{(\vlam{x}{\exprk_0})}{\valk_1}
                \ccKS \vsubst{\exprk_0}{x}{\valk_1}
              @tr-and[4]
              \valn_0 = \vlam{x}{\exprn_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprn_0
         @tr-and[]
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrND \vsubst{\exprn_0}{x}{\valn_1}}
      definition @${\rrND}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn_1} \nkrel \vsubst{\exprk_0}{x}{\valk_1}}
      @|NK-subst|
    }
    @tr-qed{}
  }

  @tr-case[@${\eapp{(\vlam{x}{\exprk_0})}{\valk_1}
                \ccKD \vsubst{\exprk_0}{x}{\valk_1}
              @tr-and[4]
              \valn_0 = \vmonfun{(\tarr{\tau_d}{\tau_c})}{\valn_{0'}}}]{
    @tr-step{
      @${\valn_{0'} \nkrel (\vlam{x}{\exprk_0})
         \valn_1 \nkrel \valk_1}
      @${\eapp{\valn_0}{\valn_1} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\eapp{\valn_0}{\valn_1} \rrND \esta{\tau_c}{(\eapp{\valn_{0'}}{(\edyn{\tau_d}{\valn_1})})}}
      definition @${\rrND}
    }
    @tr-step{
      @${\wellNE \edyn{\tau_d}{\valn_1} : \tau_d}
      @|N-D-preservation|
    }
    @tr-step{
      @${\edyn{\tau_d}{\valn_1} \rrNDstar \valn_{1'} \mbox{ and } \valn_{1'} \nkrel \valk_1
         @tr-or[]
         \edyn{\tau_d}{\valn_1} \rrNDstar \boundaryerror}
      @|NK-check| (1, 3)
    }
    @tr-if[@${\edyn{\tau_d}{\valn_1} \rrNDstar \boundaryerror}]{
      @tr-qed{
        @${\eapp{\valn_0}{\valn_1} \rrNDstar \boundaryerror}
      }
    }
    @tr-step{
      @${\valn_{0'} = \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{\valn_{0''}} \mbox{ and } \valn_{0''} \nkrel \valk_0
         @tr-or[]
         \valn_{0'} = \vlam{x}{\exprn} \mbox{ and } \exprn \nkrel \exprk_0}
      (1)
    }
    @tr-if[@${\valn_{0'} = \vlam{x}{\exprn}}]{
      @tr-step{
        @${\wellNE \valn_{0'} : \tau_0
           @tr-and[]
           \tau_0 \subteq \tarr{\tau_d}{\tau_c}}
        @|N-D-inversion|
      }
      @tr-contradiction{
        @${\wellNE \vlam{x}{\exprn} : \tau_0}
      }
    }
    @tr-step{
      @${\eapp{\valn_{0'}}{\valn_{1'}} \rrNS \edyn{\tau_c'}{(\esta{\tau_d'}{\valn_{1'}})}}
      definition @${\rrNS}
    }
    @tr-step{
      @${\wellNE \esta{\tau_d'}{\valn_{1'}} : \tau_d'}
      @|N-S-preservation|
    }
    @tr-step{
      @${\esta{\tau_d'}{\valn_{1'}} \rrNSstar \valn_{1''} \mbox{ and } \valn_{1''} \nkrel \valk_1}
      @|NK-check|
    }
    @tr-step{
      @${\esta{\tau_c}{(\edyn{\tau_c'}{\ehole})} \nkrel \ehole}
      definition @${\nkrel}
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \nkrel \eapp{\valk_0}{\valk_1}}
    }
    @tr-step{
      @${\wellNE \eapp{\valn_{0''}}{\valn_{1''}}}
      @|N-D-preservation|
    }
    @tr-step{
      @${\eapp{\valn_{0''}}{\valn_{1''}} \rrNDstar \exprn_2
         @tr-and[]
         \exprn_2 \nkrel \exprk_2}
      @tr-IH
    }
    @tr-qed{
      @${\eapp{\valn_0}{\valn_1} \rrNSstar \esta{\tau_c}{(\edyn{\tau_c'}{\exprn_2})}}
    }
  }
}

@tr-lemma[#:key "NK-fail" @elem{@${\vfromany} inversion}]{
  If @${\efromany{\tagof{\tau}}{\valk} = \boundaryerror} and @${\valn \nkrel \valk}
  then @${\efromdynN{\tau}{\valn} = \boundaryerror}
}@tr-proof{
  By case analysis on @${\tau}.

  @tr-case[@${\tau = \tnat}]{
    @tr-step{
      @${\valk \not\in \naturals}
      @${\efromany{\tagof{\tau}}{\valk} = \boundaryerror}
    }
    @tr-step{
      @${\valn \not\in \naturals}
      (1)
    }
    @tr-step{
      @${\efromdynN{\tau}{\valn} = \boundaryerror}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tint}]{
    @tr-step{
      @${\valk \not\in \integers}
      @${\efromany{\tagof{\tau}}{\valk} = \boundaryerror}
    }
    @tr-step{
      @${\valn \not\in \integers}
      (1)
    }
    @tr-step{
      @${\efromdynN{\tau}{\valn} = \boundaryerror}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tpair{\tau_0}{\tau_1}}]{
    @tr-step{
      @${\valk \not\in \vpair{v}{v}}
      @${\efromany{\tagof{\tau}}{\valk} = \boundaryerror}
    }
    @tr-step{
      @${\valn \not\in \vpair{v}{v}}
      (1)
    }
    @tr-step{
      @${\efromdynN{\tau}{\valn} = \boundaryerror}
      (2)
    }
    @tr-qed{}
  }

  @tr-case[@${\tau = \tarr{\tau_d}{\tau_c}}]{
    @tr-step{
      @${\valk \in \integers
         @tr-or[]
         \valk \in \vpair{v}{v}}
      @${\efromany{\tagof{\tau}}{\valk} = \boundaryerror}
    }
    @tr-step{
      @${\valn \in \integers
         @tr-or[]
         \valn \in \vpair{v}{v}}
      (1)
    }
    @tr-step{
      @${\efromdynN{\tau}{\valn} = \boundaryerror}
      (2)
    }
    @tr-qed{}
  }
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
      @${\nkrel}
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
      @${\nkrel}
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
        \wellKE \ctxk[\exprk] : K
        @tr-and[]
        \ctxn[\exprn] \nkrel \ctxk[\exprk]}
  @linebreak[]
  then one of the following holds:
  @itemlist[
    @item{
      @${\wellNE \exprn : \tau' @tr-and[] \wellKE \exprk : K'}

    }
    @item{
      @${\wellNE \exprn @tr-and[] \wellKE \exprk}
    }
  ]
}@tr-proof{
  By induction on the structure of @${\ctxn[\exprn] \nkrel \ctxk[\exprk]} judgment.

  @tr-case[@${\ehole \nkrel \ehole}]{
    @tr-step{
      @${\ctxn[\exprn] = \exprn}
    }
    @tr-step{
      @${\ctxk[\exprk] = \exprk}
    }
    @tr-qed{ }
  }

  @tr-case[@${\ctxn \nkrel \echk{K}{\ctxk_0}}]{
    @tr-step{
      @${\ctxk[\exprk] = \echk{K}{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk] : \kany}
      @|K-S-inversion|
    }
    @tr-step{
      @${\ctxn[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eapp{\ctxn_0}{\exprn_1} \nkrel \eapp{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eapp{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \eapp{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tarr{\tau_d}{\tau_c}}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk] : \kfun}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eapp{\valn_0}{\ctxn_1} \nkrel \eapp{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eapp{\valn_0}{\ctxn_1[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \eapp{\valk_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn] : \tau_d}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_1[\exprk] : \kany}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\ctxn_0}{\exprn_1} \nkrel \vpair{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \vpair{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \vpair{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk] : \kany}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\valn_0}{\ctxn_1} \nkrel \vpair{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \vpair{\valn_0}{\ctxn_1[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \vpair{\valk_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn] : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_1[\exprk] : \kany}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eunop{\ctxn_0} \nkrel \eunop{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eunop{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \eunop{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tpair{\tau_0}{\tau_1}}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk] : \kpair}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\ctxn_0}{\exprn_1} \nkrel \ebinop{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \ebinop{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \ebinop{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tau_0}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk] : K_0}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\valn_0}{\ctxn_1} \nkrel \ebinop{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxk[\exprk] = \ebinop{\valn_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn] : \tau_1}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_1[\exprk] : K_1}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edyn{\tau_0}{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \edyn{\tau_0}{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \edyn{\tau_0}{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]
         @tr-and[]
         \wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @|NK-D-type|
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edynfake{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \edyn{\tau_0}{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \edynfake{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]
         @tr-and[]
         \wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @|NK-D-type|
    }
  }

  @tr-case[@${\edyn{\tau_0}{(\esta{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-step{
      @${\ctxn[\exprn] = \edyn{\tau_0}{(\esta{\tau_1}{\ctxn_0[\exprn]})}}
    }
    @tr-step{
      @${\wellNE \esta{\tau_1}{\ctxn_0[\exprn]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tau_1}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \esta{\tau_0}{\ctxk_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn] : \tau_0}
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \estafake{\ctxk_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn] : \tau_0}
    }
  }

  @tr-case[@${\esta{\tau_0}{(\edyn{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn] : \tau}
    }
  }

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
  By induction on the structure of the @${\ctxn[\exprn] \nkrel \ctxk[\exprk]} judgment.

  @tr-case[@${\ehole \nkrel \ehole}]{
    @tr-step{
      @${\ctxn[\exprn] = \exprn}
    }
    @tr-step{
      @${\ctxk[\exprk] = \exprk}
    }
    @tr-qed{ }
  }

  @tr-case[@${\ctxn \nkrel \echk{K}{\ctxk_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxk[\exprk]}
    }
  }

  @tr-case[@${\eapp{\ctxn_0}{\exprn_1} \nkrel \eapp{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eapp{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \eapp{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eapp{\valn_0}{\ctxn_1} \nkrel \eapp{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eapp{\valn_0}{\ctxn_1[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \eapp{\valk_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_1[\exprk]}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\ctxn_0}{\exprn_1} \nkrel \vpair{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \vpair{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \vpair{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\valn_0}{\ctxn_1} \nkrel \vpair{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \vpair{\valn_0}{\ctxn_1[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \vpair{\valk_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_1[\exprk]}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eunop{\ctxn_0} \nkrel \eunop{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \eunop{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \eunop{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\ctxn_0}{\exprn_1} \nkrel \ebinop{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \ebinop{\ctxn_0[\exprn]}{\exprn_1}
         @tr-and[]
         \ctxk[\exprk] = \ebinop{\ctxk_0[\exprk]}{\exprk_1}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\valn_0}{\ctxn_1} \nkrel \ebinop{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn[\exprn] = \ebinop{\exprn_0}{\ctxn_1[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \ebinop{\exprk_0}{\ctxk_1[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_1[\exprn]}
      @|N-S-inversion|
    }
    @tr-step{
      @${\wellKE \exprk_0
         @tr-and[]
         \wellKE \ctxk_1[\exprk]}
    }
    @tr-step{
      @${\ctxn_1[\exprn] \nkrel \ctxk_1[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edyn{\tau_0}{\ctxk_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn]}
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edynfake{\ctxk_0}}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn]}
    }
  }

  @tr-case[@${\edyn{\tau_0}{(\esta{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-contradiction{
      @${\wellNE \ctxn[\exprn]}
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \esta{\tau_0}{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \esta{\tau_0}{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \esta{\tau_0}{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tau_0
         @tr-and[]
         \wellKE \ctxk_0[\exprk] : \tagof{\tau_0}}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @|NK-S-type|
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \estafake{\ctxk_0}}]{
    @tr-step{
      @${\ctxn[\exprn] = \esta{\tau_0}{\ctxn_0[\exprn]}
         @tr-and[]
         \ctxk[\exprk] = \estafake{\ctxk_0[\exprk]}}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn] : \tau_0
         @tr-and[]
         \wellKE \ctxk_0[\exprk]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk_0[\exprk]}
    }
    @tr-qed{
      @|NK-S-type|
    }
  }

  @tr-case[@${\esta{\tau_0}{(\edyn{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-step{
      @${\ctxn[\exprn] = \esta{\tau_0}{(\edyn{\tau_1}{\ctxn_0[\exprn]})}}
    }
    @tr-step{
      @${\wellNE \edyn{\tau_1}{\ctxn_0[\exprn]} : \tau_1}
    }
    @tr-step{
      @${\wellNE \ctxn_0[\exprn]}
    }
    @tr-step{
      @${\ctxn_0[\exprn] \nkrel \ctxk[\exprk]}
    }
    @tr-qed{
      @tr-IH
    }
  }

}

@tr-lemma[#:key "NK-value" @elem{@${\langN}--@${\langK} value inversion}]{
  If @${\wellNE \valn : \tau
        @tr-and[]
        \valn \nkrel \valk}
  @linebreak[]
  then @${\wellKE \valk : \tagof{\tau}}
}@tr-proof{
  By induction on the structure of the @${\valn \nkrel \valk} judgment.

  @tr-case[@${\vpair{\valn_0}{\valn_1} \nkrel \vpair{\valk_0}{\valk_1}}]{
    @tr-step{
      @${\tau = \tpair{\tau_0}{\tau_1}}
      @|N-S-inversion|
    }
    @tr-step{
      @${\tagof{\tau} = \kpair}
    }
    @tr-qed{
      @${\wellKE \vpair{\valk_0}{\valk_1} : \kpair}
    }
  }

  @tr-step[@${i \nkrel i}]{
    @tr-if[@${\tau = \tnat}]{
      @tr-step{
        @${i \in \naturals}
        @|N-S-inversion|
      }
      @tr-qed{
        @${\wellKE i \knat}
      }
    }
    @tr-else[@${\tau = \tint}]{
      @tr-qed{
        @${\wellKE i : \kint}
      }
    }
  }

  @tr-step[@${\vlam{x}{\exprn} \nkrel \vlam{x}{\exprk}}]{
    @tr-contradiction{
      @${\wellNE \vlam{x}{\exprk} : \tau}
    }
  }

  @tr-step[@${\vlam{\tann{x}{\tau}}{\exprn} \nkrel \vlam{\tann{x}{\tau}}{\exprk}}]{
    @tr-step{
      @${\tau = \tarr{\tau_d}{\tau_c}}
      @|N-S-inversion|
    }
    @tr-step{
      @${\tagof{\tau} = \kfun}
    }
    @tr-qed{
      @${\wellKE \vlam{\tann{x}{\tau}}{\exprk} : \kfun}
    }
  }

  @tr-step[@${\vmonfun{\tau}{\valn} \nkrel \valk}]{
    @tr-step{
      @${\valn \nkrel \valk}
    }
    @tr-qed{
      @tr-IH
    }
  }
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
      @${\nkrel}
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
        @${\nkrel}
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
  By induction on the structure of the @${\ctxn \nkrel \ctxk} judgment.

  @tr-case[@${\ehole \nkrel \ehole}]{
    @tr-step{
      @${\ctxn[\exprn] = \exprn}
    }
    @tr-step{
      @${\ctxk[\exprk] = \exprk}
    }
    @tr-qed{}
  }

  @tr-case[@${\ctxn \nkrel \echk{K}{\ctxk_0}}]{
    @tr-step{
      @${\ctxn \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eapp{\ctxn_0}{\exprn_1} \nkrel \eapp{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eapp{\valn_0}{\ctxn_1} \nkrel \eapp{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn_1 \nkrel \ctxk_1}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\ctxn_0}{\exprn_1} \nkrel \vpair{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\vpair{\valn_0}{\ctxn_1} \nkrel \vpair{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn_1 \nkrel \ctxk_1}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\eunop{\ctxn_0} \nkrel \eunop{\ctxk_0}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\ctxn_0}{\exprn_1} \nkrel \ebinop{\ctxk_0}{\exprk_1}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\ebinop{\valn_0}{\ctxn_1} \nkrel \ebinop{\valk_0}{\ctxk_1}}]{
    @tr-step{
      @${\ctxn_1 \nkrel \ctxk_1}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edyn{\tau_0}{\ctxk_0}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\edyn{\tau_0}{\ctxn_0} \nkrel \edynfake{\ctxk_0}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\edyn{\tau_0}{(\esta{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \esta{\tau_0}{\ctxk_0}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\esta{\tau_0}{\ctxn_0} \nkrel \estafake{\ctxk_0}}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

  @tr-case[@${\esta{\tau_0}{(\edyn{\tau_1}{\ctxn_0})} \nkrel \ctxk_0}]{
    @tr-step{
      @${\ctxn_0 \nkrel \ctxk_0}
    }
    @tr-qed{
      @tr-IH
    }
  }

}

@tr-lemma[#:key "NK-subst" @elem{@${\langN}--@${\langK} substitution}]{
  If @${\exprn \nkrel \exprk} and @${\valn \kerel \valk}
  then @${\vsubst{\exprn}{x}{\valn} \nkrel \vsubst{\exprk}{x}{\valk}}
}@tr-proof{
  By induction on the structure of the @${\exprn \nkrel \exprk} judgment.

  @tr-case[@${\exprn \nkrel \echk{K_0}{\exprk_0}}]{
    @tr-step{
      @${\exprn \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\echk{K_0}{\exprk_0}}{x}{\valk} = \echk{K_0}{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\eerr \nkrel \exprk}]{
    @tr-step{
      @${\vsubst{\eerr}{x}{\valn} = \eerr}
    }
    @tr-qed{
      @${\eerr \nkrel \vsubst{\exprk}{x}{\valk}}
    }
  }

  @tr-case[@${\edyn{\tau_0}{\exprn_0} \nkrel \edyn{\tau_0}{\exprk_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\edyn{\tau_0}{\exprn_0}}{x}{\valn} = \edyn{\tau_0}{\vsubst{\exprn_0}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\edyn{\tau_0}{\exprk_0}}{x}{\valk} = \edyn{\tau_0}{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\edyn{\tau_0}{\exprn_0} \nkrel \edynfake{\exprk_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\edyn{\tau_0}{\exprn_0}}{x}{\valn} = \edyn{\tau_0}{\vsubst{\exprn_0}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\edynfake{\exprk_0}}{x}{\valk} = \edynfake{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\edyn{\tau_0}{(\esta{\tau_1}{\exprn_0})} \nkrel \exprk}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\edyn{\tau_0}{(\esta{\tau_1}{\exprn_0})}}{x}{\valn} = \edyn{\tau_0}{(\esta{\tau_1}{\vsubst{\exprn_0}{x}{\valn}})}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esta{\tau_0}{\exprn_0} \nkrel \esta{\tau_0}{\exprk_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\esta{\tau_0}{\exprn_0}}{x}{\valn} = \esta{\tau_0}{\vsubst{\exprn_0}{x}{\valn}}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esta{\tau_0}{\exprn_0} \nkrel \estafake{\exprk_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\esta{\tau_0}{\exprn_0}}{x}{\valn} = \esta{\tau_0}{\vsubst{\exprn_0}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\estafake{\exprk_0}}{x}{\valk} = \estafake{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esta{\tau_0}{(\edyn{\tau_1}{\exprn_0})} \nkrel \exprk}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\esta{\tau_0}{(\edyn{\tau_1}{\exprn_0})}}{x}{\valn} = \esta{\tau_0}{(\edyn{\tau_1}{\vsubst{\exprn_0}{x}{\valn}})}}
    }
    @tr-qed{
    }
  }
  }

  @tr-case[@${\eapp{\exprn_0}{\exprn_1} \nkrel \eapp{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0
         @tr-and[]
         \exprn_1 \nkrel \exprk_1}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}
         @tr-and[]
         \vsubst{\exprn_1}{x}{\valn} \nkrel \vsubst{\exprk_1}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\eapp{\exprn_0}{\exprn_1}}{x}{\valn} = \eapp{\vsubst{\exprn_0}{x}{\valn}}{\vsubst{\exprn_1}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\eapp{\exprk_0}{\exprk_1}}{x}{\valk} = \eapp{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}}
    }
    @tr-qed{}
  }

  @tr-case[@${\vpair{\exprn_0}{\exprn_1} \nkrel \vpair{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0
         @tr-and[]
         \exprn_1 \nkrel \exprk_1}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}
         @tr-and[]
         \vsubst{\exprn_1}{x}{\valn} \nkrel \vsubst{\exprk_1}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\vpair{\exprn_0}{\exprn_1}}{x}{\valn} = \vpair{\vsubst{\exprn_0}{x}{\valn}}{\vsubst{\exprn_1}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\vpair{\exprk_0}{\exprk_1}}{x}{\valk} = \vpair{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}}
    }
    @tr-qed{}
  }

  @tr-case[@${\eunop{\exprn_0} \nkrel \eunop{\exprk_0}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\eunop{\exprn_0}}{x}{\valn} = \eunop{\vsubst{\exprn_0}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\eunop{\exprk_0}}{x}{\valk} = \eunop{\vsubst{\exprk_0}{x}{\valk}}}
    }
    @tr-qed{}
  }

  @tr-case[@${\ebinop{\exprn_0}{\exprn_1} \nkrel \ebinop{\exprk_0}{\exprk_1}}]{
    @tr-step{
      @${\exprn_0 \nkrel \exprk_0
         @tr-and[]
         \exprn_1 \nkrel \exprk_1}
    }
    @tr-step{
      @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}
         @tr-and[]
         \vsubst{\exprn_1}{x}{\valn} \nkrel \vsubst{\exprk_1}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\ebinop{\exprn_0}{\exprn_1}}{x}{\valn} = \ebinop{\vsubst{\exprn_0}{x}{\valn}}{\vsubst{\exprn_1}{x}{\valn}}}
    }
    @tr-step{
      @${\vsubst{\ebinop{\exprk_0}{\exprk_1}}{x}{\valk} = \ebinop{\vsubst{\exprk_0}{x}{\valk}}{\vsubst{\exprk_1}{x}{\valk}}}
    }
    @tr-qed{}
  }

  @tr-case[@${x_0 \nkrel x_0} #:itemize? #false]{
    @tr-if[@${x_0 = x}]{
      @tr-qed{
        @${\vsubst{x_0}{x}{\valn} = \valn
           @tr-and[]
           \vsubst{x_0}{x}{\valk} = \valk}
      }
    }
    @tr-else[@${x_0 \neq x}]{
      @tr-qed{
        @${\vsubst{x_0}{x}{\valn} = x_0
          @tr-and[]
          \vsubst{x_0}{x}{\valk} = x_0}
      }
    }
  }

  @tr-case[@${i \nkrel i}]{
    @tr-qed{
      @${\vsubst{i}{x}{\valn} = i
        @tr-and[]
        \vsubst{i}{x}{\valk} = i}
    }
  }

  @tr-case[@${\vlam{x_0}{\exprn_0} \nkrel \vlam{x_0}{\exprk_0}}]{
    @tr-if[@${x_0 = x}]{
      @tr-qed{
        @${\vsubst{\vlam{x_0}{\exprn_0}}{x}{\valn} = \vlam{x_0}{\exprn_0}
          @tr-and[]
          \vsubst{\vlam{x_0}{\exprk_0}}{x}{\valk} = \vlam{x_0}{\exprk_0}}
      }
    }
    @tr-else[@${x_0 \neq x}]{
      @tr-step{
        @${\exprn_0 \nkrel \exprk_0}
      }
      @tr-step{
        @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
        @tr-IH
      }
      @tr-step{
        @${\vsubst{\vlam{x_0}{\exprn_0}}{x}{\valn} = \vlam{x_0}{\vsubst{\exprn_0}{x}{\valn}}
           @tr-and[]
           \vsubst{\vlam{x_0}{\exprk_0}}{x}{\valk} = \vlam{x_0}{\vsubst{\exprk_0}{x}{\valk}}}
      }
      @tr-qed{
      }
    }
  }

  @tr-case[@${\vlam{\tann{x_0}{\tau_0}}{\exprn_0} \nkrel \vlam{\tann{x_0}{\tau_0}}{\exprk_0}}]{
    @tr-if[@${x_0 = x}]{
      @tr-qed{
        @${\vsubst{\vlam{\tann{x_0}{\tau_0}}{\exprn_0}}{x}{\valn} = \vlam{\tann{x_0}{\tau_0}}{\exprn_0}
          @tr-and[]
          \vsubst{\vlam{\tann{x_0}{\tau_0}}{\exprk_0}}{x}{\valk} = \vlam{\tann{x_0}{\tau_0}}{\exprk_0}}
      }
    }
    @tr-else[@${x_0 \neq x}]{
      @tr-step{
        @${\exprn_0 \nkrel \exprk_0}
      }
      @tr-step{
        @${\vsubst{\exprn_0}{x}{\valn} \nkrel \vsubst{\exprk_0}{x}{\valk}}
        @tr-IH
      }
      @tr-step{
        @${\vsubst{\vlam{\tann{x_0}{\tau_0}}{\exprn_0}}{x}{\valn} = \vlam{\tann{x_0}{\tau_0}}{\vsubst{\exprn_0}{x}{\valn}}
           @tr-and[]
           \vsubst{\vlam{\tann{x_0}{\tau_0}}{\exprk_0}}{x}{\valk} = \vlam{\tann{x_0}{\tau_0}}{\vsubst{\exprk_0}{x}{\valk}}}
      }
      @tr-qed{ }
    }
  }

  @tr-case[@${\vmonfun{\tau_0}{\valn_0} \nkrel \valk_0}]{
    @tr-step{
      @${\valn_0 \nkrel \valk_0}
    }
    @tr-step{
      @${\vsubst{\valn_0}{x}{\valn} \nkrel \vsubst{\valk_0}{x}{\valk}}
      @tr-IH
    }
    @tr-step{
      @${\vsubst{\vmonfun{\tau_0}{\valn_0}}{x}{\valn} = \vmonfun{\tau_0}{\vsubst{\valn_0}{x}{\valn}}}
    }
    @tr-qed{}
  }

  @tr-case[@${\eerr \nkrel \eerr}]{
    @tr-qed{
      @${\vsubst{\eerr}{x}{\valn} = \eerr}
    }
  }
}

@tr-lemma[#:key "NK-delta" @elem{@${\langN}--@${\langK} @${\delta}-preservation}]{
  @itemlist[
    @item{
      If @${\valn \nkrel \valk}
      and @${\delta(\vunop, \valn)} is defined
      then @${\delta(\vunop, \valn) \nkrel \delta(\vunop, \valk)}
    }
    @item{
      If @${\valn_0 \nkrel \valk_0}
      and @${\valn_1 \nkrel \valk_1}
      and @${\delta(\vbinop, \valn_0, \valn_1)} is defined
      then @${\delta(\vbinop, \valn_0, \valn_1) \nkrel \delta(\vbinop, \valk_0, \valk_1)}
    }
  ]
}@tr-proof{
  @tr-case[@${\vunop = \vfst}]{
    @tr-step{
      @${\valn = \vpair{\valn_0}{\valn_1}}
      @${\delta(\vfst, \valn)} is defined
    }
    @tr-step{
      @${\valk = \vpair{\valk_0}{\valk_1}
         @tr-and[]
         \valn_0 \nkrel \valk_0 \mbox{ and } \valn_1 \nkrel \valk_1}
      @${\nkrel}
    }
    @tr-step{
      @${\delta(\vfst, \valn) = \valn_0
         @tr-and[]
         \delta(\vfst, \valk) = \valk_0}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\vunop = \vsnd}]{
    @tr-step{
      @${\valn = \vpair{\valn_0}{\valn_1}}
      @${\delta(\vsnd, \valn)} is defined
    }
    @tr-step{
      @${\valk = \vpair{\valk_0}{\valk_1}
         @tr-and[]
         \valn_0 \nkrel \valk_0 \mbox{ and } \valn_1 \nkrel \valk_1}
      @${\nkrel}
    }
    @tr-step{
      @${\delta(\vsnd, \valn) = \valn_1
         @tr-and[]
         \delta(\vsnd, \valk) = \valk_1}
    }
    @tr-qed{
      (2)
    }
  }

  @tr-case[@${\vbinop = \vsum}]{
    @tr-step{
      @${\valn_0 \in \integers
         @tr-and[]
         \valn_1 \in \integers}
      @${\delta(\vbinop, \valn_0, \valn_1)} is defined
    }
    @tr-step{
      @${\valn_0 = \valk_0
          @tr-and[]
          \valn_1 = \valk_1}
      @${\nkrel}
    }
    @tr-qed[]
  }

  @tr-case[@${\vbinop = \vquotient}]{
    @tr-step{
      @${\valn_0 \in \integers
         @tr-and[]
         \valn_1 \in \integers}
      @${\delta(\vbinop, \valn_0, \valn_1)} is defined
    }
    @tr-step{
      @${\valn_0 = \valk_0
          @tr-and[]
          \valn_1 = \valk_1}
      @${\nkrel}
    }
    @tr-qed[]
  }
}

