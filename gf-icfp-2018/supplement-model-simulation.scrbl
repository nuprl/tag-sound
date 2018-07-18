#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Simulation Lemmas}


@section{Definitions}

@(begin
   (define K-S-factor @tr-ref[#:key "K-S-factor"]{boundary factoring})
   (define K-S-hole-typing @tr-ref[#:key "K-S-hole-typing"]{static hole typing})

   (define KE-approximation @tr-ref[#:key "KE-approximation"]{@${\langK}--@${\langE} approximation})
   (define KE-simulation @tr-ref[#:key "KE-simulation"]{@${\langK}--@${\langE} simulation})
   (define KE-refl @tr-ref[#:key "KE-refl"]{@${\langK}--@${\langE} reflexivity})
   (define KE-ctx @tr-ref[#:key "KE-ctx"]{@${\langK}--@${\langE} context factoring})
   (define KE-stutter @tr-ref[#:key "KE-stutter"]{@${\langK}--@${\langE} stutter})
   (define KE-step @tr-ref[#:key "KE-step"]{@${\langK}--@${\langE} step})
   (define KE-hole-subst @tr-ref[#:key "KE-hole-subst"]{@${\langK}--@${\langE} context congruence})
   (define KE-inversion @tr-ref[#:key "KE-inversion"]{@${\langK}--@${\langE} inversion})
   (define KE-subst @tr-ref[#:key "KE-subst"]{@${\langK}--@${\langE} substitution})

   (define NK-approximation @tr-ref[#:key "NK-approximation"]{@${\langN}--@${\langK} approximation})
   (define NK-simulation @tr-ref[#:key "NK-simulation"]{@${\langN}--@${\langK} simulation})
   (define NK-refl @tr-ref[#:key "NK-refl"]{@${\langN}--@${\langK} reflexivity})
   (define NK-stutter @tr-ref[#:key "NK-stutter"]{@${\langN}--@${\langK} stutter})
   (define NK-step @tr-ref[#:key "NK-step"]{@${\langN}--@${\langK} step})
   (define NK-hole-subst @tr-ref[#:key "NK-hole-subst"]{@${\langN}--@${\langK} context congruence})
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
      @|KE-refl|
    }}
    @item{@tr-qed{
      by @|KE-simulation|
    }}
  ]
}


@tr-lemma[#:key "KE-refl" @elem{@${\langK}--@${\langE} reflexivity}]{
  If @${\Gamma \wellM e : \tau} and @${\Gamma \wellKE e : \tagof{\tau} \carrow e''} then
  @${e'' \kerel e}.
}@tr-proof{
  By structural induction on the @${\Gamma \wellKE e : \tagof{\tau} \carrow e''}
   and @${\Gamma \wellKE e \carrow e''} judgments.

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
      (1)
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
      (1)
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
      (1)
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
      (1)
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
      (1)
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
      @${e' \kerel e}
    }
    @tr-qed{
      (1)
    }
  }

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
      (1)
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
      (1)
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
      (1)
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
      (1)
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
      (1)
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
      (1)
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
      @tr-IH
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
      (1)
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
        @elem{repeat from step (2)}
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
        @elem{repeat from step (2)}
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
        @elem{repeat from step (2)}
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

@tr-lemma[#:key "KE-hole-subst" @elem{@${\langK}--@${\langE} context congruence}]{
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
  If @${\exprk \kerel \expre} and @${\valk \kerel \vale} and @${\exprk} does not
  contain a subterm of the form @${\eerr}
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
    @tr-contradiction{}
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
      @|NK-refl|
    }}
    @item{@tr-qed{
      by @|NK-simulation|
    }}
  ]
}


@tr-lemma[#:key "NK-refl" @elem{@${\langN}--@${\langK} reflexivity}]{
  If @${\wellM e : \tau} and @${\wellKE e : \tagof{\tau} \carrow e''} then @${e \nkrel e''}.
}@tr-proof{
  @itemlist[
    @item{@tr-step{
      @elem{@${e} and @${e''} are identical up to @${\vchk} expressions}
      definition of @${\carrow}
    }}
    @item{@tr-qed{
      by definition of @${\nkrel}
    }}
  ]
}

@tr-lemma[#:key "NK-simulation" @elem{@${\langK}--@${\langN} simulation}]{
  If @${\exprn_0 \nkrel \exprk_0} and @${\exprk_0 \ccKS \exprk_1}
  and @${\exprn_0} does not contain a subterm of the form @${\eerr}
  then either:
  @itemlist[
    @item{
      @${\exprk_0 = \ctxe_0[\echk{K}{v}]
         @tr-and[]
         \exprk_1 = \ctxe_0[v]
         @tr-and[]
         \exprn_0 \nkrel \exprk_1}
    }
    @item{
      @${\exprn_0 \ccNS \ldots \ccNS \exprn_{n}
         @tr-and[]
         \forall i \in \{1 .. {n \mhyphen 1}\}.\, \exprn_i \kerel \exprk_0
         @tr-and[]
         \exprn_n \nkrel \exprk_1}
    }
  ]
}@tr-proof{
  @tr-case[@${\exprk_0 = \ctxk_0[\exprk_{0'}
              @tr-and[]
              \wellKE \exprk_{0'}}]{
    @tr-step{
      @${\exprn_0 = \ctxn_0[\exprn_{0'}]
         @tr-and[]
         \ctxn_0 \nkrel \ctxk_0
         @tr-and[]
         \exprn_{0'} \nkrel \exprk_{0'}}
      by definition @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'}}
      by definition @${\nkrel}
    }
    @tr-step{
      @${\ctxn_0[\exprn_{0'}] \ccNS \ldots \ccNS \ctxn_0[\exprn_{{n-1}'}]
         @tr-and[] \forall i \in \{1 .. {n \mhyphen 1}\}\,.\, \ctxn_0[\exprn_{i'}] \nkrel \ctxk_0[\exprk_{0'}]}
      repeated uses of @|NK-stutter|
    }
    @tr-step{
      @${\ctxn_0[\exprn_{{n-1}'}] \ccNS \ctxn_0[\exprn_{{n}'}]
         @tr-and[]
         \ctxn_0[\exprn_{{n}'}] \nkrel \exprk_1}
      case analysis on @${\rrKD}
    }
    @tr-qed{
    }
  }
  @tr-case[@${\exprk_0 = \ctxk_0[\exprk_{0'}
              @tr-and[]
              \wellKE \exprk_{0'} : K}]{
    @tr-step{
      @${\exprn_0 = \ctxn_0[\exprn_{0'}]
         @tr-and[]
         \ctxn_0 \nkrel \ctxk_0
         @tr-and[]
         \exprn_{0'} \nkrel \exprk_{0'}}
      by definition @${\nkrel}
    }
    @tr-step{
      @${\wellNE \exprn_{0'} : \tau
         @tr-and[]
         K = \tagof{\tau}}
      by definition @${\nkrel}
    }
    @tr-if[@${\exprk_{0'} = \echk{K}{v}}]{
      @tr-step{
        @${\exprn_{0'} \nkrel v}
        definition @${\nkrel}
      }
      @tr-step{
        @${\echk{K}{v} \rrKS v}
        (2)
      }
      @tr-qed{}
    }
    @tr-else[@${\exprk_{0'} \neq \echk{K}{v}}]{
      @tr-qed{
        by @|NK-stutter| and case analysis on @${\rrKS}
      }
    }
  }
}

@tr-lemma[#:key "NK-stutter" @elem{@${\langN}--@${\langK} stutter}]{
  If @${\ctxn[\exprn] \nkrel \ctxk[\exprk]}
  and @${\exprn = \ctxn_0[\eerr]
         @tr-or[4]
         \exprn = \ctxn_0[\edyn{\tau}{v_0}]
          \wedge
          \ctxn_0 \neq \ehole
         @tr-or[4]
         \exprn = \ctxn_0[\esta{\tau}{v_0}]
          \wedge
          \ctxn_0 \neq \ehole}
  @linebreak[]
  then @${\ctxn[\exprn] \ccNS \ctxn[\exprn_1]}
  and @${\ctxn[\exprn_1] \nkrel \ctxk[\exprk]}.
}@tr-proof[#:sketch? #true]{
  by definition of @${\nkrel}
}

