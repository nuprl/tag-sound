#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Simulation Lemmas}

@; @tr-theorem[#:key "error-simulation" @elem{@${\eerr} approximation}]{
@;   If @${e \in \exprsta} and @${\wellM e : \tau} then the following statements hold:
@;   @itemlist[
@;   @item{
@;     if @${e \rrESstar \eerr} then @${e \rrKSstar \eerr}
@;   }
@;   @item{
@;     if @${e \rrKSstar \eerr} then @${e \rrNSstar \eerr}
@;   }
@;   ]
@; }@tr-proof[#:sketch? #true]{
@;  The relation @${\rrESstar} may step to an error in two ways:
@;   either by @${\rrES} or by @${\rrED}.
@;  For @${\rrED}, @${\rrKD} has the same error transitions. @; So, done if proceed in lock-step
@;  For @${\rrES}, @${\rrKS} has no matching tag error transitions because
@;   they are ruled out by soundness; thus if @${\rrES} steps to an error
@;   then @${\rrKSstar} must step to an error earlier due to a boundary check.
@;
@;  The @${\rrKSstar} relation may step to an error via @${\rrKS} or @${\rrKD}.
@;  For @${\rrKD}, the error may be a tag error or a boundary error due to applying
@;   a typed function to an ill-tagged argument; the @${\rrND} notion of reduction
@;   has the same tag error transitions and protects typed functions with monitors.
@;  For @${\rrKS}, the error may be a check error; @$[\rrNS} detects
@;   the same errors either at the boundary or through monitors.
@; }


@; explain the main result in simple terms, motivate the definitions
@;  coming next because if no motivation its going to be disorienting I think


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
  and @${e \rrESstar \eerr} then @${\wellKE e \carrow e'' : \tagof{\tau}}
  and @${e'' \rrKSstar \eerr}
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


@tr-lemma[#:key "KE-refl" @elem{reflexivity}]{
  If @${\wellM e : \tau} and @${\wellKE e \carrow e'' : \tagof{\tau}} then @${e'' \kerel e}.
}@tr-proof{
  @itemlist[
    @item{@tr-step{
      @elem{@${e} and @${e''} are identical up to @${\vchk} expressions}
      definition of @${\carrow}
    }}
    @item{@tr-qed{
      by definition of @${\kerel}
    }}
  ]
}

@tr-lemma[#:key "KE-simulation" @elem{@${\langK}--@${\langE} simulation}]{
  If @${\exprk_0 \kerel \expre_0} and @${\expre_0 \ccES \expre_1}
  and @${\exprk_0 \not\in \eerr} then:
  @itemlist[
    @item{
      @${\exprk_0 \ccKS \ldots \ccKS \exprk_n}
    }
    @item{
      @${\forall i \in \{1 .. {n-1}\}.\, \exprk_i \kerel \expre_0}
    }
    @item{
      @${\exprk_n \kerel \expre_1}
    }
  ]
}@tr-proof{
  @tr-case[@${\expre_0 = \ctxe[\expre_{0'}]
              @tr-and[4]
              \expre_{0'} \rrES \expre_{1'}
              @tr-and[4]
              \expre_1 = \ctxe[\expre_{1'}]}]{
    @tr-step{
      @${\exprk_0 = \ctxk[\exprk_{0'}]
         @tr-and[]
         \ctxk \kerel \ctxe
         @tr-and[]
         \exprk_{0'} \kerel \expre_{0'}}
      @|KE-ctx|
    }
    @tr-step{
      @${\ctxk[\exprk_{0'}] \ccKS \ldots \ccKS \ctxk[\exprk_{{n-1}'}]
         @tr-and[] \forall i \in \{1 .. {n-1}\}\,.\, \ctxk[\exprk_{i'}] \kerel \ctxe[\expre_{0'}]
         @tr-and[] \exprk_{n-1} \neq \echk{\tau}{e}
         @tr-and[] \exprk_{n-1} \neq \edynfake{e}
         @tr-and[] \exprk_{n-1} \neq \estafake{e} }
      repeated uses of @|KE-stutter| (1)
    }
    @list[
      @tr-if[@${\exprk_{n-1} \in \eerr}]{
        @tr-qed{
          @${\exprk_0 \rrKSstar \eerr}
        }
      }
      @tr-else[@${\exprk_{n-1} \not\in \eerr}]{
        @tr-step{
          @${\ctxk[\exprk_{n-1}] \ccKS \ctxk[\exprk_n]
             @tr-and[]
             \exprk_n \kerel \expre_{1'}}
          @|KE-step| (1, 2)
        }
        @tr-qed{
          @|KE-hole-subst|
        }
      }
    ]
  }
}

@tr-lemma[#:key "KE-ctx" @elem{@${\langK}--@${\langE} context factoring}]{
  If @${\exprk_0 \kerel \expre_0} and @${\expre_0 = \ctxe_0[\expre_{1'}]}
  then @${\exprk_0 = \ctxk_0[\exprk_{0'}]}
  and @${\ctxk_0 \kerel \ctxe_0}
  and @${\exprk_{0'} \kerel \expre_{0'}}
}@tr-proof{
  @tr-qed{
    by structural induction on the derivation of @${\exprk_0 \kerel \expre_0}
  }
}

@tr-lemma[#:key "KE-stutter" @elem{@${\langK}--@${\langE} stutter}]{
  If @${\ctxk[\exprk] \kerel \ctxe[\expre]}
  and @${\exprk = \ctxk_0[\eerr]
         @tr-or[4]
         \exprk = \ctxk_0[\echk{K}{v_0}]
         @tr-or[4]
         \exprk = \ctxk_0[\edynfake{v_0}]
         @tr-or[4]
         \exprk = \ctxk_0[\estafake{v_0}]}
  @linebreak[]
  then @${\ctxk[\exprk] \ccKS \ctxk[\exprk_1]}
  and @${\ctxk[\exprk_1] \kerel \ctxe[\expre]}.
}@tr-proof{
  @tr-case[@${\exprk = \ctxk_0[\eerr]}]{
    @tr-qed{
      @${\ctxk[\exprk] \ccKS \eerr}
    }
  }
  @tr-case[@${\exprk = \ctxk_0[\echk{K}{v_0}]} #:itemize? #false]{
    @tr-if[@${\efromany{K}{v_0} = \boundaryerror}]{
      @tr-qed{
        @${\ctxk[\ctxk_0[\echk{K}{v_0}]] \ccKS \boundaryerror}
      }
    }
    @tr-else[@${\efromany{K}{v_0} = v_0}]{
      @tr-step{
        @${\ctxk[\ctxk_0[\echk{K}{v_0}]] \ccKS \ctxk[\ctxk_0[v_0]]}
      }
      @tr-step{
        @${\ctxk[\ctxk_0[v_0]] \kerel \ctxe[\expre]}
        @${\ctxk[\ctxk_0[\echk{K}{v_0}]] \kerel \ctxe[\expre]}
      }
      @tr-qed[]
    }
  }
  @tr-case[@${\exprk = \ctxk_0[\edynfake{v_0}]}]{
    @tr-step{
      @${\ctxk[\ctxk_0[\edynfake{v_0}]] \ccKS \ctxk[\ctxk_0[v_0]]}
    }
    @tr-step{
      @${\ctxk[\ctxk_0[v_0]] \kerel \ctxe[\expre]}
      @${\ctxk[\ctxk_0[\edynfake{v_0}]] \kerel \ctxe[\expre]}
    }
    @tr-qed[]
  }
  @tr-case[@${\exprk = \ctxk_0[\estafake{v_0}]}]{
    @tr-step{
      @${\ctxk[\ctxk_0[\estafake{v_0}]] \ccKS \ctxk[\ctxk_0[v_0]]}
    }
    @tr-step{
      @${\ctxk[\ctxk_0[v_0]] \kerel \ctxe[\expre]}
      @${\ctxk[\ctxk_0[\estafake{v_0}]] \kerel \ctxe[\expre]}
    }
    @tr-qed[]
  }
}

@tr-lemma[#:key "KE-step" @elem{@${\langK}--@${\langE} step}]{
  If @${\ctxk[\exprk] \kerel \ctxe[\expre]}
  and @${\exprk \not\in \{\echk{\tau}{e}, \edynfake{e}, \estafake{e}\}}
  and @${\expre \rrES \expre_1}
  then @${\ctxk[\exprk] \ccKS \ctxk[\exprk_1]} and @${\exprk_1 \kerel \expre_1}
}@tr-proof{
  By @|K-S-factor| and @|K-S-hole-typing|, the inner expression @${\exprk}
   is either typed or untyped.

  @tr-case[@${\wellKE \exprk} #:itemize? #false]{
    @tr-qed{
      by case analysis on @${\expre \rrES \expre_1}; either @${\exprk} steps
       in the same manner, or @${\exprk} steps to a boundary error due to
       the application of a typed function to an invalid argument
    }
  }

  @tr-case[@${\wellKE \exprk : K} #:itemize? #false]{
    @tr-qed{
      by case analysis on @${\expre \rrES \expre_1};
       note that @${\expre_1 \not\in \tagerror} since @${\exprk} is well-typed.
    }
  }
}

@tr-lemma[#:key "KE-hole-subst" @elem{@${\langK}--@${\langE} context congruence}]{
  If @${\exprk \kerel \expre} and @${\ctxk \kerel \ctxe} then @${\ctxk[\exprk] \kerel \ctxe[\expre]}
}@tr-proof{
  @tr-qed{
    by definition of @${\kerel}
  }
}


@; -----------------------------------------------------------------------------

@tr-lemma[#:key "NK-approximation" @elem{@${\langN}--@${\langK} approximation}]{
  If @${e \in \exprsta} and @${\wellM e : \tau}
  and @${\wellKE e \carrow e'' : \tagof{\tau}}
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
  If @${\wellM e : \tau} and @${\wellKE e \carrow e'' : \tagof{\tau}} then @${e'' \nkrel e}.
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
  and @${\exprn_0 \not\in \eerr} then either:
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
         \forall i \in \{1 .. {n-1}\}.\, \exprn_i \kerel \exprk_0
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
         @tr-and[] \forall i \in \{1 .. {n-1}\}\,.\, \ctxn_0[\exprn_{i'}] \nkrel \ctxk_0[\exprk_{0'}]}
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

