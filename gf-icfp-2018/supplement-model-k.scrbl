#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{(@${\langK}) @|FOlong| Embedding}

@; -----------------------------------------------------------------------------
@section{@|FOlong| Definitions}
@exact{\input{fig:locally-defensive-embedding.tex}}

@exact{\newpage}
@tr-definition[#:key "K-boundary-free" @elem{@${\langK} boundary-free}]{
  An expression @${e} is @emph{boundary free} if @${e} does not contain
  a subterm of the form:
  @itemlist[
  @item{ @${(\edyn{\tau'}{e'})}, }
  @item{ @${(\esta{\tau'}{e'})}, }
  @item{ @${(\edynfake{e'})}, or }
  @item{ @${(\estafake{e'})}. }
  ]
}

@; -----------------------------------------------------------------------------
@|clearpage|
@section{@|FOlong| Theorems}

@(begin
   (define K-S-soundness @tr-ref[#:key "K-S-soundness"]{static @${\langK}-soundness})
   (define K-D-soundness @tr-ref[#:key "K-S-soundness"]{static @${\langK}-soundness})
   (define K-bf-soundness @tr-ref[#:key "K-bf-soundness"]{@${\langK} boundary-free soundness})
   (define K-compilation @tr-ref[#:key "K-compilation"]{@${\langK}-compilation})
   (define NK-base-type @tr-ref[#:key "NK-base-type"]{base type equivalence})

   (define K-S-progress @tr-ref[#:key "K-S-progress"]{static progress})
   (define K-D-progress @tr-ref[#:key "K-D-progress"]{dynamic progress})
   (define K-S-preservation @tr-ref[#:key "K-S-preservation"]{static preservation})
   (define K-D-preservation @tr-ref[#:key "K-D-preservation"]{dynamic preservation})

   (define K-S-completion @tr-ref[#:key "K-S-completion"]{@${\carrow} static soundness})
   (define K-D-completion @tr-ref[#:key "K-D-completion"]{@${\carrow} dynamic soundness})

   (define K-S-factor @tr-ref[#:key "K-S-factor"]{boundary factoring})
   (define K-D-factor @tr-ref[#:key "K-D-factor"]{boundary factoring})

   (define K-boundary @tr-ref[#:key "K-boundary"]{inner boundary})

   (define K-S-uec @tr-ref[#:key "K-S-uec"]{unique evaluation contexts})
   (define K-D-uec @tr-ref[#:key "K-D-uec"]{unique evaluation contexts})

   (define K-S-hole-typing @tr-ref[#:key "K-S-hole-typing"]{static hole typing})
   (define K-D-hole-typing @tr-ref[#:key "K-D-hole-typing"]{dynamic hole typing})

   (define K-boundary-typing @tr-ref[#:key "K-boundary-typing"]{boundary hole typing})
   (define K-DS-hole @tr-ref[#:key "K-DS-hole"]{static @${\vdyn} hole typing})
   (define K-DD-hole @tr-ref[#:key "K-DD-hole"]{dynamic @${\vdyn} hole typing})
   (define K-SS-hole @tr-ref[#:key "K-SS-hole"]{static @${\vsta} hole typing})
   (define K-SD-hole @tr-ref[#:key "K-SD-hole"]{dynamic @${\vsta} hole typing})

   (define K-hole-subst @tr-ref[#:key "K-hole-subst"]{hole substitution})
   (define K-DS-hole-subst @tr-ref[#:key "K-DS-hole-subst"]{dynamic context static hole substitution})
   (define K-DD-hole-subst @tr-ref[#:key "K-DD-hole-subst"]{dynamic context dynamic hole substitution})
   (define K-SS-hole-subst @tr-ref[#:key "K-SS-hole-subst"]{static context static hole substitution})
   (define K-SD-hole-subst @tr-ref[#:key "K-SD-hole-subst"]{static context dynamic hole substitution})

   (define K-S-hole-subst @tr-ref[#:key "K-S-hole-subst"]{static boundary-free hole substitution})
   (define K-D-hole-subst @tr-ref[#:key "K-D-hole-subst"]{dynamic boundary-free hole substitution})

   (define K-S-inversion @tr-ref[#:key "K-S-inversion"]{@${\langK} inversion})
   (define K-D-inversion @tr-ref[#:key "K-D-inversion"]{@${\langK} inversion})

   (define K-S-canonical @tr-ref[#:key "K-S-canonical"]{canonical forms})

   (define K-Delta-soundness @tr-ref[#:key "K-Delta-soundness"]{@${\Delta} tag soundness})
   (define K-Delta-inversion @tr-ref[#:key "K-Delta-inversion"]{@${\Delta} inversion})
   (define K-Delta-preservation @tr-ref[#:key "K-Delta-tag-preservation"]{@${\Delta} tag preservation})

   (define K-delta-preservation @tr-ref[#:key "K-delta-preservation"]{@${\delta} preservation})

   (define K-fromdyn-soundness @tr-ref[#:key "K-fromdyn-soundness"]{@${\vfromdynK} soundness})
   (define K-fromsta-soundness @tr-ref[#:key "K-fromsta-soundness"]{@${\vfromstaK} soundness})

   (define K-check @tr-ref[#:key "K-check"]{check soundness})
   (define K-subt-preservation @tr-ref[#:key "K-subt-preservation"]{subtyping preservation})

   (define K-S-value-inversion @tr-ref[#:key "K-S-value-inversion"]{static value inversion})
   (define K-D-value-inversion @tr-ref[#:key "K-D-value-inversion"]{dynamic value inversion})

   (define K-subst @tr-ref[#:key "K-subst"]{substitution})
   (define K-DS-subst @tr-ref[#:key "K-DS-subst"]{dynamic context static value substitution})
   (define K-DD-subst @tr-ref[#:key "K-DD-subst"]{dynamic context dynamic value substitution})
   (define K-SS-subst @tr-ref[#:key "K-SS-subst"]{static context static value substitution})
   (define K-SD-subst @tr-ref[#:key "K-SD-subst"]{static context dynamic value substitution})

   (define K-weakening @tr-ref[#:key "K-weakening"]{weakening})

   (define M-uec @tr-ref[#:key "KM-uec"]{@${\langM} unique static evaluation contexts})
   (define M-subst @tr-ref[#:key "KM-subst"]{substitution})
   (define M-delta-preservation @tr-ref[#:key "KM-delta-preservation"]{@${\delta} preservation})
   (define M-weakening @tr-ref[#:key "KM-weakening"]{weakening})
   (define M-S-canonical @tr-ref[#:key "KM-S-canonical"]{static canonical forms})
   (define M-S-inversion @tr-ref[#:key "KM-S-inversion"]{static inversion forms})
)
@(provide
  K-S-completion
  K-D-completion
  K-S-factor
  K-S-hole-typing
  K-subt-preservation
  K-S-inversion
  K-D-inversion)

@tr-theorem[#:key "K-S-soundness" @elem{static @${\langK}-soundness}]{
  If @${\wellM e : \tau}
   then @${\wellM e : \tau \carrow e''}
   and @${\wellKE e'' : \tagof{\tau}}
   and one of the following holds:
@itemlist[
  @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
  @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
  @item{ @${e'' \rrKSstar \ctxE{\edynfake{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
  @item{ @${e'' \rrKSstar \boundaryerror} }
  @item{ @${e''} diverges }
]}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellKE e : \tau \carrow e''
         @tr-and[]
         \wellKE e'' : \tagof{\tau}}
      @|K-S-completion|
    }}
    @item{@tr-qed{
      by @|K-S-progress| and @|K-S-preservation|
    }}
  ]
}

@tr-theorem[#:key "K-D-soundness" @elem{dynamic @${\langK}-soundness}]{
  If @${\wellM e}
   then @${\wellM e \carrow e''}
   and @${\wellKE e''}
   and one of the following holds:
@itemlist[
  @item{ @${e'' \rrKDstar v} and @${\wellKE v} }
  @item{ @${e'' \rrKDstar \ctxE{e'} \mbox{ and } e' \rrKD \tagerror} }
  @item{ @${e'' \rrKDstar \boundaryerror} }
  @item{ @${e''} diverges }
]}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellKE e \carrow e''
         @tr-and[]
         \wellKE e''}
      @|K-D-completion|
    }}
    @item{@tr-qed{
      by @|K-D-progress| and @|K-D-preservation|
    }}
  ]
}

@tr-theorem[#:key "K-bf-soundness" @elem{boundary-free @${\langK}-soundness}]{
  If @${\wellM e : \tau}
  and @${e} is boundary-free
  then one of the following holds:
  @itemlist[
    @item{ @${e \rrKSstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrKSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @tr-qed{
    by @tr-ref[#:key "K-bf-S-progress"]{progress} and @tr-ref[#:key "K-bf-S-preservation"]{preservation}
  }
}

@tr-theorem[#:key "NK-base-type" @elem{@${\langN}/@${\langK} base type equivalence}]{
  If @${\wellM e : \tau} and all boundary terms in @${e} are of the following four forms:
  @itemlist[
  @item{ @${\edyn{\tint}{e'}} }
  @item{ @${\esta{\tint}{e'}} }
  @item{ @${\esta{\tnat}{e'}} }
  @item{ @${\edyn{\tnat}{e'}} }
  ]
  and @${\wellM e : \tau \carrow e''}, then @${e \rrNSstar v} if and only if
  @${e'' \rrKSstar v}.
}
@tr-proof{
  @itemlist[#:style 'ordered
  @item{
  @tr-step{
    @${\efromdynN{\tint}{v} = \efromdynK{\tint}{v}}
    by definition
  }}
  @item{
  @tr-step{
    @${\efromdynN{\tnat}{v} = \efromdynK{\tnat}{v}}
    by definition
  }}
  @item{
  @tr-step{
    @${\efromstaN{\tint}{v} = \efromstaK{\tint}{v}}
    by definition
  }}
  @item{
  @tr-step{
    @${\efromstaN{\tnat}{v} = \efromstaK{\tnat}{v}}
    by definition
  }}
  @item{
  @tr-qed{
  }}
  ]
}

@tr-corollary[#:key "K-compilation" @elem{@${\langK} compilation}]{
  If @${\wellM e : \tau}

  and @${\wellM e : \tau \carrow e''}

  and @${\wellKE e'' : \tagof{\tau}}

  and
    @${\rrKD'} is similar to @${\rrKD} but without the no-op boundaries, as follows:

    @$|{
      \begin{array}{l@{\hspace{0.5em}}c@{\hspace{0.5em}}l}
        \echk{K}{v} & \rrKD'
        & \efromany{K}{v}
        \\
        \eapp{v_0}{v_1} & \rrKD' & \tagerror
        \\ \sidecond{if $v_0 \in \integers$ or $v_0 = \vpair{v}{v'}$}
        \\
        \eapp{(\vlam{\tann{x}{\tau}}{e})}{v} & \rrKD'
        & \boundaryerror
        \\ \sidecond{if $\efromany{\tagof{\tau}}{v} = \boundaryerror$}
        \\
        \eapp{(\vlam{\tann{x}{\tau}}{e})}{v} & \rrKD'
        & \vsubst{e}{x}{\efromany{\tagof{\tau}}{v}}
        \\
        (\vlam{x}{e})~v & \rrKD' & \vsubst{e}{x}{v}
        \\
        \eunop{v} & \rrKD'
        & \tagerror
        \\ \sidecond{if $\delta(\vunop, v)$ is undefined}
        \\
        \eunop{v} & \rrKD'
        & \delta(\vunop, v)
        \\
        \ebinop{v_0}{v_1} & \rrKD'
        & \tagerror
        \\ \sidecond{if $\delta(\vbinop, v_0, v_1)$ is undefined}
        \\
        \ebinop{v_0}{v_1} & \rrKD'
        & \delta(\vbinop, v_0, v_1)
      \end{array}
    }|

  and
    @${e \ccKD' e} is defined as:

      @$|{
      \begin{array}{l@{\hspace{0.5em}}c@{\hspace{0.5em}}l}
        \esd[e] & \ccKD' & \ctxE{e'}
        \\ \sidecond{if $e \rrKD' e'$}
        \\
        \esd[\esta{\tau}{v}] & \ccKD' & \esd[\efromdynK{\tau}{v}]
        \\
        \esd[\edyn{\tau}{v}] & \ccKD' & \esd[\efromdynK{\tau}{v}]
        \\
        \esd[\eerr] & \ccKD' & \eerr
       \end{array}
      }|

  and @${{\rrKDstar}'} is the reflexive transitive closure of @${\ccKD'}

  @linebreak[]
  then one of the following holds:
  @itemlist[
    @item{ @${e'' {\rrKDstar}'~v \mbox{ and } \wellKE v : \tagof{\tau}} }
    @item{ @${e'' {\rrKDstar}'~\tagerror} }
    @item{ @${e'' {\rrKDstar}'~\boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof[#:sketch? #true]{
  By @|K-S-soundness| and the fact that @${\rrKS} is a subset of @${\rrKD'}
   (modulo the @${\edynfake{e}} and @${\estafake{e}} boundaries).
}


@|clearpage|
@section{@|FOlong| Lemmas}

@tr-lemma[#:key "K-fromdyn-soundness" @elem{@${\vfromdynK} soundness}]{
  If @${\wellKE v} then @${\wellKE \efromdynK{\tau}{v} : \tagof{\tau}}.
}@tr-proof{
  @itemlist[
  @item{
    @tr-step{
      @${\efromdynK{\tau}{v} = \efromany{\tagof{\tau}}{v}}
    }}
  @item{
    @tr-qed{ by @|K-check| }
  }
  ]
}

@tr-lemma[#:key "K-fromsta-soundness" @elem{@${\vfromstaK} soundness}]{
  If @${\wellKE v : \tau} then @${\wellKE \efromstaK{\tau}{v}}.
}@tr-proof{
  @itemlist[
  @item{
    @tr-step{
      @${\efromstaK{\tau}{v} = \efromany{\tagof{\tau}}{v}}
    }}
  @item{
    @tr-qed{ @|K-check| }
  }
  ]
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
              }{
                \Gamma \wellM \eerr : \tau
              }}]{
    @tr-step{
      @${\Gamma \wellM \eerr : \tau \carrow \eerr}
    }
    @tr-step{
      @${\Gamma \wellKE \eerr : \tau}
    }
    @tr-qed{}
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
    @tr-qed{
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
              }{
                \Gamma \wellM \eerr
              }}]{
    @tr-step{
      @${\Gamma \wellM \eerr \carrow \eerr}
    }
    @tr-step{
      @${\Gamma \wellKE \eerr}
    }
    @tr-qed{}
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
      by (2,3)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-progress" @elem{@${\langK} static progress}]{
  If @${\wellKE e : K} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccKS e'} }
    @item{ @${e \ccKS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \ccKD \tagerror} }
    @item{ @${e \eeq \ctxE{\edynfake{\ebase[e']}} \mbox{ and } e' \ccKD \tagerror} }
]}@tr-proof{
  By the @|K-S-factor| lemma, there are ten cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed{}
  }

  @tr-case[@${e \eeq \ebase[{v_0~v_1}]}]{
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
          @${e \ccKS \ebase[{\edynfake{(\vsubst{e'}{x}{v_1})}}]}
          @${\vapp{(\vlam{x}{e'})}{v_1} \rrKS (\edynfake{(\vsubst{e'}{x}{v_1})})}]
        @tr-qed[]
      }
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}
                @tr-and[2]
                \efromany{\tagof{\tau_d}}{v_1} = v_1}]{
        @tr-step[
          @${e \ccKS \ebase[{\vsubst{e'}{x}{v_1}}]}
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \vsubst{e'}{x}{v_1}}]
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}
                  @tr-and[4]
                  \efromany{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
        @tr-step[
          @${e \ccKS \ebase[\boundaryerror]}
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \boundaryerror}]
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ebase[{\eunop{v}}]}]{
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
      @${e \ccKS \ebase[{v_i}]}
      @${(\eunop{v}) \rrKS v_i}}
    @tr-qed[]
  }

  @tr-case[@${e \eeq \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${\wellKE \ebinop{v_0}{v_1} : K'}
      @|K-S-hole-typing|}
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[] \wellKE v_1 : K_1
         @tr-and[] \Delta(\vbinop, K_0, K_1) = K_2}
      @|K-S-inversion| (1)}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = e''}
      @|K-Delta-soundness|}
    @tr-qed{
      by @${e \ccKS \ebase[e'']}
    }
  }

  @tr-case[@${e \eeq \ebase[{\echk{K}{v_0}}]}]{
    @tr-step{
      @${e \ccKS \ebase[\efromany{K}{v}]}
    }
    @tr-qed[]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edynfake{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKD e''
         @tr-or[]
         e' \ccKD \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{v}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKD e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edynfake{e''}}}
        }
      }
      @tr-if[@${e' \ccKD \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edynfake{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-step{
          @${\esd' \in \ebase}
          @elem{@${e'} is boundary-free}
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\estafake{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKS e''
         @tr-or[]
         e' \ccKS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
         @tr-or[]
         e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{e'}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKS e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\estafake{e''}}}
        }
      }
      @tr-if[@${e' \ccKS \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\estafake{\boundaryerror}}}
        }
      }
      @tr-if[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
      @tr-else[@${e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edyn{\tau}{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKD e''
         @tr-or[]
         e' \ccKD \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{\efromdynK{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKD e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccKD \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-step{
          @${\esd' \in \ebase}
          @elem{@${e'} is boundary-free}
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\esta{\tau}{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKS e''
         @tr-or[]
         e' \ccKS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
         @tr-or[]
         e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{\efromstaK{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKS e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccKS \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-if[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
      @tr-else[@${e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-qed[@${e \ccKS \eerr}]
  }
}

@; -----------------------------------------------------------------------------

@tr-lemma[#:key "K-D-progress" @elem{@${\langK} dynamic progress}]{
  If @${\wellKE e : K} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccKD e'} }
    @item{ @${e \ccKD \boundaryerror} }
    @item{ @${e \eeq \ctxE{e'} \mbox{ and } e' \ccKD \tagerror} }
  ]
}@tr-proof{
  By the @|K-D-factor| lemma, there are nine cases.

  @tr-case[@${e \eeq v}]{
    @tr-qed[]
  }

  @tr-case[@${e \eeq \ebase[{v_0~v_1}]} #:itemize? #false]{
    @tr-if[@${v_0 \eeq \vlam{x}{e_0}}]{
      @tr-step[
        @${e \ccKD \ebase[{\vsubst{e_0}{x}{v_1}}]}
        @${(\vlam{x}{e_0})~v_1 \rrKD \vsubst{e_0}{x}{v_1}}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e_0}
              @tr-and[2]
              \efromany{\tagof{\tau_d}}{v_1} = v_1}]{
      @tr-step[
        @${e \ccKD \ebase[{\estafake{(\vsubst{e_0}{x}{v_1})}}]}
        @${(\vlam{\tann{x}{\tau_d}}{e_0})~v_1 \rrKD (\estafake{\vsubst{e_0}{x}{v_1}})}]
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e_0}
              @tr-and[2]
              \efromany{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
      @tr-step[
        @${e \ccKD \ebase[\boundaryerror]}
        @${(\vlam{\tann{x}{\tau_d}}{e_0})~v_1 \rrKD \boundaryerror}]
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step[
        @${e \ccKD \ebase[\tagerror]}
        @${v_0~v_1 \rrKD \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #f]{
    @tr-if[@${\delta(\vunop, v) = v'}]{
      @tr-step[
        @${e \ccKD \ebase[{v'}]}
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

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]} #:itemize? #f]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-qed{
        by @${e \ccKD \ctxE{e''}}
      }
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step[
        @${e \ccKD \ebase[\tagerror]}
        @${(\ebinop{v_0}{v_1}) \rrKD \tagerror}]
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\echk{K}{v_0}}]}]{
    @tr-contradiction{ @${\wellKE e} }
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edynfake{v}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKD e''
         @tr-or[]
         e' \ccKD \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{v}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKD e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edynfake{e''}}}
        }
      }
      @tr-if[@${e' \ccKD \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edynfake{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-step{
          @${\esd' \in \ebase}
          @elem{@${e'} is boundary-free}
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\estafake{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKS e''
         @tr-or[]
         e' \ccKS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
         @tr-or[]
         e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}
      @|K-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{e'}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKS e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\estafake{e''}}}
        }
      }
      @tr-if[@${e' \ccKS \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\estafake{\boundaryerror}}}
        }
      }
      @tr-if[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
      @tr-else[@${e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edyn{\tau}{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKD e''
         @tr-or[]
         e' \ccKD \boundaryerror
         @tr-or[]
         e' \eeq \ctxE{e''} \mbox{ and } e'' \rrKD \tagerror}
      @|K-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKD \ctxE{\efromdynK{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKD e'}
        }
      }
      @tr-if[@${e' \ccKD e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccKD \boundaryerror}]{
        @tr-qed{
          @${e \ccKD \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \ctxE{e''} \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-step{
          @${\esd \in \ebase}
          @${e'} is boundary-free
        }
        @tr-qed[]
      }
    ]
  }

  @tr-case[@elem{@${e \eeq \ctxE{\esta{\tau}{e'}}} where @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccKS e''
         @tr-or[]
         e' \ccKS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror
      }
      @|K-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccKS \ctxE{\efromstaK{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccKS e'}
        }
      }
      @tr-if[@${e' \ccKS e''}]{
        @tr-qed{
          @${e \ccKS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccKS \boundaryerror}]{
        @tr-qed{
          @${e \ccKS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-if[@${e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
      @tr-else[@${e' \eeq \esd''[{\edynfake{\ebase''[e'']}}] \mbox{ and } e'' \rrKD \tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccKD \eerr}
    }
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-preservation" @elem{@${\langK} static preservation}]{
  If @${\wellKE e : K} and @${e \ccKS e'} then @${\wellKE e' : K}
}@tr-proof{
  By the @|K-S-factor| lemma, there are ten cases to consider.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{ @${e \ccKS e'} }
  }

  @tr-case[@${e = \ebase[{v_0~v_1}]} #:itemize? #false]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccKS \ebase[{\edynfake{\vsubst{e'}{x}{v_1}}}]}]{
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
        @|K-subst| (3, 4)
      }
      @tr-step{
        @${\wellKE \edynfake{(\vsubst{e'}{x}{v_1})} : \kany}
        (5)
      }
      @tr-qed{
        by @|K-hole-subst|
      }
    }
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
              @tr-and[4]
              \efromany{\tagof{\tau}}{v_1} = \boundaryerror
              @tr-and[4]
              e \ccKD \ebase[\boundaryerror]}]{
      @tr-step{
        @${\wellKE \eapp{v_0}{v_1} : \kany}
        @|K-S-hole-typing|
      }
      @tr-step{
        @${\wellKE \boundaryerror : \kany}
      }
      @tr-qed{
        by @|K-hole-subst| (2)
      }
    }
    @tr-else[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
                @tr-and[4]
                e \ccKS \ebase[{\vsubst{e'}{x}{\efromany{\tagof{\tau}}{v_1}}}]}]{
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
        @${\wellKE \efromany{\tagof{\tau}}{v_1} : \tagof{\tau}}
        @|K-check| (2)}
      @tr-step{
        @${\wellKE \vsubst{e}{x}{\efromany{\tagof{\tau}}{v_1}} : \kany}
        @|K-subst| (3, 4)}
      @tr-qed{
        by @|K-hole-subst|
      }
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]
              @tr-and[4]
              \delta(\vunop, v) = v'
              @tr-and[4]
              e \ccKS \ebase[{v'}]}]{
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
      by @|K-hole-subst| (5)
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = e''
              @tr-and[4]
              e \ccKS \ebase[{e''}]}]{
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
      @${\wellKE e'' : K''}
      @|K-Delta-soundness| (3)
    }
    @tr-step{
      @${\wellKE e'' : K'}
      (2, 3)
    }
    @tr-qed{
      by @|K-hole-subst| (4)
    }
  }

  @tr-case[@${e = \ebase[\echk{K_0}{v_0}]}]{
    @tr-step{
      @${\ebase[{\echk{K_0}{v_0}}] \ccKS \ebase[\efromany{K_0}{v_0}]}
    }
    @tr-step{
      @${\wellKE \echk{K_0}{v} : K''}
      @|K-S-hole-typing|
    }
    @tr-step{
      @${K_0 \subkeq K''}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \efromany{K_0}{v_0} : K_0}
      @|K-check|
    }
    @tr-qed{
      by (3, 4, @|K-hole-subst|)
    }
  }

  @tr-case[@elem{@${e = \ctxE{\edynfake{e'}}} where @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKS \ctxE{e'}}
      }
      @tr-step{
        @${\wellKE \edynfake{e'} : \kany}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-value-inversion| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKD e''}]{
      @tr-step{
        @${e \ccKS \ctxE{\edynfake{e''}}}
      }
      @tr-step{
        @${\wellKE \edynfake{e'} : \kany}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e''}
        @|K-D-preservation| (3)
      }
      @tr-step{
        @${\wellKE \edynfake{e''} : \kany}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\estafake{e'}}} where @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKS \ctxE{e'}}
      }
      @tr-step{
        @${\wellKE \estafake{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-value-inversion| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKS e''}]{
      @tr-step{
        @${e \ccKS \ctxE{\estafake{e''}}}
      }
      @tr-step{
        @${\wellKE \estafake{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'' : \kany}
        @|K-S-preservation| (3)
      }
      @tr-step{
        @${\wellKE \estafake{e''}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau}{e'}}} where @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKS \ctxE{\efromdynK{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e'} : \tagof{\tau'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE \efromdynK{\tau'}{e'} : \tagof{\tau'}}
        @|K-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKD e''}]{
      @tr-step{
        @${e \ccKS \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e'} : \tagof{\tau'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e''}
        @|K-D-preservation| (3)
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e''} : \tagof{\tau'}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau}{e'}}} where @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKS \ctxE{\efromstaK{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \tagof{\tau'}}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE \efromstaK{\tau'}{e'}}
        @|K-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKS e''}]{
      @tr-step{
        @${e \ccKS \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \tagof{\tau'}}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'' : \tagof{\tau'}}
        @|K-S-preservation| (3)
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccKS \eerr}
    }
    @tr-qed{
      @${\wellKE \eerr : K}
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-preservation" @elem{@${\langK} dynamic preservation}]{
  If @${\wellKE e} and @${e \ccKD e'} then @${\wellKE e'}
}@tr-proof{
  By @|K-D-factor| there are nine cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccKD e'}}
  }

  @tr-case[@${e = \ebase[{v_0~v_1}]} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{x}{e'}
              @tr-and[2]
              e \ccKD \ebase[{\vsubst{e'}{x}{v_1}}]}]{
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
        @|K-subst| (2, 3)
      }
      @tr-qed{
        by @|K-hole-subst|
      }
    }
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
                @tr-and[4]
                \efromany{\tagof{\tau}}{v_1} = \boundaryerror
                @tr-and[4]
                e \ccKD \ebase[\boundaryerror]}]{
      @tr-step{
        @${\wellKE \eapp{v_0}{v_1}}
        @|K-D-hole-typing|
      }
      @tr-step{
        @${\wellKE \boundaryerror}
      }
      @tr-qed{
        by @|K-hole-subst| (2)
      }
    }
    @tr-else[@${v_0 = \vlam{\tann{x}{\tau}}{e'}
                @tr-and[4]
                e \ccKD \ebase[{\estafake{(\vsubst{e'}{x}{\efromany{\tagof{\tau}}{v_1}})}}]}]{
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
        @${\wellKE \efromany{\tagof{\tau}}{v_1} : \tagof{\tau}}
        @|K-check| (2)}
      @tr-step{
        @${\wellKE \vsubst{e}{x}{\efromany{\tagof{\tau}}{v_1}} : \kany}
        @|K-subst| (3, 4)
      }
      @tr-step{
        @${\wellKE \estafake{(\vsubst{e}{x}{\efromany{\tagof{\tau}}{v_1}})}}
        (5)
      }
      @tr-qed{
        by @|K-hole-subst| (6)
      }
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]
              @tr-and[4]
              \delta(\vunop, v) = v'
              @tr-and[4]
              e \ccKD \ebase[v']}]{
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
      by @|K-hole-subst| (3)
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]
              @tr-and[4]
              \delta(\vbinop, v_0, v_1) = e''
              @tr-and[4]
              e \ccKD \ebase[{e''}]}]{
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
      @${\wellKE e''}
      @|K-delta-preservation| (2)
    }
    @tr-qed{
      by @|K-hole-subst| (3)
    }
  }

  @tr-case[@elem{@${e = \esd[{\edynfake{e'}}]} where @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKD \ctxE{e'}}
      }
      @tr-step{
        @${\wellKE \edynfake{e'} : \kany}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKD e''}]{
      @tr-step{
        @${e \ccKD \ctxE{\edynfake{e''}}}
      }
      @tr-step{
        @${\wellKE \edynfake{e'} : \kany}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e''}
        @|K-D-preservation| (3)
      }
      @tr-step{
        @${\wellKE \edynfake{e''} : \kany}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[{\estafake{e'}}]} where @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccKD \ctxE{e'}}
      }
      @tr-step{
        @${\wellKE \estafake{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-value-inversion| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
    @tr-else[@${e' \ccKS e''}]{
      @tr-step{
        @${e \ccKD \ctxE{\estafake{e''}}}
      }
      @tr-step{
        @${\wellKE \estafake{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \kany}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'' : \kany}
        @|K-S-preservation| (3)
      }
      @tr-step{
        @${\wellKE \estafake{e''}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[{\edyn{\tau}{e'}}]} where @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccKD \ctxE{\efromdynK{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e'} : \tagof{\tau'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e'}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE \efromdynK{\tau'}{e'} : \tagof{\tau'}}
        @|K-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccKD e''}]{
      @tr-step{
        @${e \ccKD \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e'} : \tagof{\tau'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' 
           @tr-and[]
           \tau' \subteq \tau''}
        @|K-S-inversion| (2)
      }
      @tr-step{
        @${\wellKE e''}
        @|K-D-preservation| (3)
      }
      @tr-step{
        @${\wellKE \edyn{\tau'}{e''} : \tagof{\tau'}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[{\esta{\tau}{e'}}]} where @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccKD \ctxE{\efromstaK{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \tagof{\tau'}}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE \efromstaK{\tau'}{e'}}
        @|K-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
    @tr-else[@${e' \ccKS e''}]{
      @tr-step{
        @${e \ccKD \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e'}}
        @|K-boundary-typing|
      }
      @tr-step{
        @${\wellKE e' : \tagof{\tau'}}
        @|K-D-inversion| (2)
      }
      @tr-step{
        @${\wellKE e'' : \tagof{\tau'}}
        @|K-S-preservation| (3)
      }
      @tr-step{
        @${\wellKE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|K-hole-subst| (5)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccKD \eerr}}
    @tr-qed{
      @${\wellKE \eerr}
    }
  }

}

@; -----------------------------------------------------------------------------

@tr-lemma[#:key "K-bf-S-progress" @elem{boundary-free progress}]{
  If @${\wellM e : \tau} and @${e} is boundary-free, then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccKS e'} }
    @item{ @${e \ccKS \boundaryerror} }
  ]
}@tr-proof{
  By the @|M-uec| lemma, there are five cases:

  @tr-case[@${e = v}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[{\vapp{v_0}{v_1}}]} #:itemize? #f]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau'}}{e'}}]{
      @tr-step{
        @${e \ccKS \ebase[{\vsubst{e'}{x}{v_1}}]}
        @${\vapp{v_0}{v_1} \rrKS \vsubst{e'}{x}{v_1}}}
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

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vunop, v) = e''}]{
      @tr-step{
        @${e \ccKS \ebase[{e''}]}
        @${(\eunop{v}) \rrKS e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${e \ccKS \ebase[{e''}]}
        @${(\ebinop{v_0}{v_1}) \rrKS e''}}
      @tr-qed[]
    }
    @tr-if[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @tr-step{
        @${e \ccKS \boundaryerror}
        @${(\ebinop{v_0}{v_1}) \rrKS \boundaryerror}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ebase[{\eerr}]}]{
    @tr-step{
      @${\ebase[{\eerr}] \ccKS \eerr}}
    @tr-qed[]
  }

}

@tr-lemma[#:key "K-bf-S-preservation" @elem{@${\langK} boundary-free preservation}]{
  If @${\wellM e : \tau} and @${e} is boundary-free and @${e \ccKS e'}
  then @${\wellM e' : \tau} and @${e'} is boundary-free.
}@tr-proof{
  By the @|M-uec| lemma, there are five cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{ @${e \ccKS e'} }
  }

  @tr-case[@${e = \ebase[{\vapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_d}}{e'}}]{
      @tr-step{
        @${\ebase[{v_0~v_1}] \ccKS \ebase[{\vsubst{e'}{x}{v_1}}]}}
      @tr-step{
        @${\wellM \eapp{v_0}{v_1} : \tau_c}}
      @tr-step{
        @${\wellM v_0 : \tarr{\tau_d}{\tau_c} @tr-and[] \wellM v_1 : \tau_d}
        (2)}
      @tr-step{
        @${\tann{x}{\tau_d} \wellM e' : \tau_c}
        (3)}
      @tr-step{
        @${\wellM \vsubst{e'}{x}{v_1} : \tau_c}
        @|M-subst| (3, 4)}
      @tr-step{
        @elem{@${\vsubst{e'}{x}{v_1}} is boundary-free}
        @elem{@${e'} and @${v_1} are boundary-free}}
      @tr-qed[]
    }
    @tr-else[""]{
      @tr-contradiction{@${\wellM e : \tau}}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]}]{
    @tr-step{
      @${\ebase[{\eunop{v}}] \ccKS \ebase[{v'}]
         @tr-and[]
         \delta(\vunop, v) = e''}}
    @tr-step{
      @${\wellM \eunop{v} : \tau'}}
    @tr-step{
      @${\wellM v : \tau_0}}
    @tr-step{
      @${\wellM e'' : \tau'}
      @|M-delta-preservation| (3)}
    @tr-qed{}
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${\ebase[{\ebinop{v_0}{v_1}}] \ccKS \ebase[{v'}]
         @tr-and[]
         \delta(\vbinop, v_0, v_1) = e''}}
    @tr-step{
      @${\wellM \ebinop{v_0}{v_1} : \tau'}}
    @tr-step{
      @${\wellM v_0 : \tau_0 @tr-and[] \wellM v_1 : \tau_1}
    }
    @tr-step{
      @${\wellM e'' : \tau'}
      @|M-delta-preservation| (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \ebase[{\eerr}]}]{
    @tr-step{
      @${\ebase[{\eerr}] \ccKS \eerr}}
    @tr-qed{
      by @${\wellM \eerr : \tau} }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-check" @elem{@${\vfromany} soundness}]{
  For all @${K} and @${v}, @${\wellKE \efromany{K}{v} : K}.
}@tr-proof{
  @tr-case[@${\wellKE v : K}]{
    @tr-step{
      @${\efromany{K}{v} = v}
    }
    @tr-qed[]
  }

  @tr-case[@${\not\wellKE v : K}]{
    @tr-step{
      @${\efromany{K}{v} = \boundaryerror}
    }
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-factor" @elem{@${\langK} static boundary factoring}]{
  If @${\wellKE e : K} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ebase[\eapp{v_0}{v_1}]} }
    @item{ @${e = \ebase[\eunop{v}]} }
    @item{ @${e = \ebase[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \ebase[\echk{K}{v}]} }
    @item{ @${e = \esd[\edynfake{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\estafake{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\edyn{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\esta{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\eerr]} }
  ]
}@tr-proof{
  By the @|K-S-uec| lemma, there are ten cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \esd[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}] }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eapp{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\eapp{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\eapp{v_0}{v_1}]}]}]
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
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]
        }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eunop{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\eunop{v}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\eunop{v}]}]}]
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
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]
         }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\ebinop{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\edynfake{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\estafake{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
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

@tr-lemma[#:key "K-S-uec" @elem{@${\langK} unique static evaluation contexts}]{
  If @${\wellKE e : K} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\echk{K}{v}}} }
    @item{ @${e = \ctxE{\edynfake{v}}} }
    @item{ @${e = \ctxE{\estafake{v}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{v}}} }
    @item{ @${e = \ctxE{\esta{\tau}{v}}} }
    @item{ @${e = \ctxE{\eerr}} }
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

  @tr-case[@${e = \edynfake{e_0}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellKE e_0}
        @|K-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|K-D-uec| (1)
      }
      @tr-step{
        @${\ED = \edynfake{\ED_0}}
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
        @${e = \ED[\edynfake{e_0}]}
      }
    }
  }

  @tr-case[@${e = \estafake{e_0}}]{
    @tr-contradiction{@${\wellKE e : K}}
  }

  @tr-case[@${e = \edyn{\tau}{e_0}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellKE e_0}
        @|K-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|K-D-uec| (1)
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

  @tr-case[@${e = \esta{K'}{e_0}}]{
    @tr-contradiction{@${\wellKE e : K}}
  }

  @tr-case[@${e = \eerr}]{
    @tr-step{
      @${\esd = \ehole}
    }
    @tr-qed[@${e = \esd[\eerr]}]
  }

}

@tr-lemma[#:key "K-boundary" @elem{@${\langK} inner boundary}]{
  For all contexts @${\esd}, one of the following holds:
  @itemlist[
  @item{@${\esd = \ebase}}
  @item{@${\esd = \esd'[\edynfake{v}]}}
  @item{@${\esd = \esd'[\estafake{v}]}}
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_1 = \esd_1'[\edynfake{\ebase}]
         @tr-or[]
         \esd_1 = \esd_1'[\estafake{\ebase}]
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
      @tr-if[@${\esd_1 = \esd_1'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_1 = \esd_1'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eapp{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
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
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]}
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_1 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_1 = \esd_1'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_1 = \esd_1'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \vpair{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eunop{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \eunop{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{\esd_0'}{e_1}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_1 = \esd_1'[\edynfake{\ebase}]
         @tr-or[]
         \esd_1 = \esd_1'[\estafake{\ebase}]
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
      @tr-if[@${\esd_1 = \esd_1'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_1 = \esd_1'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \ebinop{v_0}{\esd_1'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau'}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \edynfake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \edynfake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \edynfake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau'}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \edynfake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau'}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
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
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \estafake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \estafake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \estafake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau'}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau'}{\ebase}]}]{
        @tr-step{
          @${\esd' = \estafake{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau'}{\ebase}]}
        ]
      }
    ]
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau'}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau'}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \edyn{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \edyn{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
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
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \esta{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \esta{\tau}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
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

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-step{
      @${\esd_0 = \ebase
         @tr-or[]
         \esd_0 = \esd_0'[\edynfake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\estafake{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd_0 = \esd_0'[\esta{\tau}{\ebase}]
         }
      @tr-IH
    }
    @list[
      @tr-if[@${\esd_0 = \ebase}]{
        @tr-qed{@${\esd} is boundary-free}
      }
      @tr-if[@${\esd_0 = \esd_0'[\edynfake{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{K_0}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edynfake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\estafake{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{K_0}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\estafake{\ebase}]}
        ]
      }
      @tr-if[@${\esd_0 = \esd_0'[\edyn{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{K_0}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\edyn{\tau}{\ebase}]}
        ]
      }
      @tr-else[@${\esd_0 = \esd_0'[\esta{\tau}{\ebase}]}]{
        @tr-step{
          @${\esd' = \echk{K_0}{\esd_0'}}
        }
        @tr-qed[
          @${\esd = \esd'[\esta{\tau}{\ebase}]}
        ]
      }
    ]
  }

}

@tr-lemma[#:key "K-D-factor" @elem{@${\langK} dynamic boundary factoring}]{
  If @${\wellKE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value}
    @item{ @${e = \ebase[\eapp{v_0}{v_1}]} }
    @item{ @${e = \ebase[\eunop{v}]} }
    @item{ @${e = \ebase[\ebinop{v_0}{v_1}]} }
    @item{ @${e = \esd[\edynfake{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\estafake{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\edyn{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\esta{\tau}{e'}]} where @${e'} is boundary-free }
    @item{ @${e = \esd[\eerr]} }
  ]
}@tr-proof{
  By the @|K-D-uec| lemma, there are ten cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \esd[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]
         }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eapp{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\eapp{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\eapp{v_0}{v_1}]}]}]
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
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]
         }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\eunop{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\eunop{v}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\eunop{v}]}]}]
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
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]}
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\ebinop{v_0}{v_1}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\ebinop{v_0}{v_1}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\echk{K'}{v}]}]{
    @tr-step{
      @${\esd = \ebase
         @tr-or[]
         \esd = \esd'[\edynfake{\ebase}]
         @tr-or[]
         \esd = \esd'[\estafake{\ebase}]
         @tr-or[]
         \esd = \esd'[\edyn{\tau}{\ebase}]
         @tr-or[]
         \esd = \esd'[\esta{\tau}{\ebase}]
         }
      @|K-boundary|
    }
    @list[
      @tr-if[@${\esd = \ebase}]{
        @tr-qed[@${e = \ebase[\echk{K'}{v}]}]
      }
      @tr-if[@${\esd = \esd'[\edynfake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edynfake{\ebase[\echk{K'}{v}]}]}]
      }
      @tr-if[@${\esd = \esd'[\estafake{\ebase}]}]{
        @tr-qed[@${e = \esd'[\estafake{\ebase[\echk{K'}{v}]}]}]
      }
      @tr-if[@${\esd = \esd'[\edyn{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\edyn{\tau}{\ebase[\echk{K'}{v}]}]}]
      }
      @tr-else[@${\esd = \esd'[\esta{\tau}{\ebase}]}]{
        @tr-qed[@${e = \esd'[\esta{\tau}{\ebase[\echk{K'}{v}]}]}]
      }
    ]
  }

  @tr-case[@${e = \esd[\edynfake{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
  }

  @tr-case[@${e = \esd[\estafake{v}]}]{
    @tr-qed{
      @${v} is boundary-free
    }
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

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-uec" @elem{@${\langK} unique dynamic evaluation contexts}]{
  If @${\wellKE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\echk{K}{v}}} }
    @item{ @${e = \ctxE{\edynfake{v}}} }
    @item{ @${e = \ctxE{\estafake{v}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{v}}} }
    @item{ @${e = \ctxE{\esta{\tau}{v}}} }
    @item{ @${e = \ctxE{\eerr}} }
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

  @tr-case[@${e = \eunop{e_0}} #:itemize? #false]{
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

  @tr-case[@${e = \echk{K}{e'}}]{
    @tr-contradiction{ @${\wellKE e} }
  }

  @tr-case[@${e = \edynfake{e_0}}]{
    @tr-contradiction{ @${\wellKE e} }
  }

  @tr-case[@${e = \estafake{e_0}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellKE e_0}
        @|K-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|K-D-uec| (1)
      }
      @tr-step{
        @${\ED = \estafake{\ED_0}}
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
        @${e = \ED[\estafake{e_0}]}
      }
    }
  }

  @tr-case[@${e = \edynfake{e_0}} #:itemize? #f]{
    @tr-contradiction{ @${\wellKE e} }
  }

  @tr-case[@${e = \esta{K_0}{e_0}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${\wellKE e_0}
        @|K-S-inversion|
      }
      @tr-step{
        @${e_0 = \ED_0[e_0']}
        @|K-S-uec| (1)
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

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-hole-typing" @elem{@${\langK} static hole typing}]{
  If @${\wellKE \ebase[{e}] : K} then the typing derivation contains a sub-term
   @${\wellKE e : K'} for some @${K'}.
}@tr-proof{
  By induction on the structure of @${\ebase}.

  @tr-case[@${\ebase = \ehole}]{
    @tr-qed{@${\ebase[{e}] = e}}
  }

  @tr-case[@${\ebase = \ebase_0~e_1}]{
    @tr-step{
      @${\ebase[{e}] = \ebase_0[e]~e_1}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : \kfun}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = v_0~\ebase_1}]{
    @tr-step{
      @${\ebase[{e}] = v_0~\ebase_1[e]}
    }
    @tr-step{
      @${\wellKE \ebase_1[e] : \kany}
      @|K-S-inversion|
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
      @${\wellKE \ebase_0[e] : \kany}
      @|K-S-inversion|
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
      @${\wellKE \ebase_1[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : \kpair}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \echk{K}{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \echk{K}{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-hole-typing" @elem{@${\langK} dynamic hole typing}]{
  If @${\wellKE \ebase[{e}]} then the derivation contains a sub-term @${\wellKE e}
}@tr-proof{
  By induction on the structure of @${\ebase}.

  @tr-case[@${\ebase = \ehole}]{
    @tr-qed{@${\ebase[{e}] = e}}
  }

  @tr-case[@${\ebase = \ebase_0~e_1}]{
    @tr-step{
      @${\ebase[{e}] = \ebase_0[e]~e_1}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = v_0~\ebase_1}]{
    @tr-step{
      @${\ebase[{e}] = v_0~\ebase_1[e]}
    }
    @tr-step{
      @${\wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \vpair{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \eunop{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \ebinop{v_0}{\ebase_1}}]{
    @tr-step{
      @${\ebase[{e}] = \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      @tr-IH (2)
    }
  }

  @tr-case[@${\ebase = \echk{K}{\ebase_0}}]{
    @tr-contradiction{ @${\wellKE \ebase[{e}]} }
  }
}

@tr-lemma[#:key "K-boundary-typing" @elem{@${\langK} boundary hole typing}]{
  @itemlist[
  @item{
    If @${\wellKE \ctxE{\edynfake{e}}} then the derivation contains a
    sub-term @${\wellKE \edynfake{e} : \kany}
  }
  @item{
    If @${\wellKE \ctxE{\edynfake{e}} : K'} then the derivation contains a
    sub-term @${\wellKE \edynfake{e} : \kany}
  }
  @item{
    If @${\wellKE \ctxE{\estafake{e}}} then the derivation contains a
    sub-term @${\wellKE \estafake{e}}
  }
  @item{
    If @${\wellKE \ctxE{\estafake{e}} : K'} then the derivation contains a
    sub-term @${\wellKE \estafake{e}}
  }
  @item{
    If @${\wellKE \ctxE{\edyn{\tau}{e}}} then the derivation contains a
    sub-term @${\wellKE \edyn{\tau}{e} : \tagof{\tau}}
  }
  @item{
    If @${\wellKE \ctxE{\edyn{\tau}{e}} : K'} then the derivation contains a
    sub-term @${\wellKE \edyn{\tau}{e} : \tagof{\tau}}
  }
  @item{
    If @${\wellKE \ctxE{\esta{\tau}{e}}} then the derivation contains a
    sub-term @${\wellKE \esta{\tau}{e}}
  }
  @item{
    If @${\wellKE \ctxE{\esta{\tau}{e}} : K'} then the derivation contains a
    sub-term @${\wellKE \esta{\tau}{e}}
  }
  ]
}@tr-proof{
  By the following four lemmas: @|K-DS-hole|, @|K-DD-hole|, @|K-SS-hole|, and @|K-SD-hole|.
}

@tr-lemma[#:key "K-DS-hole" @elem{@${\langK} static @${\vdyn} hole typing}]{
  If @${\wellKE \ctxE{\edyn{\tau}{e}} : K'} then the derivation contains
   a sub-term @${\wellKE \edyn{\tau}{e} : \tagof{\tau}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-step{
      @${\wellKE \edyn{\tau}{e} : K''}
      @|K-S-hole-typing|
    }
    @tr-step{
      @${\wellKE \edyn{\tau}{e} : \tagof{\tau}}
      @|K-S-inversion| (1)
    }
    @tr-qed{
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \edynfake{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-DD-hole| (2)
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\edyn{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \edyn{\tau_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-DD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\edyn{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \echk{K_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

}

@tr-lemma[#:key "K-DD-hole" @elem{@${\langK} dynamic @${\vdyn} hole typing}]{
  If @${\wellKE \ctxE{\edyn{\tau}{e}}} then the derivation contains
   a sub-term @${\wellKE \edyn{\tau}{e} : \tagof{\tau}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellKE \ctxE{\edyn{\tau}{e}}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\edyn{\tau}{e}}] = \eapp{\esd_0[{\edyn{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\edyn{\tau}{e}}]}
      @|K-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\edyn{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \estafake{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\edyn{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\edyn{\tau}{e}} = \esta{\tau_0}{\esd_0[{\edyn{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\edyn{\tau}{e}}] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\edyn{\tau}{e}}}
    }
  }

}

@tr-lemma[#:key "K-SS-hole" @elem{@${\langK} static @${\vsta} hole typing}]{
  If @${\wellKE \ctxE{\esta{\tau}{e}} : K'} then the derivation contains
   a sub-term @${\wellKE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellKE \ctxE{\esta{\tau}{e}} : \tau'} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \edynfake{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\esta{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \edyn{\tau_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\esta{\tau}{e}} : \tau'}
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \echk{K_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

}

@tr-lemma[#:key "K-SD-hole" @elem{@${\langK} dynamic @${\vsta} hole typing}]{
  If @${\wellKE \ctxE{\esta{\tau}{e}}} then the derivation contains
   a sub-term @${\wellKE \esta{\tau}{e}}.
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{
      by @|K-D-hole-typing|
    }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[{\esta{\tau}{e}}] = \eapp{\esd_0[{\esta{\tau}{e}}]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[{\esta{\tau}{e}}]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[{\esta{\tau}{e}}]}
      @|K-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\esta{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \estafake{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SS-hole| (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\esta{\tau}{e}}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{\esta{\tau}{e}} = \esta{\tau_0}{\esd_0[{\esta{\tau}{e}}]}}
    }
    @tr-step{
      @${\wellKE \esd_0[{\esta{\tau}{e}}] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SS-hole| (2)
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{\esta{\tau}{e}}}
    }
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-S-hole-subst" @elem{@${\langK} static hole substitution}]{
  If @${\wellKE \ebase[{e}] : K}
  and the derivation contains a sub-term @${\wellKE e : K'}
  and @${\wellKE e' : K'},
  then @${\wellKE \ebase[{e'}] : K}
}@tr-proof{
  By induction on the structure of @${\ebase}.

  @tr-case[@${\ebase = \ehole}]{
    @tr-step{
      @${\ebase[{e}] = e
         @tr-and[]
         \ebase[{e'}] = e'}
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

  @tr-case[@${\ebase = \vpair{\ebase_0}{e_1}}]{
    @tr-step{
      @${\ebase[{e}] = \vpair{\ebase_0[e]}{e_1}
        @tr-and[]
        \ebase[{e'}] = \vpair{\ebase_0[e']}{e_1}}
    }
    @tr-step{
      @${\wellKE \vpair{\ebase_0[e]}{e_1} : K}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{\ebase_0[e']}{e_1} : K}
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
      @${\wellKE \vpair{v_0}{\ebase_1[e]} : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ebase_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{v_0}{\ebase_1[e']} : K}
      (2, 3, 4)
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
      @${\wellKE \ebase_0[e]~e_1 : K}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebase_0[e']~e_1 : K}
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
      @${\wellKE v_0~\ebase_1[e] : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ebase_1[e] : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ebase_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE v_0~\ebase_1[e'] : K}
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
      @${\wellKE \eunop{\ebase_0[e]} : K}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0}
      @|K-S-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \eunop{\ebase_0[e']} : K}
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
      @${\wellKE \ebinop{\ebase_0[e]}{e_1} : K}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0
         @tr-and[]
         \wellKE e_1 : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ebase_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{\ebase_0[e']}{e_1} : K}
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
      @${\wellKE \ebinop{v_0}{\ebase_1[e]} : K}
    }
    @tr-step{
      @${\wellKE v_0 : K_0
         @tr-and[]
         \wellKE \ebase_1[e] : K_1}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ebase_1[e'] : K_1}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{v_0}{\ebase_1[e']} : K}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \echk{K_c}{\ebase_0}}]{
    @tr-step{
      @${\ebase[{e}] = \echk{K_c}{\ebase_0[e]}
        @tr-and[]
        \ebase[{e'}] = \echk{K_c}{\ebase_0[e']}}
    }
    @tr-step{
      @${\wellKE \echk{K_c}{\ebase_0[e]} : K}
    }
    @tr-step{
      @${\wellKE \ebase_0[e] : K_0}
      @K-S-inversion
    }
    @tr-step{
      @${\wellKE \ebase_0[e'] : K_0}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \echk{K_c}{\ebase_0[e']} : K}
      (2, 3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "K-D-hole-subst" @elem{@${\langK} dynamic hole substitution}]{
  If @${\wellKE \ebase[{e}]} and @${\wellKE e'} then @${\wellKE \ebase[{e'}]}
}
@tr-proof{
  By induction on the structure of @${\ebase}.

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
      @${\wellKE \vpair{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{\ebase_0[e']}{e_1}}
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
      @${\wellKE \vpair{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \vpair{v_0}{\ebase_1[e']}}
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
      @${\wellKE \ebase_0[e]~e_1}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebase_0[e']~e_1}
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
      @${\wellKE v_0~\ebase_1[e]}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE v_0~\ebase_1[e']}
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
      @${\wellKE \eunop{\ebase_0[e]}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \eunop{\ebase_0[e']}}
      (3, 4)
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
      @${\wellKE \ebinop{\ebase_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \ebase_0[e]
         @tr-and[]
         \wellKE e_1}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_0[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{\ebase_0[e']}{e_1}}
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
      @${\wellKE \ebinop{v_0}{\ebase_1[e]}}
    }
    @tr-step{
      @${\wellKE v_0
         @tr-and[]
         \wellKE \ebase_1[e]}
      @|K-D-inversion|
    }
    @tr-step{
      @${\wellKE \ebase_1[e']}
      @tr-IH (3)
    }
    @tr-step{
      @${\wellKE \ebinop{v_0}{\ebase_1[e']}}
      (3, 4)
    }
    @tr-qed{
      by (1, 5)
    }
  }

  @tr-case[@${\ebase = \echk{K_c}{\ebase_0}}]{
    @tr-contradiction{
      @${\wellKE \ebase[{e}]}
    }
  }

}

@tr-lemma[#:key "K-hole-subst" @elem{@${\langK} hole substitution}]{
  @itemlist[
  @item{
    If @${\wellKE \ctxE{e} : K} and the derivation contains a sub-term
     @${\wellKE e : K'} and @${\wellKE e' : K'} then @${\wellKE \ctxE{e'} : K}.
  }
  @item{
    If @${\wellKE \ctxE{e} : K} and the derivation contains a sub-term
     @${\wellKE e} and @${\wellKE e'} then @${\wellKE \ctxE{e'} : K}.
  }
  @item{
    If @${\wellKE \ctxE{e}} and the derivation contains a sub-term
     @${\wellKE e : K'} and @${\wellKE e' : K'} then @${\wellKE \ctxE{e'}}.
  }
  @item{
    If @${\wellKE \ctxE{e}} and the derivation contains a sub-term
     @${\wellKE e} and @${\wellKE e'} then @${\wellKE \ctxE{e'}}.
  }
  ]
}@tr-proof{
  By the following four lemmas:
   @|K-DS-hole-subst|, @|K-DD-hole-subst|, @|K-SS-hole-subst|, and @|K-SD-hole-subst|.
}


@tr-lemma[#:key "K-DS-hole-subst" @elem{@${\langK} dynamic context static hole substitution}]{
  If @${\wellKE \ctxE{e}}
   and contains @${\wellKE e : K'},
   and furthermore @${\wellKE e' : K'},
   then @${\wellKE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellKE \ctxE{e}} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \estafake{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \kany}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SS-hole-subst| (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SS-hole-subst| (2)
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-contradiction{ @${\wellKE \esd[e]} }
  }

}

@tr-lemma[#:key "K-DD-hole-subst" @elem{@${\langK} dynamic context dynamic hole substitution}]{
  If @${\wellKE \ctxE{e}}
   and contains @${\wellKE e},
   and furthermore @${\wellKE e'},
   then @${\wellKE \ctxE{e'}}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|K-D-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_0[e]}
      @|K-D-inversion|
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
      @${\wellKE \esd_1[e]}
      @|K-D-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \estafake{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \kany}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SD-hole-subst| (2)
    }
  }

  @tr-case[@${\esd = \edyn{\tau''}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e}}
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \esta{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \tagof{\tau_0}}
      @|K-D-inversion|
    }
    @tr-qed{
      by @|K-SD-hole-subst| (2)
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \esd[e]}
    }
  }
}

@tr-lemma[#:key "K-SS-hole-subst" @elem{@${\langK} static context static hole substitution}]{
  If @${\wellKE \ctxE{e} : K}
   and contains @${\wellKE e : K'},
   and furthermore @${\wellKE e' : K'},
   then @${\wellKE \ctxE{e'} : K}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-qed{ by @|K-S-hole-subst| }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edynfake{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e} : K}
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-DS-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e} : K}
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \echk{K_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }
}

@tr-lemma[#:key "K-SD-hole-subst" @elem{@${\langK} static context dynamic hole substitution}]{
  If @${\wellKE \ctxE{e} : K}
   and contains @${\wellKE e},
   and furthermore @${\wellKE e'},
   then @${\wellKE \ctxE{e'} : K}
}@tr-proof{
  By induction on the structure of @${\esd}.

  @tr-case[@${\esd \in \ebase}]{
    @tr-contradiction{ @${\wellKE \ctxE{e} : K} }
  }

  @tr-case[@${\esd = \eapp{\esd_0}{e_1}}]{
    @tr-step{
      @${\esd[e] = \eapp{\esd_0[e]}{e_1}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_0[e] : K_0}
      @|K-S-inversion|
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
      @${\wellKE \esd_1[e] : K_1}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
    }
  }

  @tr-case[@${\esd = \edynfake{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edynfake{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \estafake{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e} : K}
    }
  }

  @tr-case[@${\esd = \edyn{\tau_0}{\esd_0}}]{
    @tr-step{
      @${\ctxE{e} = \edyn{\tau_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e]}
      @|K-S-inversion|
    }
    @tr-qed{
      by @|K-SD-hole| (2)
    }
  }

  @tr-case[@${\esd = \esta{\tau_0}{\esd_0}}]{
    @tr-contradiction{
      @${\wellKE \ctxE{e} : K}
    }
  }

  @tr-case[@${\esd = \echk{K_0}{\esd_0}}]{
    @tr-step{
      @${\esd[e] = \echk{K_0}{\esd_0[e]}}
    }
    @tr-step{
      @${\wellKE \esd_0[e] : \kany}
      @|K-S-inversion|
    }
    @tr-qed{
      by @tr-IH (2)
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
    by the definition of @${\Gamma \wellKE e : \tau}
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
      If @${\wellKE \estafake{e}} then
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
  then @${\wellKE \delta(\vbinop, v_0, v_1) : K}.
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
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
        @tr-qed{
          by @${\wellKE \boundaryerror : K}
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
        @tr-step{
          @${\delta(\vquotient, i_0, i_1) = \boundaryerror}
        }
        @tr-qed{
          by @${\wellKE \boundaryerror : K}
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
@tr-lemma[#:key "K-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellKE v} and @${\delta(\vunop, v) = e} then @${\wellKE e}
    }
    @item{
      If @${\wellKE v_0} and @${\wellKE v_1} and @${\delta(\vbinop, v_0, v_1) = e}
       then @${\wellKE e}
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

  @tr-case[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
    @tr-qed[]
  }
}

@; -----------------------------------------------------------------------------
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
@tr-lemma[#:key "K-subst" @elem{@${\langK} substitution}]{
  @itemlist[
  @item{
    If @${\tann{x}{\tau},\Gamma \wellKE e}
    and @${\wellKE v : \tagof{\tau}}
    then @${\Gamma \wellKE \vsubst{e}{x}{v}}
  }
  @item{
    If @${x,\Gamma \wellKE e}
    and @${\wellKE v}
    then @${\Gamma \wellKE \vsubst{e}{x}{v}}
  }
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellKE e : K}
    and @${\wellKE v : \tagof{\tau_x}}
    then @${\Gamma \wellKE \vsubst{e}{x}{v} : K}
  }
  @item{
    If @${x,\Gamma \wellKE e : K}
    and @${\wellKE v}
    then @${\Gamma \wellKE \vsubst{e}{x}{v} : K}
  }
  ]
}@tr-proof{
  By the following four lemmas:
    @|K-DS-subst|, @|K-DD-subst|, @|K-SS-subst|, and @|K-SD-subst|.
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
                e = \edynfake{e'}
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

  @tr-case[@${e = \estafake{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \estafake{\vsubst{e'}{x}{v}}}
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
      @${\Gamma \wellKE \estafake{(\vsubst{e'}{x}{v})}}
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
                e = \edynfake{e'}
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

  @tr-case[@${e = \estafake{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \estafake{\vsubst{e'}{x}{v}}}
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
      @${\Gamma \wellKE \estafake{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

}

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

  @tr-case[@${e = \edynfake{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edynfake{\vsubst{e'}{x}{v}}}
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
      @${\Gamma \wellKE \edynfake{(\vsubst{e'}{x}{v})} : K}
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
              e = \estafake{e'}}]{
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

  @tr-case[@${e = \edynfake{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \edynfake{\vsubst{e'}{x}{v}}}
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
      @${\Gamma \wellKE \edynfake{(\vsubst{e'}{x}{v})} : K}
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
                e = \estafake{e'}}]{
    @tr-contradiction{@${\Gamma \wellKE e : K}}
  }

}


@; -----------------------------------------------------------------------------
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
  @itemize[
    @item{
      @tr-step[
        @${e \mbox{ is closed under } \Gamma}
        @${\Gamma \wellKE e
           @tr-or[]
           \Gamma \wellKE e : \tau}
      ]
      @tr-qed{}
    }
  ]
}

@tr-lemma[#:key "KM-uec" @elem{unique static evaluation contexts}]{
  If @${\wellM e : \tau} and @${e} is boundary-free then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ebase[{v_0~v_1}]} }
    @item{ @${e = \ebase[{\eunop{v}}]} }
    @item{ @${e = \ebase[{\ebinop{v_0}{v_1}}]} }
    @item{ @${e = \ebase[\eerr]} }
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

  @tr-case[@${e = \vpair{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ebase_0[e_0']}
        @|tr-IH|
      }
      @${\ebase = \vpair{\ebase_0}{e_1}}
      @tr-qed{
        by @${e = \ebase[{e_0'}]}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ebase_1[e_1']}
        @|tr-IH|
      }
      @tr-step{
        @${\ebase = \vpair{e_0}{\ebase_1}}
      }
      @tr-qed{
        by @${e = \ebase[{e_1'}]}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @tr-step{@${\ebase = \ehole}}
      @tr-qed{@${e = \ebase[{\vpair{e_0}{e_1}}]}}
    }
  }

  @tr-case[@${e = \vapp{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ebase_0[e_0']}
        @|tr-IH|
      }
      @tr-step{
        @${\ebase = \vapp{\ebase_0}{e_1}}
      }
      @tr-qed{
        by @${e = \ebase[{e_0'}]}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ebase_1[e_1']}
        @|tr-IH|
      }
      @tr-step{
        @${\ebase = \vapp{e_0}{\ebase_1}}
      }
      @tr-qed{
        by @${e = \ebase[{e_1'}]}
      }
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ebase = \ehole}
      @tr-qed{@${e = \ebase[{\vapp{e_0}{e_1}}]}}
    }
  }

  @tr-case[@${e = \eunop{e_0}} #:itemize? #false]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ebase_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ebase = \eunop{\ebase_0}}
      }
      @tr-qed{
        @${e = \ebase[{e_0'}]}
      }
    }
    @tr-else[@${e_0 \in v}]{
      @${\ebase = \ehole}
      @tr-qed{@${e = \ebase[{\eunop{e_0}}]}}
    }
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}} #:itemize? #f]{
    @tr-if[@${e_0 \not\in v}]{
      @tr-step{
        @${e_0 = \ebase_0[e_0']}
        @tr-IH
      }
      @tr-step{
        @${\ebase = \ebinop{\ebase_0}{e_1}}
      }
      @tr-qed{
        @${e = \ebase[{e_0'}]}
      }
    }
    @tr-if[@${e_0 \in v
              @tr-and[2]
              e_1 \not\in v}]{
      @tr-step{
        @${e_1 = \ebase_1[e_1']}
        @tr-IH
      }
      @tr-step{
        @${\ebase = \ebinop{e_0}{\ebase_1}}
      }
      @tr-qed{@${e = \ebase[{e_1'}]}}
    }
    @tr-else[@${e_0 \in v
                @tr-and[4]
                e_1 \in v}]{
      @${\ebase = \ehole}
      @tr-qed{@${e = \ebase[{\ebinop{e_0}{e_1}}]}}
    }
  }

  @tr-case[@${e = \echk{K'}{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \edynfake{e_0}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \estafake{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \edyn{\tau}{e_0}}]{
    @tr-qed{
      @${e} is boundary-free
    }
  }

  @tr-case[@${e = \esta{\tau}{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \eerr}]{
    @tr-step{
      @${\ebase = \ehole}
    }
    @tr-qed{}
  }

}

@tr-lemma[#:key "KM-S-inversion" @elem{@${\wellM} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellM x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellM e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \vpair{e_0}{e_1} : \tau}
      then @${\Gamma \wellM e_0 : \tau_0}
      and @${\Gamma \wellM e_1 : \tau_1}
      and @${\tpair{\tau_0}{\tau_1} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \eapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellM e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellM e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellM \efst{e} : \tau}
      then @${\Gamma \wellM e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \esnd{e} : \tau}
      then @${\Gamma \wellM e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellM e_0 : \tau_0}
      and @${\Gamma \wellM e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellM \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellM e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellM e : \tau}
  }
}

@tr-lemma[#:key "KM-S-canonical" @elem{canonical forms}]{
  @itemlist[
    @item{
      If @${\wellM v : \tpair{\tau_0}{\tau_1}}
      then @${v \eeq \vpair{v_0}{v_1}}
    }
    @item{
      If @${\wellM v : \tarr{\tau_d}{\tau_c}}
      then @${v \eeq \vlam{\tann{x}{\tau_x}}{e'} @tr-and[] \tau_d \subteq \tau_x}
    }
    @item{
      If @${\wellM v : \tint} then @${v \eeq i}
    }
    @item{
      If @${\wellM v : \tnat}
      then @${v \eeq i} and @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellM e : \tau}
  }
}

@tr-lemma[#:key "KM-subst" @elem{substitution}]{
  If @${\tann{x}{\tau_x},\Gamma \wellM e : \tau},
  and @${e} is boundary-free
  and @${\wellM v : \tau_x}
  then @${\Gamma \wellM \vsubst{e}{x}{v} : \tau}
}@tr-proof{
  By induction on the structure of @${e}.

  @tr-case[@${e = x}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = v}
    }
    @tr-step{
      @${\tau_x = \tau}
    }
    @tr-step{
      @${\Gamma \wellM v : \tau}
      @elem{@|M-weakening|}
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
    @tr-contradiction{
      @${\tann{x}{\tau_x},\Gamma \wellM e : \tau}
    }
  }

  @tr-case[@${e = \vlam{\tann{x}{\tau'}}{e'}}]{
    @tr-qed{
      by @${\vsubst{(\vlam{\tann{x}{\tau'}}{e'})}{x}{v} = \vlam{\tann{x}{\tau'}}{e'}}
    }
  }

  @tr-case[@${e = \vlam{\tann{x'}{\tau'}}{e'}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
    }
    @tr-step{
      @${\tann{x'}{\tau'},x,\Gamma \wellM e'}
      @|M-S-inversion|
    }
    @tr-step{
      @${\tann{x'}{\tau'},\Gamma \wellM \vsubst{e'}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vlam{\tann{x'}{\tau'}}{(\vsubst{e'}{x}{v})}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vpair{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vpair{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \vapp{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \vapp{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \eunop{e_0}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \eunop{\vsubst{e_0}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \eunop{\vsubst{e_0}{x}{v}}}
      (3)
    }
    @tr-qed[]
  }

  @tr-case[@${e = \ebinop{e_0}{e_1}}]{
    @tr-step{
      @${\vsubst{e}{x}{v} = \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
    }
    @tr-step{
      @${x,\Gamma \wellM e_0
         @tr-and[]
         x,\Gamma \wellM e_1}
      @|M-S-inversion|
    }
    @tr-step{
      @${\Gamma \wellM \vsubst{e_0}{x}{v}
         @tr-and[]
         \Gamma \wellM \vsubst{e_1}{x}{v}}
      @elem{@tr-IH (2)}
    }
    @tr-step{
      @${\Gamma \wellM \ebinop{\vsubst{e_0}{x}{v}}{\vsubst{e_1}{x}{v}}}
      (3)
    }
    @tr-qed{}
  }

  @tr-case[@${e = \echk{K'}{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \edynfake{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \estafake{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \edyn{\tau'}{e'}}]{
    @tr-contradiction{ @${e} is boundary-free }
  }

  @tr-case[@${e = \esta{\tau'}{e'}}]{
    @tr-contradiction[@${\wellM e : \tau}]
  }

  @tr-case[@${e = \eerr}]{
    @tr-qed{
      @${\vsubst{\eerr}{x}{v} = \eerr}
    }
  }

}

@tr-lemma[#:key "KM-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellM v} and @${\delta(\vunop, v) = v'} then @${\wellM e'}
    }
    @item{
      If @${\wellM v_0} and @${\wellM v_1} and @${\delta(\vbinop, v_0, v_1) = e'}
       then @${\wellM v'}
    }
  ]
}@tr-proof{

  @tr-case[@${\delta(\vfst, \vpair{v_0}{v_1}) = v_0}]{
    @tr-step{
      @${\wellM v_0}
      @|M-S-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsnd, \vpair{v_0}{v_1}) = v_1}]{
    @tr-step{
      @${\wellM v_1}
      @|M-S-inversion|
    }
    @tr-qed[]
  }

  @tr-case[@${\delta(\vsum, v_0, v_1) = v_0 + v_1}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \floorof{v_0 / v_1}}]{
    @tr-qed[]
  }

  @tr-case[@${\delta(\vquotient, v_0, v_1) = \boundaryerror}]{
    @tr-qed[]
  }
}

@tr-lemma[#:key "KM-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellM e} then @${x,\Gamma \wellM e}
    }
    @item{
      If @${\Gamma \wellM e} then @${\tann{x}{\tau},\Gamma \wellM e}
    }
  ]
}@tr-proof{
  @tr-qed{because @${e} is closed under @${\Gamma}}
}
