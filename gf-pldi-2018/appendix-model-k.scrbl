#lang gf-pldi-2018

@section{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-embedding.tex" "Tagged Embedding"]
@include-figure*["fig:locally-defensive-completion.tex" "Tagged Completion"]

@|K-SOUNDNESS|
@proof{
  Both @${\wellM e : \tau \carrow e^+} and @${\wellKE e^+ : K} follow from
   @tech[#:key "lemma:completion-soundness"]{completion soundness for @${\carrow}}.
  The outcomes for @${\rrKEstar} follow from progress and preservation lemmas
   for the @${\wellKE} relation.
}

@lemma[@elem{@${\langK} static progress} #:key "LK-S-progress"]{
  If @${\wellKE e : K} then either:}
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \ccKS e'} }
    @item{ @${e \ccKS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau}{e'}} \mbox{ and } e' \ccKD \tagerror} }
  ]
@proof{
  @; TODO better sketch
  Proceed by case analysis on the structure of @${e}.
  The definition of @${\ccKS} lists three ways to step:
   two by @${\ccKD} and one by @${\liftKS}.
  By the unique evaluation contexts lemma for @${\langK},
   there are seven cases to consider.

  @proofcase[@${e \eeq v}]{
    immediate
  }
  @proofcase[@${e \eeq \ctxE{\edyn{\tau}{e'}}}]{
    @proofif[@${e' \in v}]{
      @proofif[@${\mchk{\tagof{\tau}}{e'} = e'}]{
        @proofthen
          @${e \ccKS \ctxE{e'}}
        @proofbecause
          @${(\edyn{\tau}{e'}) \rrKS e'}
      }
      @proofelse[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @proofthen
          @${e \ccKS \boundaryerror}
        @proofbecause
          @${(\edyn{\tau}{e'}) \rrKS \boundaryerror}
      }
    }
    @proofelse[@${e' \not\in v}]{
      @proofif[@${e' \ccKD e''}]{
        @proofthen
          @${e \ccKS \ctxE{\edyn{\tau}{e''}}}
      }
      @proofelse[@${e' \ccKD A}]{
        @proofthen
          @${e \ccKS A}
      }
    }
  }

  @proofcase[@${e \eeq \ctxE{\edyn{\kany}{v}}}]{
    @proofthen
      @${e \ccKS \ctxE{v}}
    @proofbecause
      @${(\edyn{\kany}{v}) \rrKS v}
  }

  @proofcase[@${e \eeq \ctxE{\echk{K}{v}}}]{
    @proofif[@${\mchk{K}{v} = v}]{
      @proofthen
      @${e \ccKS \ctxE{v}}
      @proofbecause
      @${(\echk{K}{v}) \rrKS v}
    }
    @proofelse[@${\mchk{K}{v} = \boundaryerror}]{
      @proofthen
      @${e \ccKS \boundaryerror}
      @proofbecause
      @${(\echk{K}{v}) \rrKS \boundaryerror}
    }
  }

  @proofcase[@${e \eeq \ctxE{v_0~v_1}}]{
    @proofitems[
      @item{
        @${\exists K' \mbox{ such that } \wellKE v_0~v_1 : K'}
        @proofby["lemma:LK-hole-typing" @${\wellKE \ctxE{v_0~v_1} : K}]
      }
      @item{
        @${\wellKE v_0 : \kfun}
        @proofby["lemma:LK-inversion" @${\wellKE v_0~v_1 : K'}]
      }
      @item{
        @${v_0 \eeq \vlam{x}{e'}} or @${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}}
        @proofby["lemma:LK-canonical" @${\wellKE v_0 : \kfun}]
      }
    ]
    @proofif[@${v_0 \eeq \vlam{x}{e'}}]{
      @proofthen
        @${e \ccKS \ctxE{\edyn{\kany}{(\vsubst{e'}{x}{v_1})}}}
      @proofbecause
        @${(\vlam{x}{e'}~v_1) \rrKS (\edyn{\kany}{(\vsubst{e'}{x}{v_1})})}
    }
    @proofelse[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e'}}]{
      @proofif[@${\mchk{\tagof{\tau_d}}{v_1} = v_1}]{
        @proofthen
          @${e \ccKS \ctxE{\vsubst{e'}{x}{v_1}}}
        @proofbecause
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \vsubst{e'}{x}{v_1}}
      }
      @proofelse[@${\mchk{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
        @proofthen
          @${e \ccKS \boundaryerror}
        @proofbecause
          @${(\vlam{\tann{x}{\tau_d}}{e'})~v_1 \rrKS \boundaryerror}
      }
    }
  }

  @proofcase[@${e \eeq \ctxE{\eunop{v}}}]{
    @proofitems[
      @item{
        @${\vunop \eeq \vfst} or @${\vunop \eeq \vsnd}
        @proofby["def:LK"]
      }
      @item{
        @${\exists K' \mbox{ such that } \wellKE \eunop{v} : K'}
        @proofby["lemma:LK-hole-typing" @${\wellKE \ctxE{\eunop{v}} : K}]
      }
      @item{
        @${\wellKE v : \kpair}
        @proofby["lemma:LK-inversion" @${\wellKE \eunop{v} : K'}]
      }
      @item{
        @${v \eeq \vpair{v_0}{v_1}}
        @proofby["lemma:LK-canonical" @${\wellKE v : \kpair}]
      }
      @item{
        @${\delta(\vunop, v) = v_i} where @${i \in \{0,1\}}
        @proofby["def:LK"]
      }
    ]
    @proofthen
      @${e \ccKS \ctxE{v_i}}
    @proofbecause
      @${(\eunop{v}) \rrKS v_i}
  }

  @proofcase[@${e \eeq \ctxE{\ebinop{v_0}{v_1}}}]{
    @proofitems[
      @item{
        @${\exists K' \mbox{ such that } \wellKE \ebinop{v_0}{v_1} : K'}
        @proofby["lemma:LK-hole-typing" @${\wellKE \ctxE{\ebinop{v_0}{v_1}} : K}]
      }
      @item{
        @${\exists K_0 K_1 K_2 \mbox{ such that } \wellKE v_0 : K_0
           \mbox{ and } \wellKE v_1 : K_1
           \mbox{ and } \Delta(\vbinop, K_0, K_1) = K_2}
        @proofby["lemma:LK-inversion" @${\wellKE \ebinop{v_0}{v_1} : K'}]
      }
      @item{
        @${\delta(\vbinop, v_0, v_1) = v \mbox{ or } \delta(\vbinop, v_0, v_1) = \boundaryerror}
        @proofby["lemma:Delta-soundness"]
      }
    ]
    @proofif[@${\delta(\vbinop, v_0, v_1) = v}]{
      @proofthen
        @${e \ccKS \ctxE{v}}
      @proofbecause
        @${(\ebinop{v_0}{v_1}) \rrKS v}
    }
    @proofelse[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @proofthen
        @${e \ccKS \boundaryerror}
      @proofbecause
        @${(\ebinop{v_0}{v_1}) \rrKS \boundaryerror}
    }
  }
}

@lemma[@elem{@${\langK} dynamic progress} #:key "LK-D-progress"]{
  If @${\wellKE e} then either @${e} is a value or @${e \ccKD A}.
}
@proof{
  
}

@lemma[@elem{@${\langK} preservation} #:key "LK-preservation"]{
}
@proof{
  TBA
}

@lemma[@elem{@${\carrow}-soundness} #:key "lemma:completion-soundness"]{
  TBA
}
@proof{
  TBA
}


@lemma[@elem{@${K \subt K} finite}]{
  All chains @${K_0 \subt \cdots \subt K_n} are finite.
}
@proof{
  By definition.
  The longest chain has three tags: @${\knat \subt \kint \subt \kany}.
}
