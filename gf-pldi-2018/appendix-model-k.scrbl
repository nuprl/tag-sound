#lang gf-pldi-2018

@section{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-embedding.tex" "Tagged Embedding"]
@include-figure*["fig:locally-defensive-completion.tex" "Tagged Completion"]

@|K-SOUNDNESS|
@proof{
  Both @${\wellM e : \tau \carrow e^+} and @${\wellKE e^+ : K} follow from
   @tech[#:key "lemma:completion-soundness"]{@${\carrow}-soundness}.
  The outcomes for @${\rrKEstar} follow from progress and preservation lemmas
   for the @${\wellKE} relation.
}

@lemma[@elem{@${\langK} static progress} #:key "LK-S-progress"]{
  If @${\wellKE e : K} then either @${e} is a value or @${e \ccKS A}.
}
@proof{
  @; TODO better sketch
  Proceed by case analysis on the structure of @${e}.
  The definition of @${\ccKS} lists three ways to step: two by @${\ccKD} and one by @${\liftKS}.

  By the unique evaluation contexts lemma for @${\langK}, there are seven cases to consider.

  @proofcase[@${e = \ctxE{\edyn{\tau}{e'}}}]{
    @proofif[@${e' \in v}]{
      @proofif[@${\mchk{\tagof{\tau}}{e'} = e'}]{
        @proofthen[
          @${e \ccKS \ctxE{e'}}
          @${\ctxE{\edyn{\tau}{e'}} \liftKS \ctxE{e'}}
        ]
      }
      @proofelse[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @proofthen[
          @${e \ccKS \boundaryerror}
          @${\ctxE{\edyn{\tau}{e'}} \liftKS \boundaryerror}
        ]
      }
    }
    @proofelse[@${e' \not\in v}]{
      @proofif[@${e' \ccKD e''}]{
        @proofthen[
          @${e \ccKS \ctxE{\edyn{\tau}{e''}}}
        ]
      }
      @proofelse[@${e' \ccKD A}]{
        @proofthen[
          @${e \ccKS A}
        ]
      }
    }
  }

  @proofcase[@${e = \edyn{\kany}{v}}]{
    Immediate, @${e \rrKS v}.
  }

  @proofcase[@${e = \echk{K}{v}}]{
  }

  @proofcase[@${e = v_0~v_1}]{
  }

  @proofcase[@${e = \eunop{v}}]{
  }

  @proofcase[@${e = \ebinop{v_0}{v_1}}]{
  }

  @proofcase[@${e = v}]{
    Otherwise @${e} is an integer, pair, or function literal.
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
