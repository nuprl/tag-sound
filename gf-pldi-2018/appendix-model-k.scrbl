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

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} static progress} #:key "lemma:LK-S-progress"]{
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
  By @tech{lemma:LK-S-uec} there are seven cases to consider.

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
      @proofby["lemma:LK-D-progress"]

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

  @proofcase[@${e \eeq \ctxE{\edyn{\kany}{e'}}}]{
    @proofif[@${e' \in v}]{
      @proofthen
        @${e \ccKS \ctxE{v}}
      @proofbecause
        @${(\edyn{\kany}{v}) \rrKS v}
    }
    @proofelse[@${e' \not\in v}]{
      @proofby["lemma:LK-D-progress"]

      @proofif[@${e' \ccKD e''}]{
        @proofthen
          @${e \ccKS \ctxE{\edyn{\kany}{e''}}}
      }
      @proofelse[@${e' \ccKD A}]{
        @proofthen
          @${e \ccKS A}
      }
    }
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

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} dynamic progress} #:key "lemma:LK-D-progress"]{
  If @${\wellKE e} then either @${e} is a value or @${e \ccKD A}.}
@proof{
  Proceed by case analysis on the structure of @${e}.
  By @tech{lemma:LK-D-uec} there are seven cases to consider.

  @proofcase[@${e \eeq v}]{
    Immediate
  }

  @proofcase[@${e \eeq \ctxE{\esta{\tau}{e'}}}]{
    @proofif[@${e' \in v}]{
      @proofif[@${\mchk{\tagof{\tau}}{e'} = e'}]{
        @proofthen
          @${e \ccKD \ctxE{e'}}
        @proofbecause
          @${(\esta{\tau}{e'}) \rrKD e'}
      }
      @proofelse[@${\mchk{\tagof{\tau}}{e'} = \boundaryerror}]{
        @proofthen
          @${e \ccKD \boundaryerror}
        @proofbecause
          @${(\esta{\tau}{e'}) \rrKD \boundaryerror}
      }
    }
    @proofelse[@${e' \not\in v}]{
      @proofby["lemma:LK-S-progress"]

      @proofif[@${e' \ccKS e''}]{
        @proofthen
          @${e \ccKD \ctxE{\esta{\tau}{e''}}}
      }
      @proofelse[@${e' \ccKS A}]{
        @proofthen
          @${e \ccKD A}
      }
    }
  }

  @proofcase[@${e \eeq \ctxE{\esta{\kany}{e'}}}]{
    @proofif[@${e' \in v}]{
      @proofthen
        @${e \ccKD \ctxE{e'}}
      @proofbecause
        @${(\esta{\kany}{e'}) \rrKD e'}
    }
    @proofelse[@${e' \not\in v}]{
      @proofby["lemma:LK-S-progress"]

      @proofif[@${e' \ccKS e''}]{
        @proofthen
          @${e \ccKD \ctxE{\esta{\kany}{e''}}}
      }
      @proofelse[@${e' \ccKS A}]{
        @proofthen @${e \ccKD A}
      }
    }
  }

  @proofcase[@${e \eeq \ctxE{\echk{K}{v}}}]{
    @proofif[@${\mchk{K}{v} = v}]{
      @proofthen
        @${e \ccKD \ctxE{v}}
      @proofbecause
        @${(\echk{K}{v}) \rrKD v}
    }
    @proofelse[@${\mchk{K}{v} = \boundaryerror}]{
      @proofthen
        @${e \ccKD \boundaryerror}
      @proofbecause
        @${(\echk{K}{v}) \rrKD \boundaryerror}
    }
  }

  @proofcase[@${e \eeq \ctxE{v_0~v_1}}]{
    @proofif[@${v_0 \eeq \vlam{x}{e_0}}]{
      @proofthen
        @${e \ccKD \ctxE{\vsubst{e_0}{x}{v_1}}}
      @proofbecause
        @${(\vlam{x}{e_0}~v_1) \rrKD \vsubst{e_0}{x}{v_1}}
    }
    @proofif[@${v_0 \eeq \vlam{\tann{x}{\tau_d}}{e_0}}]{
      @proofif[@${\mchk{\tagof{\tau_d}}{v_1} = v_1}]{
        @proofthen
          @${e \ccKD \ctxE{\esta{\kany}{(\vsubst{e_0}{x}{v_1})}}}
        @proofbecause
          @${(\vlam{\tann{x}{\tau_d}}{e_0}~v_1) \rrKD (\esta{\kany}{\vsubst{e_0}{x}{v_1}})}
      }
      @proofelse[@${\mchk{\tagof{\tau_d}}{v_1} = \boundaryerror}]{
        @proofthen
          @${e \ccKD \boundaryerror}
        @proofbecause
          @${(\vlam{\tann{x}{\tau_d}}{e_0}~v_1) \rrKD \boundaryerror}
      }
    }
    @proofelse[@${v_0 \eeq i \mbox{ or } v_0 \eeq \vpair{v}{v'}}]{
      @proofthen
        @${e \ccKD \tagerror}
      @proofbecause
        @${v_0~v_1 \rrKD \tagerror}
    }
  }

  @proofcase[@${e = \ctxE{\eunop{v}}}]{
    @proofif[@${\delta(\vunop, v) = v'}]{
      @proofthen
        @${e \ccKD \ctxE{v'}}
      @proofbecause
        @${(\eunop{v}) \rrKD v'}
    }
    @proofelse[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @proofthen
        @${e \ccKD \tagerror}
      @proofbecause @${(\eunop{v}) \rrKD \tagerror}
    }
  }

  @proofcase[@${e = \ctxE{\ebinop{v_0}{v_1}}}]{
    @proofif[@${\delta(\vbinop, v_0, v_1) = v'}]{
      @proofthen @${e \ccKD \ctxE{v'}}
      @proofbecause @${(\ebinop{v_0}{v_1}) \rrKD v'}
    }
    @proofif[@${\delta(\vbinop, v_0, v_1) = \boundaryerror}]{
      @proofthen @${e \ccKD \boundaryerror}
      @proofbecause @${(\ebinop{v_0}{v_1}) \rrKD \boundaryerror}
    }
    @proofelse[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @proofthen @${e \ccKD \tagerror}
      @proofbecause @${(\ebinop{v_0}{v_1}) \rrKD \tagerror}
    }
  }
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} preservation} #:key "LK-preservation"]{
}
@proof{
  TBA
}


@; -----------------------------------------------------------------------------
@lemma[@elem{@${\carrow}-soundness} #:key "lemma:completion-soundness"]{
  TBA
}
@proof{
  TBA
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} unique static evaluation contexts} #:key "lemma:LK-S-uec"]{
  If @${\wellKE e : K} then either:
}
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\edyn{\tau}{e'}}} }
    @item{ @${e = \ctxE{\edyn{\kany}{e'}}} }
    @item{ @${e = \ctxE{\echk{K}{v}}} }
  ]
@proof{
  By induction on the structure of @${e}.

  @proofcase[@${e = x}]{
    @proofcontradiction[@${\wellKE e : K}]
  }

  @proofcase[@${e = i \mbox{ or }
                e = \vlam{x}{e'} \mbox{ or }
                e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @proofthen @${e} is a value
  }

  @proofcase[@${e = \esta{\tau}{e'} \mbox{ or } e = \esta{\kany}{e'}}]{
    @proofcontradiction[@${\wellKE e : K}]
  }

  @proofcase[@${e = \vpair{e_0}{e_1}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ES_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${E = \vpair{\ES_0}{e_1}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ES_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${E = \vpair{e_0}{\ES_1}}
        }
      ]
      @proofthen @${e = \ctxE{e_1'}}
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofthen @${e} is a value
    }
  }

  @proofcase[@${e = e_0~e_1}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ED_0~e_1}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ED_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${\ED = e_0~\ED_1}
        }
      ]
      @proofthen @${e = \ctxE{e_1'}}
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofitems[@item{ @${\ED = \ehole} }]
      @proofthen @${e = \ctxE{e_0~e_1}}
    }
  }

  @proofcase[@${e = \eunop{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \eunop{\ED_0}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[@item{ @${E = \ehole} }]
      @proofthen @${e = \ctxE{\eunop{e_0}}}
    }
  }

  @proofcase[@${e = \ebinop{e_0}{e_1}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ebinop{\ED_0}{e_1}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ED_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ebinop{e_0}{\ED_1}}
        }
      ]
      @proofthen @${e = \ctxE{e_1'}}
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofitems[ @item{ @${\ED = \ehole} } ]
      @proofthen @${e = \ctxE{\ebinop{e_0}{e_1}}}
    }
  }

  @proofcase[@${e = \edyn{\tau}{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \edyn{\tau}{\ED_0}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[@item{ @${\ED = \ehole} }]
      @proofthen @${e = \ctxE{\edyn{\tau}{e_0}}}
    }
  }

  @proofcase[@${e = \edyn{\kany}{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \edyn{\kany}{\ED_0}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[@item{ @${\ED = \ehole} }]
      @proofthen @${e = \ctxE{\edyn{\kany}{e_0}}}
    }
  }

  @proofcase[@${e = \echk{K}{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \echk{K}{\ED_0}}
        }
      ]
      @proofthen @${e = \ctxE{e_0'}}
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[@item{ @${\ED = \ehole} }]
      @proofthen @${e = \ctxE{\echk{K}{e_0}}}
    }
  }
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} unique dynamic evaluation contexts} #:key "lemma:LK-D-uec"]{
  If @${\wellKE e} then either:
}
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e = \ctxE{v_0~v_1}} }
    @item{ @${e = \ctxE{\eunop{v}}} }
    @item{ @${e = \ctxE{\ebinop{v_0}{v_1}}} }
    @item{ @${e = \ctxE{\esta{\tau}{e'}}} }
    @item{ @${e = \ctxE{\esta{\kany}{e'}}} }
    @item{ @${e = \ctxE{\echk{K}{v}}} }
  ]
@proof{
  By induction on the structure of @${e}.

  @proofcase[@${e = x}]{
    @proofcontradiction[@${\wellKE e}]
  }

  @proofcase[@${e = i \mbox{ or }
                e = \vlam{x}{e'} \mbox{ or }
                e = \vlam{\tann{x}{\tau_d}}{e'}}]{
    @proofqed @${e} is a value
  }

  @proofcase[@${e = \edyn{\tau}{e'} \mbox{ or }
                e = \edyn{\kany}{e'} \mbox{ or }
                e = \echk{K}{e'}}]{
    @proofcontradiction[@${\wellKE e}]
  }

  @proofcase[@${e = \vpair{e_0}{e_1}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ES_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${E = \vpair{\ES_0}{e_1}}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ES_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${E = \vpair{e_0}{\ES_1}}
        }
        @item{
          @proofqed @${e = \ctxE{e_1'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofitems[@item{@proofqed @${e} is a value}]
    }
  }

  @proofcase[@${e = e_0~e_1}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ED_0~e_1}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ED_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${\ED = e_0~\ED_1}
        }
        @item{
          @proofqed @${e = \ctxE{e_1'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofitems[
        @item{ @${\ED = \ehole} }
        @item{ @proofqed @${e = \ctxE{e_0~e_1}} }
      ]
    }
  }

  @proofcase[@${e = \eunop{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \eunop{\ED_0}}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[
        @item{ @${E = \ehole} }
        @item{ @proofqed @${e = \ctxE{\eunop{e_0}}} }
      ]
    }
  }

  @proofcase[@${e = \ebinop{e_0}{e_1}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ebinop{\ED_0}{e_1}}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofif[@${e_0 \in v \mbox{ and } e_1 \not\in v}]{
      @proofitems[
        @item{
          @${e_1 = \ED_1[e_1']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \ebinop{e_0}{\ED_1}}
        }
        @item{
          @proofqed @${e = \ctxE{e_1'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v \mbox{ and } e_1 \in v}]{
      @proofitems[
        @item{ @${\ED = \ehole} }
        @item{ @proofqed @${e = \ctxE{\ebinop{e_0}{e_1}}} }
      ]
    }
  }

  @proofcase[@${e = \esta{\tau}{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \esta{\tau}{\ED_0}}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[
        @item{ @${\ED = \ehole} }
        @item{ @proofqed @${e = \ctxE{\esta{\tau}{e_0}}} }
      ]
    }
  }

  @proofcase[@${e = \esta{\kany}{e_0}}]{
    @proofif[@${e_0 \not\in v}]{
      @proofitems[
        @item{
          @${e_0 = \ED_0[e_0']}
          @proofbyIH[]
        }
        @item{
          @${\ED = \esta{\kany}{\ED_0}}
        }
        @item{
          @proofqed @${e = \ctxE{e_0'}}
        }
      ]
    }
    @proofelse[@${e_0 \in v}]{
      @proofitems[
        @item{ @${\ED = \ehole} }
        @item{
          @proofqed @${e = \ctxE{\esta{\kany}{e_0}}}
        }
      ]
    }
  }
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} static hole typing} #:key "lemma:LK-S-hole-typing"]{
  If @${\wellKE \ctxE{e} : K} then the typing derivation contains a sub-term
   @${\wellKE e : K'} for some @${K'}.
}
@proof{
  By induction on the structure of @${\ED}.

  @proofcase[@${\ED = \ehole}]{
    @proofqed @${\ctxE{e} = e}
  }

  @proofcase[@${\ED = \ED_0~e_1}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ED_0[e]~e_1}
      }
      @item{
        @${\wellKE \ED_0[e] : \kfun}
        @proofby["lemma:LK-S-inversion" @${\wellKE \ED_0[e]~e_1 : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = v_0~\ED_1}]{
    @proofitems[
      @item{
        @${\ctxE{e} = v_0~\ED_1[e]}
      }
      @item{
        @${\wellKE \ED_1[e] : \kany}
        @proofby["lemma:LK-S-inversion" @${\wellKE v_0~\ED_1[e] : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \vpair{\ED_0}{e_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}}
      }
      @item{
        @${\wellKE \ED_0[e] : \kany}
        @proofby["lemma:LK-S-inversion" @${\wellKE \vpair{\ED_0[e]}{e_1} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \vpair{v_0}{\ED_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \vpair{v_0}{\ED_1[e]}}
      }
      @item{
        @${\wellKE \ED_1[e] : \kany}
        @proofby["lemma:LK-S-inversion" @${\wellKE \vpair{v_0}{\ED_1[e]} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \eunop{\ED_0}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \eunop{\ED_0[e]}}
      }
      @item{
        @${\wellKE \ED_0[e] : \kpair}
        @proofby["lemma:LK-S-inversion" @${\wellKE \eunop{\ED_0[e]} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}}
      }
      @item{
        @${\wellKE \ED_0[e] : K_0}
        @proofby["lemma:LK-S-inversion" @${\wellKE \ebinop{\ED_0[e]}{e_1} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}}
      }
      @item{
        @${\wellKE \ED_1[e] : K_1}
        @proofby["lemma:LK-S-inversion" @${\wellKE \ebinop{v_0}{\ED_1[e]} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \echk{K}{\ED_0}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \echk{K}{\ED_0[e]}}
      }
      @item{
        @${\wellKE \ED_0[e] : \kany}
        @proofby["lemma:LK-S-inversion" @${\wellKE \echk{K}{\ED_0[e]} : K}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${\langK} dynamic hole typing} #:key "lemma:LK-D-hole-typing"]{
  If @${\wellKE \ctxE{e}} then the derivation contains a sub-term
   @${\wellKE e}
}
@proof{
  By induction on the structure of @${\ED}.

  @proofcase[@${\ED = \ehole}]{
    @proofqed @${\ctxE{e} = e}
  }

  @proofcase[@${\ED = \ED_0~e_1}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ED_0[e]~e_1}
      }
      @item{
        @${\wellKE \ED_0[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \ED_0[e]~e_1}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = v_0~\ED_1}]{
    @proofitems[
      @item{
        @${\ctxE{e} = v_0~\ED_1[e]}
      }
      @item{
        @${\wellKE \ED_1[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE v_0~\ED_1[e]}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \vpair{\ED_0}{e_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \vpair{\ED_0[e]}{e_1}}
      }
      @item{
        @${\wellKE \ED_0[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \vpair{\ED_0[e]}{e_1}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \vpair{v_0}{\ED_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \vpair{v_0}{\ED_1[e]}}
      }
      @item{
        @${\wellKE \ED_1[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \vpair{v_0}{\ED_1[e]}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \eunop{\ED_0}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \eunop{\ED_0[e]}}
      }
      @item{
        @${\wellKE \ED_0[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \eunop{\ED_0[e]}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \ebinop{\ED_0}{e_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ebinop{\ED_0[e]}{e_1}}
      }
      @item{
        @${\wellKE \ED_0[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \ebinop{\ED_0[e]}{e_1}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \ebinop{v_0}{\ED_1}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \ebinop{v_0}{\ED_1[e]}}
      }
      @item{
        @${\wellKE \ED_1[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \ebinop{v_0}{\ED_1[e]}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }

  @proofcase[@${\ED = \echk{K}{\ED_0}}]{
    @proofitems[
      @item{
        @${\ctxE{e} = \echk{K}{\ED_0[e]}}
      }
      @item{
        @${\wellKE \ED_0[e]}
        @proofby["lemma:LK-D-inversion" @${\wellKE \echk{K}{\ED_0[e]}}]
      }
      @item{
        @proofqed @proofbyIH{2}
      }
    ]
  }
}

@; -----------------------------------------------------------------------------
@lemma[@elem{} #:key "lemma:LK-inversion"]{
}

@; -----------------------------------------------------------------------------
@lemma[@elem{} #:key "lemma:LK-canonical"]{
}

@; -----------------------------------------------------------------------------
@lemma[@elem{} #:key "lemma:LK-Delta-soundness"]{
}

@; -----------------------------------------------------------------------------
@lemma[@elem{@${K \subt K} finite}]{
  All chains @${K_0 \subt \cdots \subt K_n} are finite.
}
@proof{
  By definition.
  The longest chain has three tags: @${\knat \subt \kint \subt \kany}.
}
