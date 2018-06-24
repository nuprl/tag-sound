#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{Co-Natural Embedding}

@section{@${\langC} Definitions}
@exact{\input{fig:conatural-embedding.tex}}

@|clearpage|
@section{@${\langC} Theorems}

@(begin
   (define C-S-soundness @tr-ref[#:key "C-S-soundness"]{static @${\langC}-soundness})
   (define C-D-soundness @tr-ref[#:key "C-S-soundness"]{static @${\langC}-soundness})

   (define C-S-progress @tr-ref[#:key "C-S-progress"]{static progress})
   (define C-D-progress @tr-ref[#:key "C-D-progress"]{dynamic progress})
   (define C-S-preservation @tr-ref[#:key "C-S-preservation"]{static preservation})
   (define C-D-preservation @tr-ref[#:key "C-D-preservation"]{dynamic preservation})

   (define C-S-implies @tr-ref[#:key "C-S-implies"]{static subset})
   (define C-D-implies @tr-ref[#:key "C-D-implies"]{dynamic subset})

   (define C-S-factor @tr-ref[#:key "C-S-factor"]{boundary factoring})
   (define C-D-factor @tr-ref[#:key "C-D-factor"]{boundary factoring})

   (define C-boundary @tr-ref[#:key "C-boundary"]{inner boundary})

   (define C-S-uec @tr-ref[#:key "C-S-uec"]{unique static evaluation contexts})
   (define C-D-uec @tr-ref[#:key "C-D-uec"]{unique dynamic evaluation contexts})

   (define C-S-hole-typing @tr-ref[#:key "C-S-hole-typing"]{static hole typing})
   (define C-D-hole-typing @tr-ref[#:key "C-D-hole-typing"]{dynamic hole typing})

   (define C-boundary-typing @tr-ref[#:key "C-boundary-typing"]{boundary hole typing})

   (define C-hole-subst @tr-ref[#:key "C-hole-subst"]{hole substitution})

   (define C-S-inversion @tr-ref[#:key "C-S-inversion"]{inversion})
   (define C-D-inversion @tr-ref[#:key "C-D-inversion"]{inversion})

   (define C-S-canonical @tr-ref[#:key "C-S-canonical"]{canonical forms})

   (define C-Delta-soundness @tr-ref[#:key "C-Delta-type-soundness"]{@${\Delta} type soundness})
   (define C-delta-preservation @tr-ref[#:key "C-delta-preservation"]{@${\delta} preservation})

   (define C-fromdyn-soundness @tr-ref[#:key "C-fromdyn-soundness"]{@${\vfromdynC} soundness})
   (define C-fromsta-soundness @tr-ref[#:key "C-fromsta-soundness"]{@${\vfromstaC} soundness})

   (define C-subst @tr-ref[#:key "C-subst"]{substitution})

   (define C-weakening @tr-ref[#:key "C-weakening"]{weakening})
)

@tr-theorem[#:key "C-S-soundness" @elem{static @${\langC} soundness}]{
  If @${\wellM e : \tau} then @${\wellCE e : \tau} and one of the following holds:
  @itemlist[
    @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
    @item{ @${e \rrCSstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \rrCD \tagerror} }
    @item{ @${e \rrCSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step[
      @${\wellCE e : \tau}
      @|C-S-implies|
    ]}
    @item{@tr-qed{
      by @|C-S-progress| and @|C-S-preservation|.
    }}
  ]
}

@tr-theorem[#:key "C-D-soundness" @elem{dynamic @${\langC}-soundness}]{
    If @${\wellM e} then @${\wellCE e} and one of the following holds:
    @itemlist[
      @item{ @${e \rrCDstar v \mbox{ and } \wellCE v} }
      @item{ @${e \rrCDstar \ctxE{e'}} and @${e' \rrCD \tagerror} }
      @item{ @${e \rrCDstar \boundaryerror} }
      @item{ @${e} diverges}
    ]
}@tr-proof{
  @itemlist[#:style 'ordered
    @item{@tr-step{
      @${\wellCE e}
      @|C-D-implies|
    }}
    @item{@tr-qed{
      by @|C-D-progress| and @|C-D-preservation|.
    }}
  ]
}

@tr-corollary[#:key "C-pure-static" @elem{@${\langC} static soundness}]{
  If @${\wellM e : \tau} and @${e} is boundary-free, then one of the following holds:
  @itemlist[
    @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
    @item{ @${e \rrCSstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@tr-proof{
  Consequence of the proof for @|C-S-soundness|
}


@|clearpage|
@section{@${\langC} Lemmas}

@tr-lemma[#:key "C-fromdyn-soundness" @elem{@${\vfromdynC} soundness}]{
  If @${\wellCE v} then @${\wellCE \efromdynC{\tau}{v} : \tau}
}@tr-proof{
  @tr-case[@${\efromdynC{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-step{
      @${\wellCE \vmonfun{(\tarr{\tau_d}{\tau_c})}{v} : \tarr{\tau_d}{\tau_c}}
      @${\wellCE v}
    }
    @tr-qed{}
  }

  @tr-case[@${\efromdynC{\tpair{\tau_0}{\tau_1}}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-step{
      @${\wellCE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v} : \tpair{\tau_0}{\tau_1}}
      @${\wellCE v}
    }
    @tr-qed{}
  }

  @tr-case[@${v = i @tr-and[4] \efromdynC{\tint}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${v \in \naturals @tr-and[4] \efromdynC{\tnat}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${\efromdynC{\tau}{v} = \boundaryerror}]{
    @tr-qed{}
  }
}

@tr-lemma[#:key "C-fromsta-soundness" @elem{@${\vfromstaC} soundness}]{
  If @${\wellCE v : \tau} then @${\wellCE \efromstaC{\tau}{v}}
}@tr-proof{
  @tr-case[@${\wellCE v : \tarr{\tau_d}{\tau_c}
              @tr-and[4]
              \efromstaC{\tarr{\tau_d}{\tau_c}}{v} = \vmonfun{(\tarr{\tau_d}{\tau_c})}{v}}]{
    @tr-qed{}
  }

  @tr-case[@${\wellCE v : \tpair{\tau_0}{\tau_1}
              @tr-and[4]
              \efromstaC{\tpair{\tau_0}{\tau_1}}{v} = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v}}]{
    @tr-qed{}
  }

  @tr-case[@${\wellCE v : \tint
              @tr-and[4]
              \efromstaC{\tint}{v} = v}]{
    @tr-qed{}
  }

  @tr-case[@${\wellCE v : \tnat
              @tr-and[4]
              \efromstaC{\tnat}{v} = v}]{
    @tr-qed{}
  }
}

@tr-corollary[#:key "C-S-implies" @elem{@${\langC} static subset}]{
  If @${\Gamma \wellM e : \tau} then @${\Gamma \wellCE e : \tau}.
}@tr-proof{
  Consequence of the proof for the @|holong| @tr-ref[#:key "N-S-implies"]{static subset} lemma; both
   @${\wellCE} and @${\wellNE} have the same typing rules for surface-language
   expressions.
}

@tr-corollary[#:key "C-D-implies" @elem{@${\langC} dynamic subset}]{
  If @${\Gamma \wellM e} then @${\Gamma \wellCE e}.
}@tr-proof{
  Consequence of the proof for the @|holong| @tr-ref[#:key "N-D-implies"]{dynamic subset} lemma.
}

@tr-lemma[#:key "C-S-progress" @elem{@${\langC} static progress}]{
  If @${\wellCE e : \tau} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccCS e'} }
    @item{ @${e \ccCS \boundaryerror} }
    @item{ @${e \eeq \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccCD \tagerror} }
  ]
}@tr-proof{
  By the @|C-S-factor| lemma, there are seven possible cases.

  @tr-case[@elem{@${e} is a value}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[\eapp{v_0}{v_1}]}]{
    @tr-step{
      @${\wellCE \eapp{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v_0 : \tarr{\tau_d}{\tau_c}
         @tr-and[]
         \wellCE v_1 : \tau_d}
      @|C-S-inversion|}
    @tr-step{
      @${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}
         @tr-or[]
         v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}
      @|C-S-canonical|}
    @list[
      @tr-if[@${v_0 \eeq \vlam{\tann{x}{\tau_d'}}{e'}}]{
        @tr-step{
          @${e \ccCS \ebase[{\vsubst{e'}{x}{v_1}}]}
          @${\eapp{v_0}{v_1} \rrCS \vsubst{e'}{x}{v_1}}}
        @tr-qed[]
      }
      @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v_f}}]{
        @tr-step{
          @${e \ccCS \ebase[{\edyn{\tau_c'}{(\eapp{v_f}{(\esta{\tau_d'}{v_1})})}}]}
          @${\eapp{v_0}{v_1} \rrCS \edyn{\tau_c'}{(\eapp{v_f}{(\esta{\tau_d'}{v_1})})}}}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]}]{
    @tr-step{
      @${\wellCE \eunop{v} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v : \tpair{\tau_0}{\tau_1}}
      @|C-S-inversion|}
    @tr-step{
      @${v = \vpair{v_0}{v_1}
         @tr-or[]
         v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
      @|C-S-canonical|}
    @list[
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vfst}]{
        @tr-step{
          @${\delta(\vunop, \vpair{v_0}{v_1}) = v_0}
          definition
        }
        @tr-step{
          @${e \ccCS \ebase[{v_0}]}
          @${\eunop{v} \rrCS v_0}}
        @tr-qed[]
      }
      @tr-if[@${v = \vpair{v_0}{v_1}
                @tr-and[2]
                \vunop = \vsnd}]{
        @tr-step{
          @${\delta(\vunop, \vpair{v_0}{v_1}) = v_1}
          definition
        }
        @tr-step{
          @${e \ccCS \ebase[{v_1}]}
          @${\eunop{v} \rrCS v_1}}
        @tr-qed[]
      }
      @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
                @tr-and[2]
                \vunop = \vfst}]{
        @tr-step{
          @${e \ccCS \ebase[{\edyn{\tau_0}{(\eunop{v'})}}]}
          definition}
        @tr-qed[]
      }
      @tr-else[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
                @tr-and[4]
                \vunop = \vsnd}]{
        @tr-step{
          @${e \ccCS \ebase[{\edyn{\tau_1}{(\eunop{v'})}}]}
          definition}
        @tr-qed[]
      }
    ]
  }

  @tr-case[@${e \eeq \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${\wellCE \ebinop{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''}
      @|C-S-inversion|}
    @tr-step{
      @${\delta(\vbinop, v_0, v_1) = e'}
      @elem{@|C-Delta-soundness| (2)}}
    @tr-step{
      @${\ebinop{v_0}{v_1} \rrCS e'}
      (3)}
    @tr-qed{
      by @${e \ccCS \ebase[e']}
    }
  }

  @tr-case[@elem{@${e \eeq \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccCD e''
         @tr-or[]
         e' \ccCD \boundaryerror
         @tr-or[]
         e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrCD \tagerror
      }
      @|C-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccCS \ctxE{\efromdynC{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccCS e'}
        }
      }
      @tr-if[@${e' \ccCD e''}]{
        @tr-qed{
          @${e \ccCS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccCD \boundaryerror}]{
        @tr-qed{
          @${e \ccCS \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \esd'[{e''}] \mbox{ and } e'' \rrCD \tagerror}]{
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
         e' \in \eerr
         @tr-or[]
         e' \ccCS e''
         @tr-or[]
         e' \ccCS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrCD \tagerror}
      @|C-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccCS \ctxE{\efromstaC{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccCS e'}
        }
      }
      @tr-if[@${e' \ccCS e''}]{
        @tr-qed{
          @${e \ccCS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccCS \boundaryerror}]{
        @tr-qed{
          @${e \ccCS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e'\!\eeq\!\esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrCD\!\tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e \eeq \ctxE{\eerr}}]{
    @tr-qed[@${e \ccCS \eerr}]
  }
}

@tr-lemma[#:key "C-D-progress" @elem{@${\langC} dynamic progress}]{
  If @${\wellCE e} then one of the following holds:
  @itemlist[
    @item{ @${e} is a value }
    @item{ @${e \in \eerr} }
    @item{ @${e \ccCD e'} }
    @item{ @${e \ccCD \boundaryerror} }
    @item{ @${e \ccCD \tagerror} }
  ]
}@tr-proof{
  By the @|C-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-qed[]
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{x}{e'}}]{
      @tr-step{
        @${e \ccCD \ebase[{\vsubst{e'}{x}{v_1}}]}
        @${\eapp{v_0}{v_1} \rrCD \vsubst{e'}{x}{v_1}}}
      @tr-qed[]
    }
    @tr-if[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}}]{
      @tr-step{
        @${e \ccCD \ebase[{\esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}]}
        @${\eapp{v_0}{v_1}
           \rrCD \esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}}
      @tr-qed[]
    }
    @tr-else[@${v_0 \eeq i
                @tr-or[4]
                v_0 \eeq \vpair{v}{v'}}]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${(\eapp{v_0}{v_1}) \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${v \eeq \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vfst}]{
      @tr-step{
        @${e \ccCD \ebase[{\esta{\tau_0}{\eunop{v'}}}]}
        @${\eunop{v} \rrCD \esta{\tau_0}{\eunop{v'}}}}
      @tr-qed[]
    }
    @tr-if[@${v \eeq \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vsnd}]{
      @tr-step{
        @${e \ccCD \ebase[{\esta{\tau_1}{\eunop{v'}}}]}
        @${\eunop{v} \rrCD \esta{\tau_1}{\eunop{v'}}}}
      @tr-qed[]
    }
    @tr-if[@${\delta(\vunop, v) = e'}]{
      @tr-step{
        @${(\eunop{v}) \rrCD e'}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vunop, v) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${(\eunop{v}) \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${\delta(\vbinop, v_0, v_1) = e''}]{
      @tr-step{
        @${\ebinop{v_0}{v_1} \rrCD e''}}
      @tr-qed[]
    }
    @tr-else[@${\delta(\vbinop, v_0, v_1) \mbox{ is undefined}}]{
      @tr-step{
        @${e \ccCD \tagerror}
        @${\ebinop{v_0}{v_1} \rrCD \tagerror}}
      @tr-qed[]
    }
  }

  @tr-case[@elem{@${e = \esd[{\edyn{\tau'}{e'}}]} and @${e'} is boundary-free}]{
    @tr-step{
      @${e' \mbox{ is a value}
         @tr-or[]
         e' \in \eerr
         @tr-or[]
         e' \ccCD e''
         @tr-or[]
         e' \ccCD \boundaryerror
         @tr-or[]
         e' \eeq \ctxE{e''} \mbox{ and } e'' \rrCD \tagerror}
      @|C-D-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccCD \ctxE{\efromdynC{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccCD e'}
        }
      }
      @tr-if[@${e' \ccCD e''}]{
        @tr-qed{
          @${e \ccCS \ctxE{\edyn{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccCD \boundaryerror}]{
        @tr-qed{
          @${e \ccCD \ctxE{\edyn{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e' \eeq \ctxE{e''} \mbox{ and } e'' \rrCD \tagerror}]{
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
         e' \in \eerr
         @tr-or[]
         e' \ccCS e''
         @tr-or[]
         e' \ccCS \boundaryerror
         @tr-or[]
         e' \eeq \esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrCD \tagerror}
      @|C-S-progress|
    }
    @list[
      @tr-if[@${e' \mbox{ is a value}}]{
        @tr-qed{
          @${e \ccCS \ctxE{\efromstaC{\tau'}{e'}}}
        }
      }
      @tr-if[@${e' \in \eerr}]{
        @tr-qed{
          @${e \ccCS e'}
        }
      }
      @tr-if[@${e' \ccCS e''}]{
        @tr-qed{
          @${e \ccCS \ctxE{\esta{\tau'}{e''}}}
        }
      }
      @tr-if[@${e' \ccCS \boundaryerror}]{
        @tr-qed{
          @${e \ccCS \ctxE{\esta{\tau'}{\boundaryerror}}}
        }
      }
      @tr-else[@${e'\!\eeq\!\esd''[{\edyn{\tau''}{\ebase''[e'']}}] \mbox{ and } e'' \rrCD\!\tagerror}]{
        @tr-contradiction{@${e'} is boundary-free}
      }
    ]
  }

  @tr-case[@${e = \esd[\eerr]}]{
    @tr-qed{
      @${e \ccCD \eerr}
    }
  }
}

@tr-lemma[#:key "C-S-preservation" @elem{@${\langC} static preservation}]{
  If @${\wellCE e : \tau} and @${e \ccCS e'} then @${\wellCE e' : \tau}
}@tr-proof{
  By the @|C-S-factor| lemma there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccCS e'}}
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 = \vlam{\tann{x}{\tau_x}}{e'}
              @tr-and[2]
              e \ccCS \ebase[{\vsubst{e'}{x}{v_1}}]}]{
      @tr-step{
        @${\wellCE \eapp{v_0}{v_1} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v_0 : \tarr{\tau_d}{\tau_c}
           @tr-and[]
           \wellCE v_1 : \tau_d
           @tr-and[]
           \tau_c \subteq \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\tau_d \subteq \tau_x}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tann{x}{\tau_x} \wellCE e' : \tau_c}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\wellCE v_1 : \tau_x}
        (2, 3)}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1} : \tau_c}
        @elem{@|C-subst| (4, 5)}}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1} : \tau'}
        (2, 6)}
      @tr-qed{
        by @|C-hole-subst| (7)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}
              @tr-and[4]
              e \ccCS \ebase[{\edyn{\tau_c}{(\eapp{v_f}{(\esta{\tau_d}{v_1})})}}]}]{
      @tr-step{
        @${\wellCE \eapp{v_0}{v_1} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v_0 : \tarr{\tau_d'}{\tau_c'}
           @tr-and[]
           \wellCE v_1 : \tau_d'
           @tr-and[]
           \tau_c' \subteq \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v_f}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tarr{\tau_d}{\tau_c} \subteq \tarr{\tau_d'}{\tau_c'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_d' \subteq \tau_d
           @tr-and[]
           \tau_c \subteq \tau_c'}
        (4)}
      @tr-step{
        @${\wellCE v_1 : \tau_d}
        (2, 5)}
      @tr-step{
        @${\wellCE \esta{\tau_d}{v_1}}
        (6)}
      @tr-step{
        @${\wellCE \eapp{v_f}{(\esta{\tau_d}{v_1})}}
        (3, 7)}
      @tr-step{
        @${\wellCE \edyn{\tau_c}{(\eapp{v_f}{(\esta{\tau_d}{v_1})})} : \tau_c}
        (8)}
      @tr-step{
        @${\wellCE \edyn{\tau_c}{(\eapp{v_f}{(\esta{\tau_d}{v_1})})} : \tau'}
        (2, 5, 9)}
      @tr-qed{
        by @|C-hole-subst| (10)}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCS \ebase[{\edyn{\tau_0}{(\efst{v'})}}]}]{
      @tr-step{
        @${\wellCE \efst{v} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_0' \subt \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v'}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tpair{\tau_0}{\tau_1} \subteq \tpair{\tau_0'}{\tau_1'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_0 \subteq \tau_0'}}
      @tr-step{
        @${\wellCE \efst{v'}}
        (3)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\efst{v'})} : \tau_0}
        (6)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\efst{v'})} : \tau'}
        (2, 5, 7)}
      @tr-qed{
        by @|C-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{\vpair{v_0}{v_1}}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccCS \ebase[{\edyn{\tau_0}{(\esnd{v'})}}]}]{
      @tr-step{
        @${\wellCE \esnd{v} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE v : \tpair{\tau_0'}{\tau_1'}
           @tr-and[]
           \tau_1' \subt \tau'}
        @|C-S-inversion|}
      @tr-step{
        @${\wellCE v'}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\tpair{\tau_0}{\tau_1} \subteq \tpair{\tau_0'}{\tau_1'}}
        @|C-S-canonical| (2)}
      @tr-step{
        @${\tau_1 \subteq \tau_1'}}
      @tr-step{
        @${\wellCE \esnd{v'}}
        (3)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\esnd{v'})} : \tau_0}
        (5)}
      @tr-step{
        @${\wellCE \edyn{\tau_0}{(\esnd{v'})} : \tau'}
        (2, 5, 7)}
      @tr-qed{
        by @|C-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCS \ebase[{v_0}]}]{
      @tr-step{
        @${\wellCE \efst{\vpair{v_0}{v_1}} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_0 \subteq \tau'}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE v_0 : \tau_0}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\wellCE v_0 : \tau'}
        (2, 3)}
      @tr-qed{
        by @|C-hole-subst| (4)}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
                @tr-and[4]
                \vunop = \vsnd
                @tr-and[4]
                e \ccCS \ebase[{v_1}]}]{
      @tr-step{
        @${\wellCE \esnd{\vpair{v_0}{v_1}} : \tau'}
        @|C-S-hole-typing|}
      @tr-step{
        @${\wellCE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}
           @tr-and[]
           \tau_1 \subteq \tau'}
        @|C-S-inversion| (1)}
      @tr-step{
        @${\wellCE v_1 : \tau_1}
        @|C-S-inversion| (2)}
      @tr-step{
        @${\wellCE v_1 : \tau'}
        (2, 3)}
      @tr-qed{
        by @|C-hole-subst| (4)}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${e \ccCS \ebase[{\delta(\vbinop, v_0, v_1)}]}
      @${e \ccCS e'}
    }
    @tr-step{
      @${\wellCE \ebinop{v_0}{v_1} : \tau'}
      @|C-S-hole-typing|}
    @tr-step{
      @${\wellCE v_0 : \tau_0
         @tr-and[]
         \wellCE v_1 : \tau_1
         @tr-and[]
         \Delta(\vbinop, \tau_0, \tau_1) = \tau''
         @tr-and[]
         \tau'' \subteq \tau'}
      @|C-S-inversion| (1)}
    @tr-step{
      @${\wellCE \delta(\vbinop, v_0, v_1) : \tau''}
      @|C-Delta-soundness| (2)}
    @tr-step{
      @${\wellCE \delta(\vbinop, v_0, v_1) : \tau'}
      (2, 3)}
    @tr-qed{
      by @|C-hole-subst| (4)
    }
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccCS \ctxE{\efromdynC{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau'}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e'}
        @|C-S-inversion| (2)
      }
      @tr-step{
        @${\wellCE \efromdynC{\tau'}{e'} : \tau'}
        @|C-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|C-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccCD e''}]{
      @tr-step{
        @${e \ccCS \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau'}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e'}
        @|C-S-inversion| (2)
      }
      @tr-step{
        @${\wellCE e''}
        @|C-D-preservation| (3)
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|C-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #false]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccCS \ctxE{\efromstaC{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion| (2)
      }
      @tr-step{
        @${\wellCE \efromstaC{\tau'}{e'}}
        @|C-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|C-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccCS e''}]{
      @tr-step{
        @${e \ccCS \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion| (2)
      }
      @tr-step{
        @${\wellCE e'' : \tau'}
        @|C-S-preservation| (3)
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|C-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \esd[\eerr]}}]{
    @tr-step{
      @${e \ccCS \eerr}
    }
    @tr-qed{
      by @${\wellCE \eerr : \tau}
    }
  }
}

@tr-lemma[#:key "C-D-preservation" @elem{@${\langC} dynamic preservation}]{
  If @${\wellCE e} and @${e \ccCD e'} then @${\wellCE e'}
}@tr-proof{
  By the @|C-D-factor| lemma, there are seven cases.

  @tr-case[@${e \mbox{ is a value}}]{
    @tr-contradiction{@${e \ccCD e'}}
  }

  @tr-case[@${e = \ebase[{\eapp{v_0}{v_1}}]} #:itemize? #false]{
    @tr-if[@${v_0 \eeq \vlam{x}{e'}
              @tr-and[2]
              e \ccCD \ebase[{\vsubst{e'}{x}{v_1}}]}]{
      @tr-step{
        @${\wellCE \eapp{v_0}{v_1}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v_0
           @tr-and[]
           \wellCE v_1}
        @|C-D-inversion| (1)}
      @tr-step{
        @${x \wellCE e'}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \vsubst{e'}{x}{v_1}}
        @|C-subst| (2, 3)}
      @tr-qed{
        @|C-hole-subst| (4)}
    }
    @tr-else[@${v_0 \eeq \vmonfun{(\tarr{\tau_d}{\tau_c})}{v_f}
                @tr-and[4]
                e \ccCD \ebase[{\esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}]}]{
      @tr-step{
        @${\wellCE \eapp{v_0}{v_1}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v_0
           @tr-and[]
           \wellCE v_1}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_f : \tarr{\tau_d}{\tau_c}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \edyn{\tau_d}{v_1} : \tau_d}
        (2)}
      @tr-step{
        @${\wellCE \eapp{v_f}{(\edyn{\tau_d}{v_1})} : \tau_c}
        (3, 4)}
      @tr-step{
        @${\wellCE \esta{\tau_c}{(\eapp{v_f}{(\edyn{\tau_d}{v_1})})}}
        (5)}
      @tr-qed{
        by @|C-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\eunop{v}}]} #:itemize? #false]{
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCD \ctxE{\esta{\tau_0}{(\efst{v'})}}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v' : \tpair{\tau_0}{\tau_1}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \efst{v'} : \tau_0}
        (3)}
      @tr-step{
        @${\wellCE \esta{\tau_0}{(\efst{v'})}}
        (4)}
      @tr-qed{
        by @|C-hole-subst|}
    }
    @tr-if[@${v = \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccCD \ctxE{\esta{\tau_0}{(\esnd{v'})}}}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE \vmonpair{(\tpair{\tau_0}{\tau_1})}{v'}}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v' : \tpair{\tau_0}{\tau_1}}
        @|C-D-inversion| (2)}
      @tr-step{
        @${\wellCE \esnd{v'} : \tau_1}
        (3)}
      @tr-step{
        @${\wellCE \esta{\tau_1}{(\esnd{v'})}}
        (4)}
      @tr-qed{
        by @|C-hole-subst|}
    }
    @tr-if[@${v = \vpair{v_0}{v_1}
              @tr-and[2]
              \vunop = \vfst
              @tr-and[2]
              e \ccCD \ebase[{v_0}]}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_0}
        @|C-D-inversion| (2)}
      @tr-qed{
        by @|C-hole-subst|}
    }
    @tr-else[@${v = \vpair{v_0}{v_1}
              @tr-and[4]
              \vunop = \vsnd
              @tr-and[4]
              e \ccCD \ebase[{v_1}]}]{
      @tr-step{
        @${\wellCE \eunop{v}}
        @|C-D-hole-typing|}
      @tr-step{
        @${\wellCE v}
        @|C-D-inversion| (1)}
      @tr-step{
        @${\wellCE v_1}
        @|C-D-inversion| (2)}
      @tr-qed{
        by @|C-hole-subst|}
    }
  }

  @tr-case[@${e = \ebase[{\ebinop{v_0}{v_1}}]}]{
    @tr-step{
      @${e \ccCD \ebase[{\delta(\vbinop, v_0, v_1)}]}
    }
    @tr-step{
      @${\wellCE \ebinop{v_0}{v_1}}
      @|C-D-hole-typing|}
    @tr-step{
      @${\wellCE v_0
         @tr-and[]
         \wellCE v_1}
      @|C-D-inversion| (1)}
    @tr-step{
      @${\wellCE {\delta(\vbinop, v_0, v_1)}}
      @|C-delta-preservation| (2)}
    @tr-qed{
      by @|C-hole-subst| (3)}
  }

  @tr-case[@elem{@${e = \ctxE{\edyn{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \mbox{ is a value}}]{
      @tr-step{
        @${e \ccCD \ctxE{\efromdynC{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau'}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e'}
        @|C-S-inversion| (2)
      }
      @tr-step{
        @${\wellCE \efromdynC{\tau'}{e'} : \tau'}
        @|C-fromdyn-soundness| (3)
      }
      @tr-qed{
        by @|C-hole-subst| (4)
      }
    }
    @tr-else[@${e' \ccCD e''}]{
      @tr-step{
        @${e \ccCD \ctxE{\edyn{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e'} : \tau'}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e' 
           @tr-and[]
           \tau' \subteq \tau''}
        @|C-S-inversion| (2)
      }
      @tr-step{
        @${\wellCE e''}
        @|C-D-preservation| (3)
      }
      @tr-step{
        @${\wellCE \edyn{\tau'}{e''} : \tau'}
        (4)
      }
      @tr-qed{
        by @|C-hole-subst| (5)
      }
    }
  }

  @tr-case[@elem{@${e = \ctxE{\esta{\tau'}{e'}}} and @${e'} is boundary-free} #:itemize? #f]{
    @tr-if[@${e' \in v}]{
      @tr-step{
        @${e \ccCD \ctxE{\efromstaC{\tau'}{e'}}}
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion| (2)
      }
      @tr-step{
        @${\wellCE \efromstaC{\tau'}{e'}}
        @|C-fromsta-soundness| (3)
      }
      @tr-qed{
        by @|C-hole-subst| (5)
      }
    }
    @tr-else[@${e' \ccCS e''}]{
      @tr-step{
        @${e \ccCD \ctxE{\esta{\tau'}{e''}}}
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e'}}
        @|C-boundary-typing|
      }
      @tr-step{
        @${\wellCE e' : \tau'}
        @|C-D-inversion| (2)
      }
      @tr-step{
        @${\wellCE e'' : \tau'}
        @|C-S-preservation| (3)
      }
      @tr-step{
        @${\wellCE \esta{\tau'}{e''}}
        (4)
      }
      @tr-qed{
        by @|C-hole-subst| (5)
      }
    }
  }

  @tr-case[@${e = \ctxE{\eerr}}]{
    @tr-step{
      @${e \ccCD \eerr}}
    @tr-qed{
      @${\wellCE \eerr}
    }
  }
}

@tr-lemma[#:key "C-S-factor" @elem{@${\langC} static boundary factoring}]{
  If @${\wellCE e : \tau} then one of the following holds:
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
  By the @tr-ref[#:key "N-S-factor"]{boundary factoring} lemma for the
   @|holong| embedding.
  (The only difference is the meaning of @emph{e is a value}.)
}

@tr-lemma[#:key "C-D-factor" @elem{@${\langC} dynamic boundary factoring}]{
  If @${\wellCE e} then one of the following holds:
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
  By the @tr-ref[#:key "N-D-factor"]{boundary factoring} lemma for the
   @|holong| embedding.
}

@tr-lemma[#:key "C-S-hole-typing" @elem{@${\langC} static hole typing}]{
  If @${\wellCE \ebase[{e}] : \tau} then the derivation
   contains a sub-term @${\wellCE e : \tau'}
}@tr-proof[#:sketch? #true]{
  Similar to the @tr-ref[#:key "N-S-hole-typing"]{static hole typing} lemma for the
   @|holong| embedding.
}

@tr-lemma[#:key "C-D-hole-typing" @elem{@${\langC} dynamic hole typing}]{
  If @${\wellCE \ebase[{e}]} then the derivation contains a sub-term @${\wellCE e}
}@tr-proof[#:sketch? #true]{
  Similar to the @tr-ref[#:key "N-D-hole-typing"]{static hole typing} lemma for the
   @|holong| embedding.
}

@tr-lemma[#:key "C-boundary-typing" @elem{@${\langC} boundary hole typing}]{
  @itemlist[
  @item{
    If @${\wellCE \ctxE{\edyn{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellCE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellCE \ctxE{\edyn{\tau}{e}}} then the derivation contains a
    sub-term @${\wellCE \edyn{\tau}{e} : \tau}
  }
  @item{
    If @${\wellCE \ctxE{\esta{\tau}{e}} : \tau'} then the derivation contains a
    sub-term @${\wellCE \esta{\tau}{e}}
  }
  @item{
    If @${\wellCE \ctxE{\esta{\tau}{e}}} then the derivation contains a
    sub-term @${\wellCE \esta{\tau}{e}}
  }
  ]
}@tr-proof[#:sketch? #true]{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-boundary-typing"]{boundary hole typing} lemma.
}

@tr-lemma[#:key "C-hole-subst" @elem{@${\langC} hole substitution}]{
  @itemlist[
  @item{
    If @${\wellCE \ctxE{e}} and the derivation contains a sub-term
     @${\wellCE e : \tau'} and @${\wellCE e' : \tau'} then @${\wellCE \ctxE{e'}}.
  }
  @item{
    If @${\wellCE \ctxE{e}} and the derivation contains a sub-term
     @${\wellCE e} and @${\wellCE e'} then @${\wellCE \ctxE{e'}}.
  }
  @item{
    If @${\wellCE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellCE e : \tau'} and @${\wellCE e' : \tau'} then @${\wellCE \ctxE{e'} : \tau}.
  }
  @item{
    If @${\wellCE \ctxE{e} : \tau} and the derivation contains a sub-term
     @${\wellCE e} and @${\wellCE e'} then @${\wellCE \ctxE{e'} : \tau}.
  }
  ]
}@tr-proof[#:sketch? #true]{
  Similar to the proof of the @|holong| @tr-ref[#:key "N-hole-subst"]{hole substitution} lemma,
   just replacing @${\wellNE} with @${\wellCE}.
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-S-inversion" @elem{@${\wellCE} static inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellCE x : \tau}
      then @${\tann{x}{\tau'} \in \Gamma}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vlam{\tann{x}{\tau_d'}}{e'} : \tau}
      then @${\tann{x}{\tau_d'},\Gamma \wellCE e' : \tau_c'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vpair{e_0}{e_1} : \tpair{\tau_0}{\tau_1}}
      then @${\Gamma \wellCE e_0 : \tau_0'}
      and @${\Gamma \wellCE e_1 : \tau_1'}
      and @${\tau_0' \subteq \tau_0}
      and @${\tau_1' \subteq \tau_1}
    }
    @item{
      If @${\Gamma \wellCE \vapp{e_0}{e_1} : \tau_c}
      then @${\Gamma \wellCE e_0 : \tarr{\tau_d'}{\tau_c'}}
      and @${\Gamma \wellCE e_1 : \tau_d'}
      and @${\tau_c' \subteq \tau_c}
    }
    @item{
      If @${\Gamma \wellCE \efst{e} : \tau}
      then @${\Gamma \wellCE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vfst, \tpair{\tau_0}{\tau_1}) = \tau_0}
      and @${\tau_0 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \esnd{e} : \tau}
      then @${\Gamma \wellCE e : \tpair{\tau_0}{\tau_1}}
      and @${\Delta(\vsnd, \tpair{\tau_0}{\tau_1}) = \tau_1}
      and @${\tau_1 \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \ebinop{e_0}{e_1} : \tau}
      then @${\Gamma \wellCE e_0 : \tau_0}
      and @${\Gamma \wellCE e_1 : \tau_1}
      and @${\Delta(\vbinop, \tau_0, \tau_1) = \tau'}
      and @${\tau' \subteq \tau}
    }
    @item{
      If @${\Gamma \wellCE \vmonpair{\tpair{\tau_0'}{\tau_1'}}{v'} : \tpair{\tau_0}{\tau_1}}
      then @${\Gamma \wellCE v'}
      and @${\tpair{\tau_0'}{\tau_1'} \subteq \tpair{\tau_0}{\tau_1}}
    }
    @item{
      If @${\Gamma \wellCE \vmonfun{\tarr{\tau_d'}{\tau_c'}}{v'} : \tarr{\tau_d}{\tau_c}}
      then @${\Gamma \wellCE v'}
      and @${\tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellCE \edyn{\tau'}{e'} : \tau}
      then @${\Gamma \wellCE e'}
      and @${\tau' \subteq \tau}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellCE e : \tau}
  }
}

@tr-lemma[#:key "C-D-inversion" @elem{@${\wellCE} dynamic inversion}]{
  @itemlist[
    @item{
      If @${\Gamma \wellCE x}
      then @${x \in \Gamma}
    }
    @item{
      If @${\Gamma \wellCE \vlam{x}{e'}}
      then @${x,\Gamma \wellCE e'}
    }
    @item{
      If @${\Gamma \wellCE \vpair{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \vapp{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \eunop{e_0}}
      then @${\Gamma \wellCE e_0}
    }
    @item{
      If @${\Gamma \wellCE \ebinop{e_0}{e_1}}
      then @${\Gamma \wellCE e_0}
      and @${\Gamma \wellCE e_1}
    }
    @item{
      If @${\Gamma \wellCE \vmonfun{\tarr{\tau_d}{\tau_c}}{v'}}
      then @${\Gamma \wellCE v' : \tarr{\tau_d}{\tau_c}}
    }
    @item{
      If @${\Gamma \wellCE \vmonpair{\tpair{\tau_0}{\tau_1}}{v'}}
      then @${\Gamma \wellCE v' : \tpair{\tau_0}{\tau_1}}
    }
    @item{
      If @${\Gamma \wellCE \esta{\tau'}{e'}}
      then @${\Gamma \wellCE e' : \tau'}
    }
  ]
}@tr-proof{
  @tr-qed{
    by the definition of @${\Gamma \wellCE e}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-S-canonical" @elem{@${\langC} canonical forms}]{
  @itemlist[
    @item{
      If @${\wellCE v : \tpair{\tau_0}{\tau_1}}
      then either:
      @itemlist[
        @item{
          @${v \eeq \vpair{v_0}{v_1}}
        }
        @item{
          or @${v \eeq \vmonpair{(\tpair{\tau_0'}{\tau_1'})}{v'}
                @tr-and[]
                \tpair{\tau_0'}{\tau_1'} \subteq \tpair{\tau_0}{\tau_1}}
        }
      ]
    }
    @item{
      If @${\wellCE v : \tarr{\tau_d}{\tau_c}}
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
      If @${\wellCE v : \tint}
      then @${v \eeq i}
    }
    @item{
      If @${\wellCE v : \tnat}
      then @${v \eeq i} and @${v \in \naturals}
    }
  ]
}@tr-proof{
  @tr-qed{
    by definition of @${\wellCE e : \tau}
  }
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-Delta-type-soundness" @elem{@${\Delta} type soundness}]{
  If @${\wellCE v_0 : \tau_0 \mbox{ and }
        \wellCE v_1 : \tau_1 \mbox{ and }
        \Delta(\vbinop, \tau_0, \tau_1) = \tau}
  then one of the following holds:
  @itemize[
    @item{ @${\delta(\vbinop, v_0, v_1) = v \mbox{ and } \wellCE v : \tau}, or }
    @item{ @${\delta(\vbinop, v_0, v_1) = \boundaryerror } }
  ]
}@tr-proof[#:sketch? #true]{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-Delta-type-soundness"]{@${\Delta} type soundness} lemma.
}

@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-delta-preservation" @elem{@${\delta} preservation}]{
  @itemlist[
    @item{
      If @${\wellCE v} and @${\delta(\vunop, v) = v'} then @${\wellCE v'}
    }
    @item{
      If @${\wellCE v_0} and @${\wellCE v_1} and @${\delta(\vbinop, v_0, v_1) = v'}
       then @${\wellCE v'}
    }
  ]
}@tr-proof[#:sketch? #true]{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-delta-preservation"]{@${\delta} preservation} lemma.
}

@; -----------------------------------------------------------------------------

@tr-lemma[#:key "C-subst" @elem{@${\langC} substitution}]{
  @itemlist[
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellCE e}
    and @${\wellCE v : \tau_x}
    then @${\Gamma \wellCE \vsubst{e}{x}{v}}
  }
  @item{
    If @${x,\Gamma \wellCE e}
    and @${\wellCE v}
    then @${\Gamma \wellCE \vsubst{e}{x}{v}}
  }
  @item{
    If @${\tann{x}{\tau_x},\Gamma \wellCE e : \tau}
    and @${\wellCE v : \tau_x}
    then @${\Gamma \wellCE \vsubst{e}{x}{v} : \tau}
  }
  @item{
    If @${x,\Gamma \wellCE e : \tau}
    and @${\wellCE v}
    then @${\Gamma \wellCE \vsubst{e}{x}{v} : \tau}
  }
  ]
}@tr-proof[#:sketch? #true]{
  Similar to the proof for the @|holong| @tr-ref[#:key "N-subst"]{substitution} lemma.
}


@; -----------------------------------------------------------------------------
@tr-lemma[#:key "C-weakening" @elem{weakening}]{
  @itemize[
    @item{
      If @${\Gamma \wellCE e} then @${x,\Gamma \wellCE e}
    }
    @item{
      If @${\Gamma \wellCE e : \tau} then @${\tann{x}{\tau'},\Gamma \wellCE e : \tau}
    }
  ]
}@tr-proof{
  @tr-qed{because @${e} is closed under @${\Gamma}}
}

