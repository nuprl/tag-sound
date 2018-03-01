#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Apples-to-Apples Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]

@; TODO
@; - introduce / explain soundness
@; - contrast with examples
@; - kind-of-mention performance, but do NOT focus, that's for next section
@; - single-language corollaries ... not exactly sure how to weave these in

@; -----------------------------------------------------------------------------

In summary, main differences between the embeddings are with respect to four characteristics:
@itemlist[#:style 'ordered
@item{
  What kinds of checks does the embedding perform when a value reaches a type boundary?
}
@item{
  When, if ever, does the embedding wrap a value in a monitor?
}
@item{
  If an ill-typed value reaches a type boundary, when does the embedding signal an error?
}
@item{
  How do types affect behavior?
}
]

@parag{Natural embedding}
@itemlist[#:style 'ordered
@item{
  recursively check read-only values;
}
@item{
  monitor functional and mutable values;
}
@item{
  detect boundary errors as early as possible;
}
@item{
  types globally constrain behavior.
}
]

@parag{Co-Natural embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  monitor all data structures and functions;
}
@item{
  detect boundary errors as late as possible; *
}
@item{
  types globally constrain behavior
}
]

@parag{Forgetful embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  apply at most one monitor to each value;
}
@item{
  detect boundary errors as late as possible;
}
@item{
  types locally constrain behavior.
}
]

@parag{Locally-Defensive embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  never allocate a monitor;
}
@item{
  detect boundary errors as late as possible;
}
@item{
  types locally constrain behavior.
}
]

@parag{Erasure embedding}
@itemlist[#:style 'ordered
@item{
  never check values;
}
@item{
  never allocate a monitor;
}
@item{
  never detect a type boundary error;
}
@item{
  types do not affect behavior
}
]



@figure["all-soundness" "Soundness"
  @nested[#:style "TwoColumn"]{
    @tr-theorem[#:key "N-soundness" @elem{@${\mathbf{N}}-soundness}]{
      If @${\wellM e : \tau} then @${\wellNE e : \tau}
      @linebreak[]
      and one of the following holds:
      @itemlist[
        @item{ @${e \rrNEstar v \mbox{ and } \wellNE v : \tau} }
        @item{ @${e \rrNEstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccND \tagerror} }
        @item{ @${e \rrNEstar \boundaryerror} }
        @item{ @${e} diverges}
      ] }
    @exact|{
      \multicolsbreak \begin{flushleft} $\begin{array}{l@{~~}l@{~}l}
         \erelprime & \rrNEstar & \erelprimefun~\ES[\vpair{\edyn{\tnat}{{-1}}}{\edyn{\tnat}{{-2}}}]
        \\          & \rrNEstar & \boundaryerror
        \\\multicolumn{3}{l}{\mbox{where } \ES = \edyn{\tpair{\tint}{\tnat}}{(\esta{\tpair{\tnat}{\tnat}}{[]})}}
        \end{array}$ \end{flushleft}}|
  }

  @nested[#:style "TwoColumn"]{
    @tr-theorem[#:key "C-soundness" @elem{@${\mathbf{C}}-soundness}]{
      If @${\wellM e : \tau} then @${\wellCE e : \tau}
      @linebreak[]
      and one of the following holds:
      @itemlist[
        @item{ @${e \rrCEstar v \mbox{ and } \wellCE v : \tau} }
        @item{ @${e \rrCEstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccCD \tagerror} }
        @item{ @${e \rrCEstar \boundaryerror} }
        @item{ @${e} diverges}
      ] }
    @exact|{
      \multicolsbreak \begin{flushleft} $\begin{array}{l@{~~}l@{~}l}
          \erelprime & \rrCEstar & \erelprimefun~v_{m}
        %\\ & \rrCEstar & \vpair{\ES[\edyn{\tnat}{(\efst{\vpair{-1}{-2}})}]}{\esnd{v_{m}}}
        \\ & \rrCEstar & \vpair{\ES[\edyn{\tnat}{{-1}}]}{\esnd{v_{m}}}
        \\ & \rrCEstar & \boundaryerror
        \\\multicolumn{3}{l}{\mbox{where } v_{m} = (\vmonpair{\tpair{\tint}{\tnat}}{}}
        \\\multicolumn{3}{l}{\qquad\qquad\qquad\! (\vmonpair{\tpair{\tnat}{\tnat}}{}}
        \\\multicolumn{3}{l}{\qquad\qquad\qquad\,\, (\vmonpair{\tpair{\tnat}{\tnat}}{\vpair{-1}{-2}})))}
        \\\multicolumn{3}{l}{\mbox{and } \ES = \edyn{\tint}{(\esta{\tnat}{[]})}}
        \end{array}$ \end{flushleft}}|
  }

  @nested[#:style "TwoColumn"]{
    @tr-theorem[#:key "F-soundness" @elem{@${\mathbf{F}}-soundness}]{
      If @${\wellM e : \tau} then @${\wellFE e : \tau}
      @linebreak[]
      and one of the following holds:
      @itemlist[
        @item{ @${e \rrFEstar v \mbox{ and } \wellFE v : \tau} }
        @item{ @${e \rrFEstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccFD \tagerror} }
        @item{ @${e \rrFEstar \boundaryerror} }
        @item{ @${e} diverges}
      ] }
    @exact|{
      \multicolsbreak \begin{flushleft} $\begin{array}{l@{~~}l@{~}l}
          \erelprime & \rrFEstar & \erelprimefun~v_{m}
        \\ & \rrFEstar & \vpair{{-1}}{\esnd{v_{m}}}
        %\\ & \rrFEstar & \vpair{{-1}}{\edyn{\tnat}{(\esnd{\vpair{-1}{-2}})}}
        \\ & \rrFEstar & \vpair{{-1}}{\edyn{\tnat}{{-2}}}
        \\ & \rrFEstar & \boundaryerror
        \\\multicolumn{3}{l}{\mbox{where } v_{m} = \vmonpair{\tpair{\tint}{\tnat}}{\vpair{-1}{-2}}}
        \end{array}$ \end{flushleft}}|
  }

  @nested[#:style "TwoColumn"]{
    @tr-theorem[#:key "K-soundness" @elem{@${\mathbf{K}}-soundness}]{
      If @${\wellM e : \tau}
       and @${\tagof{\tau} = K}, then
       @${\wellM e : \tau \carrow e''}
       @linebreak[]
       and @${\wellKE e'' : K}
       and one of the following holds:
    @itemlist[
      @item{ @${e'' \rrKEstar v} and @${\wellKE v : K} }
      @item{ @${e'' \rrKEstar \ctxE{\edyn{\tau'}{e'}} \mbox{ and } e' \ccKD \tagerror} }
      @item{ @${e'' \rrKEstar \boundaryerror} }
      @item{ @${e''} diverges }
    ] }
  @exact|{
    \multicolsbreak \begin{flushleft} $\begin{array}{l@{~~}l@{~}l}
      \erelprime'' & \rrKEstar & \erelprimefun''~\vpair{-1}{-2}
    %\\   & \rrKEstar & \ES[\langle{\echk{\tint}{(\efst{\vpair{-1}{-2}})}}
    %\\   &           & \quad ,\,{\echk{\tnat}{(\vsnd{\vpair{-1}{-2}})}}\rangle]
    \\   & \rrKEstar & \ES[\vpair{{-1}}{\echk{\tnat}{(\vsnd{\vpair{-1}{\!-2}})}}]
    \\   & \rrKEstar & \ES[\vpair{{-1}}{\echk{\tnat}{{-2}}}]
    \\   & \rrKEstar & \boundaryerror
    \\\multicolumn{3}{l}{\mbox{where } \erelprime : \tpair{\tint}{\tnat} \carrow \erelprime''}
    \\\multicolumn{3}{l}{\mbox{and } \erelprime'' = \erelprimefun''~\erelprimearg}
    %\\\multicolumn{3}{l}{\mbox{and } \erelprimefun'' = \vlam{\tann{x}{\tpair{\tint}{\tnat}}}{\vpair{\echk{\kint}{(\efst{x})}}{\echk{\knat}{(\esnd{x})}}}}
    \\\multicolumn{3}{l}{\mbox{and } \ES = \echk{\kpair}{[]}}
    \end{array}$ \end{flushleft}}|
  }

  @nested[#:style "TwoColumn"]{
    @tr-theorem[#:key "E-soundness" @elem{@${\mathbf{E}}-soundness}]{
      If @${\wellM e : \tau}
       then @${\wellEE e}
       @linebreak[]
       and one of the following holds:
      @itemlist[
        @item{ @${e \rrEEstar v} and @${\wellEE v} }
        @item{ @${e \rrEEstar \tagerror} }
        @item{ @${e \rrEEstar \boundaryerror} }
        @item{ @${e} diverges }
      ] }
  @exact|{
    \multicolsbreak \begin{flushleft} $\begin{array}{l@{~~}l@{~}l}
      \erelprime & \rrEEstar & \erelprimefun~\vpair{-1}{-2}
    %\\        & \rrEEstar & \vpair{\efst{\vpair{-1}{-2}}}{\esnd{\vpair{-1}{-2}}}
    \\        & \rrEEstar & \vpair{-1}{\esnd{\vpair{-1}{-2}}}
    \\        & \rrEEstar & \vpair{-1}{-2}
    \end{array}$ \end{flushleft}}|
  }
]

@figure["all-corollary" "Corollaries"
@tr-theorem[#:key "K-pure-static" @elem{@${\langK} static soundness}]{
  If @${\wellM e : \tau} and @${e} does not contain a sub-term of the form
   @${(\edyn{\tau'}{e'})} then one of the following holds:
  @itemlist[
    @item{ @${e \rrKEstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrKEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}

@tr-theorem[#:key "E-pure-static" @elem{@${\langE} static soundness}]{
  If @${\wellM e : \tau} and @${e} does not contain a sub-term of the form
   @${(\edyn{\tau'}{e'})} then one of the following holds:
  @itemlist[
    @item{ @${e \rrEEstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrEEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}
]

