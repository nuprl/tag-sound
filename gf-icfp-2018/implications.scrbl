#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Apples-to-Apples Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]

@; TODO
@; - revisit soundness
@; - contrast with examples
@; - kind-of-mention performance, but do NOT focus, that's for next section
@; - single-language corollaries ... not exactly sure how to weave these in
@; - fill in TODO about what else is in the figure

@; -----------------------------------------------------------------------------

The natural, erasure, and locally-defensive embeddings implement distinct
 reduction relations that provide three different notions of soundness,
 reproduced in @figure-ref{fig:X-soundness}.
At a high level, all three guarantee that reduction is fully-defined for
 well-typed programs.
The natural and locally-defensive embeddings additionally guarantee that typed
 expressions do not raise tag errors.
Only the natural embedding guarantees that well-typed expressions reduce to
 well-typed values.

These three notions of soundness and notions of reduction have subtle consequences
 when it comes to predicting how a program will reduce.
Soundness describes the possible result values, and possible errors that may
 arise.
The notions of reduction describe performance when all goes well.
Here we contrast three broad classes of implications: implications for
 type-based reasoning, implications for mixed-typed programs, and
 implications for fully-typed programs.

@figure["fig:X-soundness" "Soundness" @list[
  @twocolumn[
    @tr-theorem[#:key #false @elem{static @${\mathbf{N}}-soundness}]{
      If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
      @linebreak[]
      of the following holds:
      @itemlist[
        @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
        @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrND \tagerror} }
        @item{ @${e \rrNSstar \boundaryerror} }
        @item{ @${e} diverges}
      ] }

    "example"
  ]

  @twocolumn[
    @tr-theorem[#:key #false @elem{static @${\mathbf{E}}-soundness}]{
      If @${\wellM e : \tau} then @${\wellEE e} and one
      @linebreak[]
      of the following holds:
      @itemlist[
        @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
        @item{ @${e \rrEEstar \tagerror} }
        @item{ @${e \rrEEstar \boundaryerror} }
        @item{ @${e} diverges}
      ] }

    "example"
  ]

  @twocolumn[
    @tr-theorem[#:key #false @elem{static @${\mathbf{K}}-soundness}]{
      If @${\wellM e : \tau} then 
      @${\wellM e : \tau \carrow e''}
      and @${\wellKE e'' : \tagof{\tau}}
      @linebreak[]
      and one of the following holds:
      @itemlist[
        @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
        @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
        @item{ @${e'' \rrKSstar \boundaryerror} }
        @item{ @${e''} diverges }
      ] }

    "example"
  ]
]]


@section{For Type-Based Reasoning}

@section{For Mixed-Typed Programs}

@;The performance overhead of the natural embedding comes from three sources:
@;  checking, indirection, and allocation.
@;By @emph{checking}, we refer to the cost of validating a type-tag and recursively
@; validating the components of a structured value.
@;For example, checking a list structure built from @${N} pair values requires
@; (at least) @${2N} recursive calls.
@;Function monitors add an @emph{indirection} cost.
@;Every call to a monitored function incurs one additional boundary-crossing.
@;If a value repeatedly crosses boundary terms, these type-checking layers
@; can accumulate without bound.@note{In a language with a JIT compiler,
@;  indirection may also affect inlining decisions.
@;  @; TODO does Spenser's work validate this?
@;  }
@;Finally, the @emph{allocation} cost of building a monitor value
@; also adds to the performance overhead.


@section{For Fully-Typed Programs}

@; with no boundaries
@; - natural has no overhead, fully sound
@; - erasure has small overhead, fully sound
@; - LD has overhead, though fully sound


@figure["purely-static" "Purely Static"
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

