#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma tr-definition tr-proof tr-and UID++)]
@(void (UID++) (UID++) (UID++) (UID++) (UID++))
@|appendix|
@|pre-clearpage|
@title[#:tag "sec:appendix"]{Appendix}

@exact{\noindent}This appendix presents two alternative higher-order approaches,
 called
 @emph{co-natural}
 and @emph{forgetful},
 and their logical implications.
Co-natural enforces all non-base types with monitors@~cite[fgr-ifl-2007 dtw-pepm-2012].
Forgetful limits each value to at most one monitor@~cite[g-popl-2015].
Full definitions and proofs are in the supplement@~cite[gf-tr-2018].

One might also explore an approach that monitors base values and further delays
 errors@~cite[dtw-pepm-2012].


@; -----------------------------------------------------------------------------
@section[#:tag "sec:conatural-embedding"]{Co-Natural Embedding}

@Figure-ref{fig:conatural-reduction} presents the co-natural embedding.
Its evaluation syntax extends the surface syntax with monitors for functions and pairs.
The @${\vfromdynC} boundary function checks that an untyped value matches the expected
 type constructor and wraps all function and pair values in a monitor.
Likewise, @${\vfromstaC} wraps functions and pairs.
The reduction rules in @figure-ref{fig:conatural-reduction} specify the behavior
 of monitored values.
Soundness for the co-natural embedding states that reduction preserves the
 property in @figure-ref{fig:conatural-preservation}.

@; For a statically-typed expression, the implication is that if reduction
@;  ends in a value then the value is well-typed and either a monitor or a
@;  well-typed value.

@;@exact{\vspace{-2ex}}
@;@twocolumn[
@;  @tr-theorem[#:key "C-static-soundness" @elem{static @${\langC}-soundness}]{
@;    If @${\wellM e : \tau} then @${\wellCE e : \tau} and one
@;    @linebreak[]
@;    of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
@;      @item{ @${e \rrCSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrCD \tagerror} }
@;      @item{ @${e \rrCSstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ] }
@;
@;  @tr-theorem[#:key "C-dynamic-soundness" @elem{dynamic @${\langC}-soundness}]{
@;    If @${\wellM e} then @${\wellCE e} and one
@;    @linebreak[]
@;    of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrCDstar v \mbox{ and } \wellCE v} }
@;      @item{ @${e \rrCDstar \ctxE{e'}} and @${e' \rrCD \tagerror} }
@;      @item{ @${e \rrCDstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ] }@;
@;]


@; -----------------------------------------------------------------------------
@section[#:tag "sec:forgetful-embedding"]{Forgetful Embedding}

The forgetful embedding, defined in @figure-ref{fig:forgetful-reduction}, prevents a
 value from accumulating more than one monitor.
If a monitored value reaches one of the @${\vfromdynF} or @${\vfromstaF} boundary
 functions, the function replaces the existing monitor.
Consequently, a statically-typed function that crosses two type boundaries
 may be wrapped in a monitor with an incompatible type:

@dbend[
  @neutral{
    \wellM \edyn{(\tarr{\tnat}{\tnat})}{(\esta{(\tarr{\tint}{\tint})}{(\vlam{\tann{x}{\tint}}{{-2}})})} \rrFSstar \vmonfun{(\tarr{\tnat}{\tnat})}{(\vlam{\tann{x}{\tint}}{{-2}})}
  }
]

@noindent[]The evaluation syntax therefore includes the @${\echk{\tau}{e}} expression
 to check the result of a monitored, typed function against the type declared
 in its monitor.
Soundness for the forgetful embedding states that reduction preserves the
 property in @figure-ref{fig:forgetful-preservation}.

@;@exact{\vspace{-2ex}}
@;@twocolumn[
@;  @tr-theorem[#:key "F-static-soundness" @elem{static @${\langF}-soundness}]{
@;    If @${\wellM e : \tau} then @${\wellFE e : \tau} and one
@;    @linebreak[]
@;    of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
@;      @item{ @${e \rrFSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrFD \tagerror} }
@;      @item{ @${e \rrFSstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ] }
@;
@;  @tr-theorem[#:key "F-dynamic-soundness" @elem{dynamic @${\langF}-soundness}]{
@;    If @${\wellM e} then @${\wellFE e} and one
@;    @linebreak[]
@;    of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrFDstar v \mbox{ and } \wellFE v} }
@;      @item{ @${e \rrFDstar \ctxE{e'}} and @${e' \rrFD \tagerror} }
@;      @item{ @${e \rrFDstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ] }@;
@;]

@section[#:tag "sec:appendix:implications"]{Implications of Co-Natural and Forgetful}

The co-natural approach delays run-time checks until the relevant part of a value
 is accessed.
Thus a type error can go undiscovered if it does not affect the particular execution:

@dbend[
  @;@safe{
  @;  \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrNSstar \boundaryerror
  @;}
  @warning{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrCSstar 2
  }
]

@exact{\noindent}Unlike the @|folong| approach, however, co-natural
 can find such errors in untyped contexts as well as typed contexts, thus
 preventing the miscalculation demonstrated in @section-ref{sec:implications}:

@dbend[
  @safe{
    \wellM \esnd{(\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})})} \rrCDstar \boundaryerror
  }
  @warning{
    \wellM \esnd{(\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})})} \rrKDstar -2
  }
]

@exact{\noindent}The forgetful approach can also detect errors in untyped contexts:

@dbend[
  @safe{
    \wellM \esnd{(\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})})} \rrFDstar \boundaryerror
  }
]

Co-natural and forgetful differ in their approach to pairs (or functions)
 that cross multiple boundary terms.
In the following example, an untyped pair flows in and out of
 typed code.
The first type annotation does not match the value and the forgetful approach
 fails to detect the mismatch:

@dbend[
  @safe{
    \wellM \esnd{(\esta{(\tpair{\tint}{\tint})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrCDstar \boundaryerror
  }
  @warning{
    \wellM \esnd{(\esta{(\tpair{\tint}{\tint})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrFDstar -2
  }
]

@;@exact{\noindent}This example also serves to illustrate a difference between
@; forgetful and @|folong|; namely,
@; the forgetful approach can detect a type mismatch in dynamically-typed code.

Unlike the @|folong| embedding, the run-time checks in the forgetful
 embedding come from boundary terms, not from the client context:

@dbend[
  @safe{
    \wellM \esnd{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tint \rrFSstar \boundaryerror
  }
  @warning{
    \wellM \esnd{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tint \rrKSstar -2
  }
]

@include-figure*["fig:conatural-reduction.tex" "Co-Natural Embedding"]
@include-figure*["fig:conatural-preservation.tex" "Property judgments for the co-natural embedding"]
@include-figure*["fig:forgetful-reduction.tex" "Forgetful Embedding"]
@include-figure*["fig:forgetful-preservation.tex" "Property judgments for the forgetful embedding"]

@exact{\clearpage}
