#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma tr-definition tr-proof tr-and UID++)]
@(void (UID++) (UID++) (UID++) (UID++) (UID++))
@|appendix|
@|pre-clearpage|
@title[#:tag "sec:appendix"]{Appendix}

The performance costs of the natural embedding suggest two alternative approaches.
One approach is to address the cost of @emph{checking} values at a boundary
 by delaying the inspection of structured values.
A second is to address the cost of @emph{indirection} by limiting the number of
 monitors a value can accumulate.
This appendix formulates two theories of these approaches,
 @emph{co-natural} (@section-ref{sec:conatural-embedding})
 and @emph{forgetful} (@section-ref{sec:forgetful-embedding}),
 and compares their logical implications (@section-ref{sec:appendix:implications}).

The co-natural approach is inspired by work on higher-order contracts@~cite[ff-icfp-2002]
 and carries the idea of delayed first-order checks to an extreme.
The forgetful approach is inspired by the eponymous approach to space-efficient
 contracts@~cite[g-popl-2015].

@; Technically, the forgetful embedding in @section-ref{sec:forgetful-embedding}
@;  is a forgetful and co-natural embedding.



@; -----------------------------------------------------------------------------
@section[#:tag "sec:conatural-embedding"]{Co-Natural Embedding}
@include-figure*["fig:conatural-reduction.tex" "Co-Natural Embedding"]
@include-figure*["fig:conatural-preservation.tex" "Property judgments for the co-natural embedding"]

The co-natural embedding (@figure-ref{fig:conatural-reduction}) extends the
 surface syntax with monitors for functions and pairs.
When a dynamically-typed value flows into a typed context, the @${\vfromdynC}
 boundary function checks that the value matches the expected type constructor
 and, unless the value is of base type, wraps the value in a monitor.
Similarly, the @${\vfromstaC} boundary function wraps function and pair.
The reduction rules in @figure-ref{fig:conatural-reduction} ensure that
 a monitor behaves the same as the encapsulated value in application and
 projection forms.

Soundness for the co-natural embedding states that reduction preserves the
 property outlined in @figure-ref{fig:conatural-preservation}.
For a statically-typed expression, the implication is that if reduction
 ends in a value then the value is well-typed and either a monitor or a
 well-typed value.
Proofs are in the supplement@~cite[gf-tr-2018].

@twocolumn[
  @tr-theorem[#:key "C-static-soundness" @elem{static @${\langC}-soundness}]{
    If @${\wellM e : \tau} then @${\wellCE e : \tau} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrCSstar v \mbox{ and } \wellCE v : \tau} }
      @item{ @${e \rrCSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrCD \tagerror} }
      @item{ @${e \rrCSstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "C-dynamic-soundness" @elem{dynamic @${\langC}-soundness}]{
    If @${\wellM e} then @${\wellCE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrCDstar v \mbox{ and } \wellCE v} }
      @item{ @${e \rrCDstar \ctxE{e'}} and @${e' \rrCD \tagerror} }
      @item{ @${e \rrCDstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }@;
]


@; -----------------------------------------------------------------------------
@section[#:tag "sec:forgetful-embedding"]{Forgetful Embedding}
@include-figure*["fig:forgetful-reduction.tex" "Forgetful Embedding"]
@include-figure*["fig:forgetful-preservation.tex" "Property judgments for the forgetful embedding"]

The forgetful embedding defined in @figure-ref{fig:forgetful-reduction} prevents a
 value from accumulating more than one monitor.
If a monitored value reaches one of the @${\vfromdynF} or @${\vfromstaF} boundary
 functions, the function replaces the existing monitor.

Consequently, a monitored function in a statically-typed context may be
 either a dynamically-typed function or statically-typed function.
In the latter case, there is no guarantee that the statically-typed function matches
 the type of its monitor; therefore, the context must check the return type.
The @${\echk{\tau}{e}} expression form represents these delayed codomain checks
 and the @${\vfromany} boundary-crossing function implements the checking.
The application of a monitored, statically-typed function in a dynamically-typed
 context similarly requires a codomain check.

Soundness for the forgetful embedding guarantees that reduction is well-defined
 and ends with either a well-typed value, a tag error in dynamically-typed code,
 or a boundary error.
Proofs are in the supplement@~cite[gf-tr-2018].
The manner in which the forgetful approach enforces soundness, however,
 has serious logical implications for type-based reasoning.
The next subsection discusses implications in depth.

@twocolumn[
  @tr-theorem[#:key "F-static-soundness" @elem{static @${\langF}-soundness}]{
    If @${\wellM e : \tau} then @${\wellFE e : \tau} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrFSstar v \mbox{ and } \wellFE v : \tau} }
      @item{ @${e \rrFSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrFD \tagerror} }
      @item{ @${e \rrFSstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "F-dynamic-soundness" @elem{dynamic @${\langF}-soundness}]{
    If @${\wellM e} then @${\wellFE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrFDstar v \mbox{ and } \wellFE v} }
      @item{ @${e \rrFDstar \ctxE{e'}} and @${e' \rrFD \tagerror} }
      @item{ @${e \rrFDstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }@;
]

@section[#:tag "sec:appendix:implications"]{Implications of Co-Natural and Forgetful}

The co-natural approach delays run-time checks until part of the relevant value
 is accessed.
Thus a type error can go undiscovered if it does not affect the particular execution.

@dbend[
  @safe{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrNSstar \boundaryerror
  }
  @warning{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrCSstar 2
  }
]

@exact{\noindent}Unlike the locally-defensive approach, however, co-natural
 can find such errors in untyped contexts as well as typed contexts.

@dbend[
  @safe{
    \wellM \esnd{\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrCDstar \boundaryerror
  }
  @warning{
    \wellM \esnd{\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrKDstar -2
  }
]

Co-natural and forgetful differ in their approach to pairs (or functions)
 that cross multiple boundary terms.
The co-natural approach enforces all boundaries, but the forgetful approach
 enforces only the most recent.
In the following example, a dynamically-typed pair flows in and out of
 statically typed code.
The first type annotation does not match the value and the forgetful approach
 fails to detect the mismatch.

@dbend[
  @safe{
    \wellM \esnd{(\esta{(\tpair{\tint}{\tint})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrCDstar \boundaryerror
  }
  @warning{
    \wellM \esnd{(\esta{(\tpair{\tint}{\tint})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})}} \rrFDstar -2
  }
]

@exact{\noindent}This example also serves to illustrate a difference between
 forgetful and locally-defensive;
 the forgetful approach can detect a type mismatch in dynamically-typed code.

Also unlike the locally-defensive embedding, the run-time checks in the forgetful
 embedding come from boundary terms.
It is possible to hide a type mismatch using subtyping in the locally-defensive
 embedding, but not in the forgetful embedding.

@dbend[
  @safe{
    \wellM \esnd{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrFSstar \boundaryerror
  }
  @warning{
    \wellM \esnd{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{2}{-2}})} : \tpair{\tnat}{\tnat} \rrKSstar -2
  }
]

