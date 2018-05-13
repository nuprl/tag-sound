#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma tr-definition tr-proof tr-and UID++)]
@(void (UID++) (UID++) (UID++) (UID++) (UID++))
@|appendix|
@|pre-clearpage|
@title[#:tag "sec:appendix"]{Appendix}

The performance costs of the natural embedding suggest two alternative approaches
 to migratory typing.
One approach is to address the cost of @emph{checking} values at a boundary
 by delaying the inspection of structured values.
A second is to address the cost of @emph{indirection} by limiting the number of
 monitors a value can accumulate.
This appendix formulates two theories of these approaches, dubbed the
 @emph{co-natural} (@section-ref{sec:conatural-embedding})
 and @emph{forgetful} (@section-ref{sec:forgetful-embedding}) embeddings,
 and compares their logical implications (@section-ref{sec:appendix:implications}).

The co-natural embedding is inspired by work on higher-order contracts@~cite[ff-icfp-2002];
 this embedding carries the idea of delayed first-order checks to an extreme.
The forgetful embedding is inspired by the eponymous approach to space-efficient
 contracts@~cite[g-popl-2015].

@; Technically, the forgetful embedding in @section-ref{sec:forgetful-embedding}
@;  is a forgetful and co-natural embedding.



@; -----------------------------------------------------------------------------
@section[#:tag "sec:conatural-embedding"]{The Co-Natural Embedding}
@include-figure*["fig:conatural-reduction.tex" "Co-Natural Embedding"]
@include-figure*["fig:conatural-preservation.tex" "Property judgments for the co-natural embedding"]

The co-natural embedding (@figure-ref{fig:conatural-reduction}) extends the
 surface syntax with monitors for functions and pairs.
When a dynamically-typed value flows into a typed context, the @${\vfromdynC}
 boundary function checks that the value matches the expected type constructor
 and, unless the value is of base type, wraps the value in a monitor.
Similarly, the @${\vfromstaC} boundary function protects function and
 pair values with a monitor.
The reduction rules in @figure-ref{fig:conatural-reduction} ensure that
 a monitor behaves the same as the encapsulated value in application and
 projection forms.

Soundness for the co-natural embedding states that reduction preserves the
 property outlined in @figure-ref{fig:conatural-preservation}.
For a statically-typed expression, the implication is that if reduction
 ends in a value then the value is well-typed and either a monitor or an
 evaluation syntax (@figure-ref{fig:multi-reduction}) value.

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
]@tr-proof[#:sketch? #true]{
  By progress and preservation lemmas, see the appendix@~cite[gf-tr-2018].
}

@; -----------------------------------------------------------------------------
@section[#:tag "sec:forgetful-embedding"]{The Forgetful Embedding}
@include-figure*["fig:forgetful-reduction.tex" "Forgetful Embedding"]
@include-figure*["fig:forgetful-preservation.tex" "Property judgments for the forgetful embedding"]

The forgetful embedding defined in @figure-ref{fig:forgetful-reduction} prevents a
 value from accumulating more than one monitor.
If a monitored value reaches the @${\vfromdynF} or @${\vfromstaF} boundary
 functions, the function replaces the existing monitor.
Consequently, a monitored function in a statically-typed context may be
 either a dynamically-typed function or statically-typed function.
In the latter case, there is no guarantee that the statically-typed function
 matches the type of its monitor --- if a monitored, typed function is applied
 in a typed context, the context must check the return type.
The @${\echk{\tau}{e}} expression form implements these delayed codomain checks
 with the help of the @${\vfromany} boundary-crossing function.

The application of a monitored, statically-typed function in a dynamically-typed
 context also requires a run-time check.
For example, the value @${\vmonfun{(\tarr{\tnat}{\tnat})}{(\vlam{\tann{x}{\tnat}}{-2})}}
 may be applied to a dynamically-typed argument.
When the inner function (of type @${\tarr{\tnat}{\tint}}) returns, the monitor
 demands a check that the returned value is a natural number.

@; TODO say more

Soundness for the forgetful embedding is superficially similar to that of the
 co-natural and natural embeddings.
TODO

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
]@tr-proof[#:sketch? #true]{
  By progress and preservation lemmas, see the appendix@~cite[gf-tr-2018].
}


@section[#:tag "sec:appendix:implications"]{Implications of Co-Natural and Forgetful}

TBA
