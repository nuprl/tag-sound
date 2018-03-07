#lang gf-icfp-2018
@|appendix|
@|pre-clearpage|
@title[#:tag "sec:appendix"]{Appendix}

@; -----------------------------------------------------------------------------
@section{The Co-Natural Embedding}
@include-figure*["fig:conatural-reduction.tex" "Co-Natural Embedding"]
@include-figure*["fig:conatural-preservation.tex" "Property judgments for the co-natural embedding"]

The natural embedding eagerly checks values that cross a type boundary.
For most values, this means that a successful boundary-crossing requires
 a linear-time traversal of the value's components.
The exception to this linear-cost rule is the function type.
To check that a dynamically-typed value matches a function type,
 the natural embedding performs a type-tag check and allocates a monitor.

In principle, an embedding can apply the same delayed-checking strategy to values
 of every non-base type.
This reduces the cost of all boundary terms to at most
 one type-tag check and one monitor application.

@Figure-ref{fig:conatural-delta} specifies the details of this @emph{co-natural}
 embedding as an extension of the natural embedding.
@(let ((value-forms '("integers" "pairs" "functions" "function monitors" "pair monitors")))
  @elem{
    In total, this language @${\langL} has @integer->word[@length[value-forms]]
     kinds of values: @authors*[value-forms]. })
The reduction rules define how the projections @${\vfst} and @${\vsnd}
 act on pair monitors.
Finally when a pair value crosses a boundary, it gets wrapped in a checking
 (or protective) monitor.

From a theoretical standpoint, the change from a natural to a co-natural embedding
 delays error-checking until just before an expression would reach an undefined
 state.
The co-natural embedding is still type sound in the same sense as the natural embedding:


@theorem[@elem{@${\langC} type soundness}]{
  If @${\wellM e : \tau} then @${\wellCE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrCEstar v \mbox{ and } \wellCE v : \tau} }
    @item{ @${e \rrCEstar \ctxE{e'} \mbox{ and } e' \ccCD \tagerror} }
    @item{ @${e \rrCEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@;
@proof-sketch{ Similar to the natural embedding. }
@; TODO actual link to appendix

There are expressions, however, that reduce to an error in the natural embedding
 and reduce to a value in the co-natural embedding; for instance
 @${(\vfst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{6}{-1}})})}.

The switch from eager to delayed run-time checks also affects performance.
Instead of checking the contents of a pair exactly once, at a boundary, the
 co-natural embedding described in @figure-ref{fig:conatural-delta} performs
 a check for each application of @${\vfst} or @${\vsnd}.
An implementation might improve this performance through caching, but its
 performance will likely be close to that of the natural embedding.
@;@citet[fgr-ifl-2007] have explored one method for dynamically reducing this cost.
@; ... for our purposes we just care about O(n) -> O(1) ???


@; -----------------------------------------------------------------------------
@section{The Forgetful Embedding}
@include-figure*["fig:forgetful-reduction.tex" "Forgetful Embedding"]
@include-figure*["fig:forgetful-preservation.tex" "Property judgments for the forgetful embedding"]

@; === INTERLUDE
@; - need to know typed functions under a monitor "have a typing"
@; - because functions are delayed computations
@; - and need to know that after substitution, they will compute _some result_ safely
@;   (doesn't matter what the result it, just need to get there safely)
@; ...
@; - monitor annotations allowed to diverge because
@;   Importing module doesn't know origin of value (looks untyped to me)

The second source of performance overhead in the natural embedding is the
 indirection cost of monitors.
Each time a function value crosses a boundary, it accumulates a new monitor.
Repeated crossings means function calls must penetrate several layers of indirection.
To reduce this cost, we need a way to collapse layers of monitors.

A simple, efficient, and type-sound way to reduce the indirection cost
 is to forget all but the most-recently-applied monitor@~cite[g-popl-2015].
When a boundary expecting type @${\tau} finds a value of the form
 @${(\vmon{\tau'}{v})}, drop the @${\tau'} monitor and return @${(\vmon{\tau}{v})}.
After all, if a function @${(\vlam{\tann{x}{\tau}}{e})} is well-typed,
 then the function body @${e} cannot depend on any properties of the old
 type @${\tau'} for soundness.

@Figure-ref{fig:forgetful-delta} presents a forgetful, final embedding that
 combines the co-natural and forgetful monitoring strategies.
Intuitively, the only difference between the forgetful language @${\langF}
 and the language in @figure-ref{fig:conatural-delta}
 is that @${\langF} prevents monitors from stacking up.
The details in @figure-ref{fig:forgetful-delta} address the fact that monitors
 in @${\langF} no longer have a one-to-one correspondence with the type boundaries
 that a value has crossed.
In particular, if the value @${(\vmon{\tau}{v})} is in a dynamically-typed
 context, then @${v} is @emph{not} necessarily a statically-typed value.
@; TODO technically application should be "check type, substitute if OK",
@;      its not right to just substitute
We address this potential confusion in two steps.
First, when the evaluator applies a function monitor to an argument, it
 checks whether the call is crossing a type boundary.
If so, it interposes a @${\vdyn} or @${\vsta} boundary.
Second, the boundaries @${(\esta{\tau}{v})} and @${(\edyn{\tau}{v})}
 perform identical checks.
The @${\mchk{\tau}{\cdot}} meta-function factors out the common work of checking
 a value and dropping any existing monitor.

The language @${\langF} satisfies the same notion of soundness as the co-natural @${\langC}
 and the natural @${\langN}:

@theorem[@elem{@${\langF} type soundness}]{
  If @${\wellM e : \tau} then @${\wellFE e : \tau} and either:
  @itemlist[
    @item{ @${e \rrFEstar v \mbox{ and } \wellFE v : \tau} }
    @item{ @${e \rrFEstar \ctxE{e'} \mbox{ and } e' \ccFD \tagerror} }
    @item{ @${e \rrFEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}@;
@proof-sketch{
  By progress and preservation of the @${\wellFE \cdot : \tau} relation.
  The key invariant is that if @${x} is a variable of type
   @${\tau}, then the forgetful semantics ensures that the value substituted
   for @${x} has the expected type.
  This value may be different from the value substituted by the natural semantics,
   but that distinction is not important for proving type soundness.
}

The forgetful embedding performs just enough run-time type checking to
 ensure that statically-typed code does not reach an undefined state, nothing more.
@; TODO example

@;In short, the combination of monitor values and forgetful semantics
@; takes the compositional reasoning property out of the static type system.


@subsection{WHY DOUBLE CHECK}

The notion of reduction @${\rrFD} has a strange rule for applying a monitored,
 typed function in an untyped context:

@exact|{\[\begin{array}{l@{~~}c@{~}l}
  \eapp{(\vmonfun{(\tarr{\tau_d}{\tau_c})}{(\vlam{\tann{x}{\tau}}{\!e})})}{v}
  & \rrFD & \esta{\tau_c}{e'}
  \\ \sidecond{if $\mchk{\tau}{v} = v'$}
  \\ \sidecond{and $e' = \echk{\tau_c}{\vsubst{e}{x}{v'}$}}
\end{array}\]}|

The result expression checks @${\tau_c} twice.
This double-check is nonsense, but makes sense in the context of our typing
 rules and the established meaning of the @${\vsta} boundary term.
Here is the same rule in terms of typing:


@exact|{\begin{mathpar}
  \inferrule*{
    \inferrule*{
      \inferrule*{
        \inferrule*{
          \vdots_1
        }{
          \tann{x}{\tau} \wellFE e : \tau'
        }
      }{
        \wellFE \vlam{\tann{x}{\tau}}{e} : \tarr{\tau}{\tau'}
      }
    }{
      \wellFE \vmonfun{\tarr{\tau_d}{\tau_c}}{\vlam{\tann{x}{\tau}}{e}}
    }
    \\
    \inferrule*{
      \vdots_2
    }{
      \wellFE v
    }
  }{
    \wellFE \eapp{(\vmonfun{\tarr{\tau_d}{\tau_c}}{(\vlam{\tann{x}{\tau}}{e})})}{v}
  }

  \inferrule*{
    \inferrule*{
      \inferrule*{
        \vdots_{1,2}
      }{
        \wellFE \vsubst{e}{x}{v} : \tau'
      }
    }{
      \wellFE \echk{\tau_c}{\vsubst{e}{x}{v}} : \tau_c
    }
  }{
    \wellFE \esta{\tau_c}{\echk{\tau_c}{\vsubst{e}{x}{v}}}
  }
\end{mathpar}|

A good compiler will remove the extra check, which we keep just for the proof.

