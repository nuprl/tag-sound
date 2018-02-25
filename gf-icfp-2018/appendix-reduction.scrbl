#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Traces}

The following term reduces differently in each of the five embeddings:

@${\begin{array}{l c l}
  \erelprime & \triangleq & ((\vlam{\tann{x}{\tpair{\tint}{\tnat}}}{\vpair{\efst{x}}{\esnd{x}}})
\\ & & \hspace{0.4em}(\edyn{\tpair{\tint}{\tnat}}{}
\\ & & \hspace{1em}(\esta{\tpair{\tnat}{\tnat}}{}
\\ & & \hspace{2em}((\edyn{\tpair{\tnat}{\tnat}}{\vpair{-1}{-2}}))))
\end{array}}

This term sends a dynamically-typed pair of integers, the value @${\vpair{-1}{-2}},
 across two @${\vdyn} boundary terms and extracts both its components.
The first boundary applies the type @${\tpair{\tnat}{\tnat}} and the second
 boundary applies the weaker type @${\tpair{\tint}{\tnat}}.
In short, here is how the embeddings react:
@itemlist[
@item{
  the natural embedding halts at the first boundary term;
}
@item{
  the co-natural embedding halts the first time a component of the pair is
   accessed, due to the monitor created by the first boundary term;
}
@item{
  the forgetful embedding halts at the call to @${\vsnd} due to the monitor
   created by the second boundary term;
}
@item{
  the locally-defensive embedding halts outside the call to @${\vsnd} because
   of a check inserted by the type annotation @${\tann{x}{\tpair{\tint}{\tnat}}}; and
}
@item{
  the erasure embedding reduces to a value.
}
]
Full reduction sequences follow.
Additionally:
@figure-ref{fig:relprime-typing} demonstrates that @${\erelprime} is a well-typed
 surface term,
@figure-ref{fig:relprime-completion} gives the completion of @${\erelprime}, and
@figure-ref{fig:relprime-tagging} gives the typing derivation of the completion of @${\erelprime}.

@exact{\input{fig:relprime-reduction.tex}}

@include-figure*["fig:relprime-typing.tex" @elem{Typing derivation for @${\erelprime}}]
@include-figure*["fig:relprime-completion.tex" @elem{Completion of @${\erelprime}}]
@include-figure*["fig:relprime-tagging.tex" @elem{Tagging derivation of the completion of @${\erelprime}}]
