#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Traces}

The following expression reduces differently in each of the five embeddings:

@$|{\begin{array}{l@{~}c@{~~}l}
  \erelprime & \BNFeq & (\eapp{\erelprimefun}{\erelprimearg})
\\\erelprimefun & \BNFeq & \vlam{\tann{x}{\tpair{\tint}{\tnat}}}{\vpair{\efst{x}}{\esnd{x}}}
\\\erelprimearg & \BNFeq & (\edyn{\tpair{\tint}{\tnat}}{}
\\ & & \quad(\esta{\tpair{\tnat}{\tnat}}{}
\\ & & \qquad((\edyn{\tpair{\tnat}{\tnat}}{\vpair{-1}{-2}}))))
\end{array}}|

The function @${\erelprimefun} extracts both components of a typed pair.
The expression @${\erelprimearg} sends a dynamically-typed pair of integers,
 the value @${\vpair{-1}{-2}}, across two @${\vdyn} boundary terms.
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
@figure-ref{fig:relprime-completion} derives a completion of @${\erelprime}, and
@figure-ref{fig:relprime-tagging} gives the typing derivation of the completion.

The completion of @${\erelprime} is the following expression:

@$|{\begin{array}{l@{~}c@{~~}l}
  \erelprime''    & \BNFeq & \echk{\kpair}{(\eapp{\erelprimefun''}{\erelprimearg})}
\\\erelprimefun'' & \BNFeq & \vlam{\tann{x}{\tpair{\tint}{\tnat}}}{}
\\                &        & \quad {\vpair{\echk{\kint}{(\efst{x})}}{\echk{\knat}{(\esnd{x})}}}
\end{array}}|


@exact{\input{fig:relprime-reduction.tex}}

@include-figure*["fig:relprime-typing.tex" @elem{Typing derivation for @${\erelprime = \eapp{\erelprimefun}{\erelprimearg}}}]
@include-figure*["fig:relprime-completion.tex" @elem{Completion of @${\erelprime = \eapp{\erelprimefun}{\erelprimearg}}}]
@include-figure*["fig:relprime-tagging.tex" @elem{Tagging derivation for @${\erelprime'' = \echk{\kpair}{(\eapp{\erelprimefun''}{\erelprimearg})}}}]
