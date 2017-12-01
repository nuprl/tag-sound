#lang gf-pldi-2018
@require{techreport.rkt}

@title[#:tag "appendix:preliminaries"]{Preliminaries}


@tr-definition[#:key "divergence" @elem{@${\rastar}-divergence}]{
  An expression @${e} diverges for the reduction relation @${\rastar} if for
   all @${e'} such that @${e\!\rastar\!e'} there exists an @${e''} such that
   @${e'\!\rightarrow\!e''}.
}@|smallskip|

@tr-convention["variable convention"]{
  All @${\lambda}-bound variables in an expression are distinct from one
   another, and from any free variables in the expression.
}@|smallskip|

@tr-lemma["weakening"]{
  If @${\Gamma \vdash e} then @${x,\Gamma \vdash e}
}@|smallskip|

@tr-lemma["permutation"]{
  If @${x,x',\Gamma \vdash e} then @${x',x,\Gamma \vdash e}
}@|smallskip|


@;Need this:
@; TODO find a home for this "bowtie" metafunction
@;@exact|{
@;\begin{flushleft}
@;\fbox{$\DSlift{E}{\rrR}{E'}{\rrRp}$} $= \vtuple{\ccR}{\ccRp}$ where:\\
@;$\begin{array}{l@{~~}c@{~~}l@{~~}l}
@;\ctxE{\edyn{\tau}{e}} & \ccR & \ctxE{\edyn{\tau}{e'}}
@;  & \mbox{if $e \ccRp e'$}
@;\\
@;\ctxE{\edyn{\tau}{e}} & \ccR & A
@;  & \mbox{if $e \ccRp A$ and $A \not\in e'$}
@;\\
@;e & \ccR & A
@;  & \mbox{if $e \cclift{E}{\rrR} A$}
@;\\[1ex]
@;\ctxE{\esta{\tau}{e}} & \ccRp & \ctxE{\esta{\tau}{e'}}
@; & \mbox{if $e \ccR e'$}
@;\\
@;\ctxE{\esta{\tau}{e}} & \ccRp & A
@; & \mbox{if $e \ccR A$ and $A \not\in e'$}
@;\\
@;e & \ccRp & A
@; & \mbox{if $e \cclift{E}{\rrR'} A$}
@;\end{array}$
@;
@;\end{flushleft}
@;}|
