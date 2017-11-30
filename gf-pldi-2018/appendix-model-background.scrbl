#lang gf-pldi-2018
@require{techreport.rkt}

@title[#:tag "appendix:preliminaries"]{Preliminaries}

@definition[@elem{@${R}-divergence}]{
  An expression @${e} diverges for the reduction relation @${R} if for
   all @${e'} such that @${e~R~e'} there exists an @${e''} such that
   @${e'~R~e''}.
}

When @${R} is clear from the context, we will just say ``@${e} diverges''.

@;Barendregt's variable convention@~cite[b-lambda-1981]:

@convention["variables"]{
  All @${\lambda}-bound variables in an expression are distinct from one
   another, and from any free variables in the expression.
}

Implies weakening lemmas.

Permutation lemmas?

  @;  @lemma[@elem{@${\langK} weakening} #:key "lemma:LK-weakening"]{
  @;  }
  @;    @itemlist[
  @;      @item{
  @;        If @${\Gamma \wellKE e : K}
  @;         and @${\not\exists \tau} such that @${\tann{x}{\tau} \in \Gamma}
  @;         then @${\tann{x}{\tau},\Gamma \wellKE e : K} for any type @${\tau}
  @;      }
  @;      @item{
  @;        If @${\Gamma \wellKE e : K}
  @;         and @${x \not\in \Gamma}
  @;         then @${x,\Gamma \wellKE e : K}.
  @;      }
  @;      @item{
  @;        If @${\Gamma \wellKE e}
  @;         and @${\not\exists \tau} such that @${\tann{x}{\tau} \in \Gamma}
  @;         then @${\tann{x}{\tau},\Gamma \wellKE e} for any type @${\tau}
  @;      }
  @;      @item{
  @;        If @${\Gamma \wellKE e}
  @;         and @${x \not in \Gamma}
  @;         then @${x,\Gamma \wellKE e}
  @;      }
  @;    ]
  @;  @proof{
  @;    Immediate, because
  @;     @${\Gamma \wellKE e : K}
  @;     and/or
  @;     @${\Gamma \wellKE e}
  @;     imply that @${e} is closed under @${\Gamma}.
  @;  }



Need this:

@; TODO find a home for this "bowtie" metafunction

@exact|{
\begin{flushleft}
\fbox{$\DSlift{E}{\rrR}{E'}{\rrRp}$} $= \vtuple{\ccR}{\ccRp}$ where:\\
$\begin{array}{l@{~~}c@{~~}l@{~~}l}
\ctxE{\edyn{\tau}{e}} & \ccR & \ctxE{\edyn{\tau}{e'}}
  & \mbox{if $e \ccRp e'$}
\\
\ctxE{\edyn{\tau}{e}} & \ccR & A
  & \mbox{if $e \ccRp A$ and $A \not\in e'$}
\\
e & \ccR & A
  & \mbox{if $e \cclift{E}{\rrR} A$}
\\[1ex]
\ctxE{\esta{\tau}{e}} & \ccRp & \ctxE{\esta{\tau}{e'}}
 & \mbox{if $e \ccR e'$}
\\
\ctxE{\esta{\tau}{e}} & \ccRp & A
 & \mbox{if $e \ccR A$ and $A \not\in e'$}
\\
e & \ccRp & A
 & \mbox{if $e \cclift{E}{\rrR'} A$}
\end{array}$

\end{flushleft}
}|
