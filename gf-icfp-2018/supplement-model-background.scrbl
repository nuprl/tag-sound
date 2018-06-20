#lang gf-icfp-2018
@require{techreport.rkt}
@UID++[]
@title[#:tag "appendix:preliminaries"]{Preliminaries}

@tr-definition[#:key "divergence" @elem{@${\rastar} divergence}]{
  Given a reduction relation @${\rastar}, an expression @${e} diverges if for
   all @${e'} such that @${e\!\rastar\!e'} there exists an @${e''} such that
   @${e'\!\rrarrow\!e''}.
}@|smallskip|

@; TODO cite barendregt ?
@tr-convention["variable convention"]{
  All @${\lambda}-bound variables in an expression are distinct from one
   another, and from any free variables in the expression.
}@|smallskip|

@;@tr-lemma["weakening"]{
@;  If @${\Gamma \vdash e} then @${x,\Gamma \vdash e}
@;}@|smallskip|

@tr-assumption[@elem{@${\vdash} permutation}]{
For all typing judgments and properties @${\vdash}:
@itemlist[
@item{
  If @${x,x',\Gamma \vdash e} then @${x',x,\Gamma \vdash e}
}
@item{
  If @${\tann{x}{\tau},\tann{x'}{\tau'},\Gamma \vdash e} then @${\tann{x'}{\tau'},\tann{x}{\tau},\Gamma \vdash e}
}
]
}@|smallskip|

@tr-definition[#:key "purely-static" @elem{@${\vdash} boundary-free}]{
  An expression @${e} is @emph{boundary free} if @${e} does not contain
  a subterm of the form @${(\edyn{\tau'}{e'})}, nor a subterm of the form
  @${(\esta{\tau'}{e'})}.
}

@exact{\bigskip}

@exact{\noindent}@emph{Notes:}
@itemlist[
@item{
  The upcoming models use a common surface syntax and typing system, but to
  keep each model self-contained we reprint this system in each definition.
}
]
