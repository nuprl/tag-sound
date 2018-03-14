#lang gf-icfp-2018
@require{techreport.rkt}
@UID++[]
@title[#:tag "appendix:preliminaries"]{Preliminaries}


@tr-definition[#:key "divergence" @elem{@${\rastar}-divergence}]{
  An expression @${e} diverges for the reduction relation @${\rastar} if for
   all @${e'} such that @${e\!\rastar\!e'} there exists an @${e''} such that
   @${e'\!\rrarrow\!e''}.
}@|smallskip|

@tr-convention["variable convention"]{
  All @${\lambda}-bound variables in an expression are distinct from one
   another, and from any free variables in the expression.
}@|smallskip|

@;@tr-lemma["weakening"]{
@;  If @${\Gamma \vdash e} then @${x,\Gamma \vdash e}
@;}@|smallskip|

@tr-lemma["permutation"]{
  If @${x,x',\Gamma \vdash e} then @${x',x,\Gamma \vdash e}
}@|smallskip|

@tr-definition[#:key "purely-static" @elem{purely-static expression}]{
  An expression @${e} is @emph{purely static} if there exists a type @${\tau}
   such that @${\wellM e : \tau} and @${e} does not contain a subterm of the
   form @${(\edyn{\tau'}{e'})}.
}
