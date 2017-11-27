#lang gf-pldi-2018

Road map:

  @models-roadmap[
    #:D "Dynamic"
    #:S "Static"
    #:M "Multi-Language"
    #:E "Erasure Embedding"
    #:N "Natural Embedding"
    #:L "Co-Natural Embedding"
    #:F "Forgetful Embedding"
    #:K "Tagged Embedding"]

@section{Preliminaries}

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

