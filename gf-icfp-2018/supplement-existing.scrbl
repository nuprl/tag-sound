#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Existing Systems}

Technical illustrations of prior work on gradual and migratory typing.


@; -----------------------------------------------------------------------------

@; -----------------------------------------------------------------------------
@section[#:tag "existing-thorn"]{Thorn}

@include-figure["fig:existing-thorn.tex" @elem{Thorn types, values, and boundary functions. The @${\vfromdyn} boundary function is undefined for all inputs.}]

@Figure-ref{fig:existing-thorn} summarizes Thorn.

The actual paper uses a heap.

Thorn lets values pass from static to dynamic at runtime.
Thorn does not let values cross from dynamic to static without an explicit type
 cast; all Thorn programs must pass the static type checker, and the static type
 checker rejects programs that send a more dynamic variable into a less dynamic context.
For example, if a program contains a class @${\texttt{Integer}} with a method
 @${\texttt{add}} that expects in instance of the @${\texttt{Integer}} class,
 then applying the method to a dynamically-typed value raises a static typing error:

@verbatim|{
  class Integer Object {
    def add(n1 : Integer) : Integer = { .... }
    ....
  }
  Integer n0 = new Integer(0);
  dyn n1 = (dyn) n0;
  n0.add(n1) // static type error
}|


Thorn values are pointers to objects.
A pointer may be wrapped in at most one cast.

@tr-lemma[#:key "thorn-canonical" @elem{Thorn canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : C} then @${v \valeq C'(f = v_f, \ldots)} and @${C' \subteq C}.
    }
    @item{
      If @${\vdash v : \thornlike{C}} then @${v \valeq \thorncast{\thornlike{C'}}{p}} and @${C' \subteq C}
    }
    @item{
      If @${\vdash v : \thorndyn} then @${v \valeq \thorncast{\thorndyn}{p}}
    }
  ]
}


@; -----------------------------------------------------------------------------
@section[#:tag "existing-dart"]{Dart}

@include-figure["fig:existing-dart.tex" @elem{Dart boundary functions for a restricted grammar of types.}]

The function syntax is an abuse of notation; to write the type @${\tarr{\darttint}{\darttint}}
 one must define a new type:

@verbatim{
  typedef int Ifun(int _); // Ifun ~ int -> int
}

Dart also uses a heap.

Dynamic is not a subtype of any type other than itself.

Every value comes with a type.
The type never goes away and is checked at runtime.

@tr-lemma[#:key "dart-canonical" @elem{Dart canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : \tau} then @${v \valeq \dartval{b}{\tau'}} and @${\tau' \subteq \tau}
    }
  ]
}


@; -----------------------------------------------------------------------------
@section[#:tag "existing-pyret"]{Pyret}

@include-figure["fig:existing-pyret.tex" @elem{Pyret boundary functions and semantics for a restricted grammar of types.}]

@tr-lemma[#:key "pyret-canonical" @elem{Pyret assert-canonical forms}]{
  If @${v} is a value with the static type @${\tau} then @${v} may be any kind of value;
   however, if @${v} is assigned to a variable @${x} with the programmer-assigned
   type @${\tau}, then one of the following holds:
  @itemlist[
    @item{
      If @${\vdash x : \tpair{\tau_0}{\tau_1}} then @${v \valeq \vpair{v_0}{v_1}}
    }
    @item{
      If @${\vdash x : \tarr{\tau_d}{\tau_c}} then either:
      @itemlist[
      @item{
        @${v \valeq \vlam{y}{e}}
      }
      @item{
        @${v \valeq \vlam{\tann{\tann{y}{\tau_d'}}{\tau_c'}}{e}}
      }
      ]
    }
    @item{
      If @${\vdash x : \tint} then @${v \in \integers}
    }
    @item{
      If @${\vdash x : \tnat} then @${v \in \naturals}
    }
  ]
}
