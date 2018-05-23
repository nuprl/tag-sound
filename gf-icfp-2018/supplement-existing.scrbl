#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title{Existing Systems}

Technical illustrations of prior work on gradual and migratory typing.


@; -----------------------------------------------------------------------------

@; -----------------------------------------------------------------------------
@section[#:tag "existing-thorn"]{Thorn}

@include-figure["fig:existing-thorn.tex" @elem{Thorn types, values, and boundary functions.}]

@Figure-ref{fig:existing-thorn} summarizes Thorn.

The actual paper uses a heap.

The @emph{this} variable ia always concretely typed.
There are no untyped classes or objects.

Thorn lets values pass from static to dynamic at runtime.
(Cannot explicitly cast from static to dynamic.)

Thorn does not let values cross from dynamic to static without an explicit type
 cast.

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
@(define strongscript @${\strongscript})
@section[#:tag "existing-strongscript"]{StrongScript}

@include-figure["fig:existing-strongscript.tex" @elem{@|strongscript| boundary functions.}]

Classes cannot have fields of function type or of undefined type.

The dynamic type (@${\sstdyn}) is not a subtype or supertype of any other type.

Not allowed to override methods.

Not allowed to delete members of a class if those members are part of its type.

Not allowed to change type of an object; an object imported from JavaScript
 always has type @${\sstdyn}.

@tr-lemma[#:key "strongscript-canonical" @elem{@|strongscript| canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : \sstconcrete{C}}
      then @${v \valeq \ssobj{\tann{s}{v} \ldots m \ldots}{C'}}
      and @${C' \subteq C}
    }
    @item{
      If @${\vdash v : C}
      then either:
      @itemlist[
      @item{
        @${v \valeq \ssobj{\tann{s}{v} \ldots m \ldots}{C'}}
      }
      @item{
        @${v \valeq \ssobj{\tann{s}{v} \ldots m \ldots}{\sstdyn}}
      }
      ]
    }
    @item{
      If @${\vdash v : \tarr{\tau_d}{\tau_c}}
      then @${v \valeq \ssfun{\tann{x}{\tau_d}}{e}{\tau_c}}
    }
    @item{
      If @${\vdash v : \sstdyn}
      then either:
      @itemlist[
      @item{
        @${v \valeq \ssobj{\tann{s}{v} \ldots m \ldots}{C'}}
      }
      @item{
        @${v \valeq \ssobj{\tann{s}{v} \ldots m \ldots}{\sstdyn}}
      }
      @item{
        @${v \valeq \ssfun{\tann{x}{\sstdyn}}{e}{\sstdyn}}
      }
      ]
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

In particular, a Dart value of type @${\darttdyn} has the form @${\dartval{b}{\tau}}
 where @${\tau} is any type.

@; need to emphasize the weirdness, that dynamic doesn't coerce to integer


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


@; -----------------------------------------------------------------------------
@section[#:tag "existing-safets"]{SafeTS}

@include-figure["fig:existing-safets.tex" @elem{SafeTS. The @${\vfromdyn} function is undefined for all inputs.}]

SafeTS is a formal core of Safe TypeScript.

Every object is statically type-checked and comes with a type.
(The embedding of compiled SafeTS to a formal semantics of JavaScript is beyond
 the scope of this work.)

A cast may add fields.

A cast may not add methods; a cast fails if the source objects methods are not
 all subtypes of the target objects methods.

The model keeps types in an external tag heap.
The types we use here for illustration do not require the heap.


@tr-lemma[#:key "safets-canonical" @elem{SafeTS canonical forms}]{
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


