#lang gf-icfp-2018
@require{techreport.rkt}

@;  @url{http://hacklang.org/}
@;  (@url{https://flow.org/})
@;  (@url{http://mypy-lang.org/})
@;  (@url{https://www.pyret.org/})
@; (@url{https://pyre-check.org/})
@; (@url{https://goo.gl/p5rmSe})  https://opensource.google.com/projects/pytype https://github.com/google/pytype

@appendix-title{Existing Systems}

This section illustrates prior work on gradual typing using the semantic
 framework of the paper.

At present (2018-05-31) these illustrations have not been approved by the
 authors of the systems.
We plan to review these illustrations with the relevant authors before the ICFP
 camera-ready.


@; -----------------------------------------------------------------------------

@; C# TODO
@; values = i | object ...
@; t = int | byte | object | dynamic | C(\sigma) 
@;  ... techincally object/dynamic are C
@; D udnefined
@; S ... checks subtype? not sure ened to see paper
@; and dynamic is not a subtype of anything

@; -----------------------------------------------------------------------------
@section[#:tag "existing-thorn"]{Thorn}

@include-figure["fig:existing-thorn.tex" @elem{Thorn types, values, and boundary functions. The @${\vfromdyn} function is undefined for all inputs.}]

@Figure-ref{fig:existing-thorn} summarizes Thorn.

The actual model uses a heap.

There are no untyped classes or objects.
Every value has a class name.
Consequence: the @emph{this} variable ia always concretely typed in method calls.

Thorn lets values pass from static to dynamic at runtime.
(Cannot explicitly cast from static to dynamic.)

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

@include-figure["fig:existing-strongscript.tex" @elem{@|strongscript| boundary functions. The @${\vfromdyn} function is undefined for all inputs.}]

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

URL: @url{https://www.dartlang.org/dart-2}


@include-figure["fig:existing-dart.tex" @elem{Dart boundary functions for a restricted grammar of types. The @${\vfromdyn} function is undefined for all inputs.}]

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
  @itemlist[
    @item{
      If @${\vdash v : \safetstpair{\tau_0}{\tau_1}} then @${v \valeq \safetspair{\tau_0'}{v_0}{\tau_1'}{v_1}}
      and @${\tau_0' \subteq \tau_0} and @${\tau_1' \subteq \tau_1}
    }
    @item{
      If @${\vdash v : \safetstfun{\tau_d}{\tau_c}} then
      @${v \valeq \safetsfun{\tau_d'}{x}{\tau_c'}{e}}
      and @${\safetstfun{\tau_d'}{\tau_c'} \subteq \safetstfun{\tau_d}{\tau_c}}
    }
    @item{
      If @${\vdash v : \safetstnum} then @${v \valeq i}
    }
  ]
}


@; -----------------------------------------------------------------------------
@section[#:tag "existing-nom"]{Nom}

@include-figure["fig:existing-nom.tex" @elem{Nom. The @${\vfromdyn} function is undefined for all inputs.}]

Nom is a nominal object oriented language.
Subset of pre-generics Java.
Proven to satisfy the gradual guarantee.

@tr-lemma[#:key "nom-canonical" @elem{Nom canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : C} then @${v = C'(v', \ldots)} and @${C' \subteq C}
    }
  ]
}

