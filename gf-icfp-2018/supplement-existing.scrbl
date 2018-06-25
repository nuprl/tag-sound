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
The goal is to
  demonstrate that the framework is able to express the main ideas of existing
   systems,
  and to outline a formal comparison between the existing systems.

The subsections also give canonical forms lemmas for each system.
This is because at the time of writing the first author thought the lemmas
 gave a quick sample of the systems' logical implications.

@; At present (2018-05-31) these illustrations have not been approved by the
@;  authors of the systems.
@; We plan to review these illustrations with the relevant authors before the ICFP
@;  camera-ready.


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

Thorn (@figure-ref{fig:existing-thorn}) is a nominally-typed object-oriented language.
The idea is that a program may: declare typed classes,
 use the classes to create typed objects,
 and manipulate the objects in gradually-typed methods.
If a method expects a dynamically-typed object,
 the type checker lets the method perform any operation on the object
 and the run-time system dynamically checks whether the operations are
 actually valid.

The types @${\tau} include @emph{concrete} class names @${C},
 @emph{like} class names (@${\thornlike{C}}),
 and a dynamic type (@${\thorndyn}).
The values are possibly-wrapped pointers to instances of classes;
 a value is either a direct pointer @${p},
 a dynamically-typed @emph{view} to a pointer @${\thorncast{\thorndyn}{p}},
 or a like-typed view to a pointer @${\thorncast{\thornlike{C}}{p}}.
Informally, a view is a method-local pointer to an object.

One main invariant of Thorn is that every value comes with a type.
In the figure, every value is an instance of a class and has the class name
 as its type.
Because of this invariant, Thorn can efficiently check whether a value is
 compatible with some other type annotation at runtime.
The @${\vfromsta} function demonstrates this compatibility check.

The @${\vfromdyn} function is undefined for all inputs because there is
 no such thing as a dynamically-typed value.
Put another way, the Thorn surface language is a single statically-typed
 language as opposed to a pair of languages.
(The statically-typed language includes a dynamic to make it easy to experiment
 with statically-typed values, but nevertheless all values are statically typed
 to ensure safety and efficiency.)

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

@include-figure["fig:existing-thorn.tex" @elem{Thorn types, values, and boundary functions. The @${\vfromdyn} function is undefined for all inputs.}]


@; -----------------------------------------------------------------------------
@|clearpage|
@(define strongscript @${\strongscript})
@section[#:tag "existing-strongscript"]{StrongScript}

StrongScript (@figure-ref{fig:existing-strongscript}) adapts the ideas from
 Thorn to a type system for JavaScript.
The types @${\tau} include concrete class names (@${\sstconcrete{C}}),
 like class names (@${C}),
 a dynamic type (@${\sstdyn}),
 and function types (@${\tarr{\tau}{\tau}}).
The values are objects and functions.

Every object and function comes with an intrinsic type.
For an object imported from JavaScript, this type is @${\sstdyn}.
(For a function imported from JavaScript, this type is presumably
 @${\tarr{\sstdyn}{\sstdyn}}.)
A typed object cannot inherit from a JavaScript object, and vice-versa.

The @${\vfromsta} function checks the intrinsic type of a value against
 a type annotation.
The idea is, if the check succeeds then a context may assume that the type
 annotation accurately describes the value.

The @${\vfromdyn} function is undefined for all inputs because the StrongScript
 paper does not directly model interactions with JavaScript.
Instead, a JavaScript object is modeled as an object with type @${\sstdyn},
 as mentioned above.

@; Classes cannot have fields of function type or of undefined type.
@; The dynamic type (@${\sstdyn}) is not a subtype or supertype of any other type.
@; Not allowed to override methods.
@; Not allowed to delete members of a class if those members are part of its type.
@; Not allowed to change type of an object; an object imported from JavaScript always has type @${\sstdyn}.

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

@include-figure["fig:existing-strongscript.tex" @elem{@|strongscript| boundary functions. The @${\vfromdyn} function is undefined for all inputs.}]


@; -----------------------------------------------------------------------------
@|clearpage|
@section[#:tag "existing-dart"]{Dart 2}

Dart 2 is a language under development at Google with some support for
 dynamic typing.
For details, see: @hyperlink["https://www.dartlang.org/dart-2"]{dartlang.org/dart-2}

@Figure-ref{}


For an official description, see the Dart website:

@nested[#:style 'inset ]



@; Dart VM version: 2.0.0-edge.ca7a70ff41cf561419d69a753d546e92b8d29a68 (Thu May 10 20:48:15 2018 +0000) on "linux_x64"


The function syntax is an abuse of notation; to write the type @${\tarr{\darttint}{\darttint}}
 one must define a new type:

@verbatim{
  typedef int Ifun(int _); // Ifun ~ int -> int
}

Dart also uses a heap.

Dynamic is not a subtype of any type other than itself.

Every value comes with a type.
The type never goes away and is checked at run-time.

In particular, a Dart value of type @${\darttdyn} has the form @${\dartval{b}{\tau}}
 where @${\tau} is any type.

@; need to emphasize the weirdness, that dynamic doesn't coerce to integer

@tr-lemma[#:key "dart-canonical" @elem{Dart canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : \tau} then @${v \valeq \dartval{b}{\tau'}} and @${\tau' \subteq \tau}
    }
  ]
}

@include-figure["fig:existing-dart.tex" @elem{Dart boundary functions for a restricted grammar of types. The @${\vfromdyn} function is undefined for all inputs.}]


@; -----------------------------------------------------------------------------
@|clearpage|
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
@|clearpage|
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
@|clearpage|
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

