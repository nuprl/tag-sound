#lang gf-icfp-2018
@require["techreport.rkt" (only-in scribble/base url)]


@appendix-title{Existing Systems}

This section illustrates prior work on gradual typing using the semantic
 framework of the paper.
The goal is to
  demonstrate that the framework is able to express the @emph{type boundaries}
  and @emph{boundary checks} of existing systems,
  and to outline a formal comparison.

This section does not attempt to summarize the novelties and subtleties of
 each system.
The interested reader must seek out the primary sources.

The subsections also give canonical forms lemmas for each system
 as a taste of their logical implications.
 
@; At present (2018-05-31) these illustrations have not been approved by the
@;  authors of the systems.
@; We plan to review these illustrations with the relevant authors before the ICFP
@;  camera-ready.

@parag{URLs}

All URLs accessed on 2018-06-28.

@itemlist[
@item{
  Gradualtalk : @url{https://pleiad.cl/research/software/gradualtalk}
}
@item{
  Typed Racket : @url{https://github.com/racket/typed-racket}
}
@item{
  TPD : @url{https://github.com/jack-williams/tpd}
}
@item{
  StrongScript : @url{https://plg.uwaterloo.ca/~dynjs/strongscript/}
}
@item{
  ActionScript : @url{https://www.adobe.com/devnet/actionscript.html}
}
@item{
  mypy : @url{http://mypy-lang.org/}
}
@item{
  Flow : @url{https://flow.org/}
}
@item{
  Hack : @url{http://hacklang.org/}
}
@item{
  Pyre : @url{https://pyre-check.org/}
}
@item{
  Pytype : @url{https://opensource.google.com/projects/pytype}
}
@item{
  rtc : @url{https://github.com/plum-umd/rtc}
}
@item{
  Strongtalk : @url{http://strongtalk.org/}
}
@item{
  TypeScript : @url{https://www.typescriptlang.org/}
}
@item{
  Typed Clojure : @url{http://typedclojure.org/}
}
@item{
  Typed Lua : @url{https://github.com/andremm/typedlua}
}
@item{
  Pyret : @url{https://www.pyret.org/}
}
@item{
  Thorn : @url{http://janvitek.org/yearly.htm}
}
@item{
  Dart 2 : @url{https://www.dartlang.org/dart-2}
}
@item{
  Nom : @url{https://www.cs.cornell.edu/~ross/publications/nomalive/}
}
@item{
  Reticulated : @url{https://github.com/mvitousek/reticulated}
}
@item{
  SafeTS : @url{https://www.microsoft.com/en-us/research/publication/safe-efficient-gradual-typing-for-typescript-3/}
}
@item{
  @|TR_LD| : @url{https://github.com/bennn/typed-racket/releases/tag/ld1.0}
}
]


@; -----------------------------------------------------------------------------

@; C# TODO
@; values = i | object ...
@; t = int | byte | object | dynamic | C(\sigma) 
@;  ... techincally object/dynamic are C
@; D udnefined
@; S ... checks subtype? not sure ened to see paper
@; and dynamic is not a subtype of anything

@; -----------------------------------------------------------------------------
@|clearpage|
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
@; Dart VM version: 2.0.0-edge.ca7a70ff41cf561419d69a753d546e92b8d29a68 (Thu May 10 20:48:15 2018 +0000) on "linux_x64"

Dart 2 is a new language with some support for
 dynamic typing.
For details, see: @hyperlink["https://www.dartlang.org/dart-2"]{dartlang.org/dart-2}

@Figure-ref{fig:existing-dart} summarizes the key aspects of dynamic typing
 in Dart for a few types.
The types represent integers (@${\darttint}),
 integers and decimal numbers (@${\darttnum}),
 lists (@${\darttlist{\tau}}),
 functions (@${\tarr{\tau}{\tau}}),
 and a dynamic type (@${\darttdyn}).
The base values @${b} match these types.

Dart programs do not directly interact with base values.
Instead, base values are stored on a typed heap.
The values @${v} in @figure-ref{fig:existing-dart} model this indirection
 by associating a base value with a compatible type.

Just like in Thorn, a typed value may be used in a context that expects a
 less precise type.
Also like Thorn, a value of type @${\darttdyn} is an object that the type
 checker assumes can recieve any method call.
The run-time system checks that such method calls are actually safe for the
 given value.

The @${\vfromsta} boundary function checks a value against a type annotation
 by checking the value's associated type.
The @${\vfromdyn} function is undefined for all inputs because it is not possible
 to define (or interact with) an untyped value.

@; Dynamic is not a subtype of any type other than itself.
@; need to emphasize the weirdness, that dynamic doesn't coerce to integer

@tr-lemma[#:key "dart-canonical" @elem{Dart canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : \tau} then @${v \valeq \dartval{b}{\tau'}} and @${\tau' \subteq \tau}
    }
  ]
}

@emph{Remark:} a Dart function type must be declared explicitly.
For example, to use the type @${\tarr{\darttint}{\darttint}} one must first
 define an alias:

@nested[#:style 'inset
@verbatim{
  typedef int IntFun(int _);
}]

@exact{\noindent}Then the name @tt{IntFun} may appear in other type annotations,
 e.g., in a method signature.

@exact{\vspace{8cm}}

@include-figure["fig:existing-dart.tex" @elem{Dart boundary functions for a restricted grammar of types. The @${\vfromdyn} function is undefined for all inputs.}]


@; -----------------------------------------------------------------------------
@|clearpage|
@section[#:tag "existing-pyret"]{Pyret}

Pyret is a dynamically-typed language with optional type annotations and
 an optional static type checker.
For details, see: @hyperlink["https://www.pyret.org"]{pyret.org}.

A type annotation in a Pyret program acts as a type-constructor
 check at run-time.
@Figure-ref{fig:existing-pyret} illustrates this aspect of Pyret in the
 @${\rrS} and @${\rrD} notions of reduction.
Both check the argument and result of a typed function against
 the function's type.
The @${\vfromany} boundary function performs the check by matching
 a type constructor @${K} against a value.

One aspect of Pyret that is missing from @figure-ref{fig:existing-pyret} is
 the translation that maps type annotations in the source code to run-time
 constructor checks.
This translation could be modeled with a completion function (@${\carrow}),
 similar to the model of the first-order embedding in the paper.
 
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

@include-figure["fig:existing-pyret.tex" @elem{Pyret boundary functions and semantics for a restricted grammar of types.}]


@; -----------------------------------------------------------------------------
@|clearpage|
@section[#:tag "existing-safets"]{SafeTS}

SafeTS is a core model of Safe TypeScript, which is a sound type system for
 JavaScript (as opposed to TypeScript).

@Figure-ref{fig:existing-safets} demonstrates SafeTS on three types:
 a type for numbers (@${\safetstnum}),
 a type for an object with two fields (@${\safetstpair{\tau}{\tau}}),
 and a type for an object with one method (@${\safetstfun{\tau}{\tau}}).
The latter types are intended to represent tuples and anonymous functions.

Every value in a SafeTS program has an intrinsic type;
 there is no notion of a value that is defined in dynamically-typed code and
 imported to statically typed code.
A typed value may, however, be used in a context that expects values with a
 different type by means of a type cast.
The different type may contain new fields, but otherwise must be a supertype
 of the value's intrinsic type.

The @${\vfromsta} boundary function illustrates the run-time checks that
 SafeTS performs for our number, pair, and function types.
For type @${\safetstnum}, SafeTS checks that the value is a number.
For a pair type, SafeTS checks that the value is a pair of compatible type and
 recursively transports the components.
For a function type, SafeTS checks that the value is a function of compatible
 type.

The @${\vfromdyn} function is undefined because the SafeTS model does not
 define interactions with a model of JavaScript.

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

@exact{\medskip}

@emph{Remark:} if a SafeTS cast adds new fields to a value, the fields are recorded
 in an external ``tag heap'' of run-time type information.
@Figure-ref{fig:existing-safets} does not model the tag heap because it is
 not relevant to the types in the figure.

@exact{\vspace{4cm}}

@include-figure["fig:existing-safets.tex" @elem{SafeTS. The @${\vfromdyn} function is undefined for all inputs.}]


@; -----------------------------------------------------------------------------
@|clearpage|
@section[#:tag "existing-nom"]{Nom}

Nom is a nominal object oriented language.
Types include a top type (@${\nomtany}),
 class names (@${C}),
 and a dynamic type (@${\nomtdyn}).
Values are instances of classes.
Each value has an intrinsic type; namely, the name of its class.

The @${\vfromsta} function checks that the intrinsic type of a value
 is compatible with a given type annotation.
The @${\vfromdyn} function is undefined for all inputs because there way to
 define or import an untyped value.

@tr-lemma[#:key "nom-canonical" @elem{Nom canonical forms}]{
  @itemlist[
    @item{
      If @${\vdash v : C} then @${v = C'(v', \ldots)} and @${C' \subteq C}
    }
  ]
}

@exact{\vspace{20cm}}

@include-figure["fig:existing-nom.tex" @elem{Nom. The @${\vfromdyn} function is undefined for all inputs.}]

