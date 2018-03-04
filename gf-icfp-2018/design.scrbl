#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]
@title[#:tag "sec:design"]{Apples-to-Apples Logic and Metatheory}

@; TODO
@; - the multi-language approach
@; - natural, tag, erasure [[nothing else!]]
@; ? why do we call it embedding?
@; - A @mytech{migratory typing system} is XXX and must YYY

@; -----------------------------------------------------------------------------

In this section we equip one syntax for @mytech{mixed-typed programs} (@figure-ref{fig:multi-syntax})
 with one type system (@figure-ref{fig:multi-preservation}) and three semantics
 (sections @secref{sec:natural-embedding}, @secref{sec:locally-defensive-embedding},
 and @secref{sec:erasure-embedding}).
Each semantics satisfies a unique soundness condition.


@section{Illustration}
@; could be seeds / trees / fruits
@; - apple / plant / fruit soundness?
@; - harder to picture trees crossing boundaries,
@;   or trees & picked fruit coexisting
@;
@; TODO need to add food

Start with a special tank of fish and eggs.
The fishtank is special because every thing in the tank is either:
 an adult @emph{red snapper},
 a red snapper egg,
 or a box of red snapper food.
A red snapper fish has a beautiful red color and is precisely @~a[(/ 1 RED-SNAPPER-RATIO)]
 times as wide as it is tall.
Red snappers can only eat certified red snapper food, else they get sick and die.
A red snapper egg is certified to hatch into a red snapper (if it hatches at all).
Over time, as old fish die out and new fish hatch from eggs, this @emph{red snapper soundness}
 property always holds for this fishtank.

@inline-pict[fishtank-pict]

One day a pathway appears, linking our fishtank to the outside.
The red snapper soundness property is now at risk.
Anything might cross over the pathway, including but not limited to:
 a red snapper, a blue snapper, a mysterious egg, or a jack-o-lantern.
The question is, what to do about this pathway.

@inline-pict[fishtank/biohazard]

One option is to enforce the red snapper property.
If an adult thing arrives at the boundary, conduct a physical examination to
 check that it is an adult red snapper.
If a mysterious egg arrives at the boundary, check its color (all red snapper
 eggs are red, of course) and monitor it.
When the egg hatches, immediately conduct a physical exam.
If a box of food arrives, check that it is safe for red snappers.
Conducting the physicals and monitoring the eggs may be costly, but is guaranteed
 to let all incoming red snappers into the tank and keep all non-red-snappers
 out.

@inline-pict[fishtank/biohazard/natural]

A second option is to let anything cross the pathway and forget about the
 red snapper property.
Instead we can be content with a trivial @emph{fish soundness} property;
 namely, that every thing in the tank is either native to the tank or came
 from the pathway.

@inline-pict[fishtank/biohazard/erasure]

A third option is to enforce a weaker @emph{red soundness} property.
If an adult thing arrives at the boundary, check its color and allow only
 red things.
If an egg arrives, check its color and check the color of the baby when it hatches.
These checks cannot ensure red snapper soundness in the face of arbitrary inputs.

@inline-pict[fishtank/biohazard/locally-defensive]

This concludes the illustration.
The three options outlined above correspond to three notions of type soundness
 for typed/untyped programs.
The strategy to enforce red snapper soundness is the natural embedding.
The strategy for fish soundness is the erasure embedding.
The strategy for red soundness is the locally-defensive embedding.


@section{Common Semantic Notions}

@Figure-ref{fig:multi-syntax} presents the syntax.
The grammar for @${\exprdyn} defines an untyped host language; the
 grammar @${\exprsta} defines an explicitly-typed twin language.
Both expression languages, @${\exprdyn} and @${\exprsta}, describe a lambda
 calculus extended with integers, pairs, related primitive operations,
 and @emph{boundary terms}.
The @${\exprdyn} boundary term @${(\esta{\tau}{\exprsta})} embeds a
 typed expression in an untyped context.
Conversely, the @${\exprsta} boundary term @${(\edyn{\tau}{\exprdyn})} embeds
 a dynamically-typed expression; the type annotation @${\tau} describes the
 context's assumptions about the value of the embedded expression.

The syntax intentionally does not include recursive functions, arbitrary-length
 data structures, mutable values, or infinite values such as streams.
Incorporating these values and their types is straightforward given a strategy
 that handles basic values, immutable data structures, and anonymous functions.
See @secref{sec:implementation} for details.
@; simple as possible ... well I guess pairs could be immutable boxes

@Figure-ref{fig:multi-preservation} defines a type system for this
 surface language.
An expression @${e} is well-formed, written @${\cdot \wellM e}, if it
 has no free variables and all its embedded terms are well-typed.
An expression is well-typed, written @${\cdot \wellM \exprsta : \tau},
 if it has no free variables, does not apply a function or primitive operation
 to an argument outside its domain, and all its embedded terms are well-typed.

The challenge is to define a sound semantics for well-typed expressions.
Specifically, we are looking for a reduction relation @${\rastar} that provides:
@itemlist[
@item{
  @emph{soundness for a single language}: for expressions without boundary
   terms, the typing judgment in @figure-ref{fig:multi-preservation} is sound
   with respect to the reduction semantics;
}
@item{
  @emph{expressive boundary terms}: the static and dynamic twin languages can
   share values at any type;
  @; e.g. no rule (dyn t->t v) ==> error to prohibit sharing all function
}
@item{
  @emph{soundness for the pair of languages}: for all expressions,
   evaluation preserves some property, though it may be weaker than a standard
   notion of type soundness.
}
]
With these goals in mind, the following three subsections give strategies for
 embedding untyped expressions (@${\exprdyn}) within typed expressions (@${\exprsta})
 and vice-versa.
Each embedding is made of five basic ingredients:
 a notion of reduction @${\rrD} for dynamically-typed expressions;
 a notion of reduction @${\rrS} for statically-typed expressions;
 a function @${\vfromdyn} that imports a dynamically-typed value into a typed context;
 a function @${\vfromsta} that imports a statically-typed value into an untyped context;
 and a judgment form that is both implied by the typing judgment in
 @figure-ref{fig:multi-preservation} and sound with respect to a semantics derived from the
 four previous components.

The starting point for these embeddings is the @mytech{evaluation syntax}
 and @${\delta} function in @figure-ref{fig:multi-reduction}.
The syntax provides a uniform language for reduction relations:
 the expression grammar @${e} is the domain of evaluation,
 evaluation ends in either a value @${v} or error @${\eerr},
 and the order of evaluation is guided by contexts @${\ES}.
There are two kinds of error.
Since this is a multi-language system, a @mytech{boundary error} @${\boundaryerror}
 can occur when one language receives an incompatible value from another.
A @mytech{tag error} @${\tagerror} occurs when value of the wrong shape reaches
 an elimination form.
@; GAAAH
High level: boundary errors and tag errors both occur because of bad values;
 boundary error is from an impedence mismatch between languages,
 tag error is from a mismatch between components in one language.
Evaluation contexts have two levels.
A pure context @${\ebase} does not contain boundary terms;
 an evaluation context @${\esd} may contain boundary terms.
This distinction is important if the embedding has two notions of reduction
 for typed and untyped code.

The @${\delta} function assigns meaning to the primitives.
The primitives @${\vfst} and @${\vsnd} extract the first and second components
 of a pair value, respectively.
The primitive @${\vsum} adds integers and the primitive @${\vquotient} performs
 integer division.
Division by zero raises a boundary error because one language (math) received
 an incompatible value from another language (@${\exprdyn} or @${\exprsta}) 

@include-figure["fig:multi-syntax.tex" @elem{Twin languages syntax}]
@include-figure["fig:multi-preservation.tex" @elem{Twin languages static typing judgments}]
@include-figure["fig:multi-reduction.tex" @elem{Common semantic notions}]

@;In order to provide some kind of type soundness, an embedding must restrict
@; the dynamically-typed values that can flow into typed contexts.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:natural-embedding"]{Natural Embedding}
@include-figure*["fig:natural-reduction.tex" "Natural Embedding"]
@include-figure*["fig:natural-preservation.tex" "Property judgments for the natural embedding"]

@; Thesis for this section?
@; - impossible to provide conventional soundness, but can faithfully
@;   approximate with runtime checks ?
@; ... simple idea just od `\vdash e : \tau` at runtime

@subsection[#:tag "sec:natural:overview"]{Overview}

A standard type soundness theorem guarantees that if a well-typed expression
 reduces to a value, the value is of the same type.
This guarantee comes about because the static type checker establishes a type
 for every sub-expression, and these proofs compose.
The analogous guarantee for the surface syntax (@figure-ref{fig:multi-syntax})
 and typing system (@figure-ref{fig:multi-reduction}) is the following:

@$$|{
  \mbox{\emph{(ideal)}}
    {\cdot \wellM \exprsta : \tau}
    \wedge
    {\exprsta \rastar v}
    \Rightarrow
    {\cdot \wellM v : \tau}
}|

It is impossible to realize this guarantee in the same way as in a statically-typed
 language, because some terms are intentionally untyped.
In the expression @${(\edyn{\tau}{e})} there is no guarantee that the expression
 @${e} has type @${\tau}, or any type at all.
Instead, however, it is possible to approximate the same guarantee with
 runtime checks.
When a value @${v} flows from dynamically-typed code into a statically-typed
 context expecting a value of type @${\tau}, a runtime check can try to establish
 that the value is well-typed.
The question is then how to implement such checks.

For base types such as @${\tint} and @${\tnat}, we suppose that the language
 comes with primitives that implement @${v \in \integers} and @${v \in \naturals}
 (see @secref{sec:implementation:tag-check} for a discussion).
For inductive types such as @${\tpair{\tau_0}{\tau_1}}, an inductive checking
 strategy can confirm that a value is a pair and that its components match
 the types @${\tau_0} and @${\tau_1}, respectively.@note{Notation: @${\tau_0} is the type at index zero in the pair type, @${\tau_1} is the type at index one.}
For coinductive types such as @${\tarr{\tau_d}{\tau_c}}, the @emph{natural}
 approach is to check that the value is a function and monitor its future
 behavior for counterexamples to the conjecture that it treats its inputs as
 values of type @${\tau_d} and yields values of type @${\tau_c}.@note{Notation: @${\tau_d} is the domain type, @${\tau_c} is the codomain type.}
Monitoring delays a type error until the runtime system finds a witness
 that the given value does not match the coinductive type.

@Figure-ref{fig:natural-reduction} implements the above checking strategy
 and uses it to define a reduction relation.
@; ??? really just want to say "Fig 1 implements the above"


@subsection[#:tag "sec:natural:implementation"]{Implementation}

@; concrete examples ... ???

The natural embedding defined in @figure-ref{fig:natural-reduction} adds
 one new value form, two functions for checking values at boundary terms,
 and two reduction rules to handle the new value form.
The new value form, @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}, is a monitor
 that associates a value @${v} with a type.
Such monitors arise at runtime as the result of calls to the @${\vfromdyn}
 and @${\vfromsta} conversion functions.

@;In principle, the one monitor value @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}
@; could be split into two value forms: one for protecting the domain of a statically-typed
@; function and one for checking the range of a dynamically-typed function.
@;The split would clarify @${\rrNS} and @${\rrND} but it would also create a
@; larger gap between the model and implementation (@secref{sec:implementation}).

The purpose of @${\efromdyn{\tau}{v}} is to import a dynamically-typed value
 into a statically-typed context, such that the result matches the assumptions
 of the context.
If @${\tau} is a base type, then @${\efromdyn{\tau}{v}} returns @${v} if the
 value matches the type and raises a boundary error otherwise.
If @${\tau} is a product type, then @${\efromdyn{\tau}{v}} asserts that @${v}
 is a pair value and returns a pair expression to import the components of the
 pair at the appropriate type.
Finally if @${\tau} is a function type, then @${\efromdyn{\tau}{v}} asserts
 that @${v} is a function (or a monitored function) and wraps @${v} in a monitor.

The purpose of @${\efromsta{\tau}{v}} is to import a statically-typed value
 into a dynamically-typed context such that context cannot break any assumption
 made by the value.
Integers and natural numbers do not interact with their context, thus
 @${\efromsta{\tint}{v}} returns the given value.
Pair values may indirectly interact with the context via their components,
 so @${\efromsta{\tpair{\tau_0}{\tau_1}}{v}} returns a pair expression to import
 the components.
Function values interact with their context by receiving arguments, and so
 @${\efromdyn{\tarr{\tau_d}{\tau_c}}{v}} wraps the function @${v} in a monitor
 to protect it from dynamically-typed arguments.

The notion of reduction @${\rrNS} adds a rule for applying a monitor as a function
 in a typed context.
The rule is to export the argument value to an untyped context and import the result
 back into typed code.
The ``export'' and ``import'' are implemented with boundary terms.
Conversely, the notion of reduction @${\rrND} adds a rule for applying a monitor
 in an untyped context.
In this case the conversion strategy is dual:
 convert the argument to typed, convert the result back to untyped.

These notions of reduction assume that all monitors in statically-typed contexts
 contain dynamically-typed values, and that all monitors in dynamically-typed
 contexts contain statically-typed values.
@Figure-ref{fig:natural-property} captures this requirement by extending the
 basic typing judgments for the evaluation syntax (@figure-ref{fig:multi-preservation})
 with appropriate rules for monitors.

The final components in @figure-ref{fig:natural-reduction} define a reduction
 relation @${\ccNE} for evaluation contexts and take the reflexive, transitive
 closure of this relation.
These define the operational semantics of an expression @${e}; a single step
 finds the innermost boundary term in @${e} and advances it.
If the innermost boundary has the form @${(\esta{\tau}{e'})} then @${\ccNE}
 either uses @${\rrNS} to step @${e'} or @${\vfromsta} to cross the boundary.
If the innermost boundary has the form @${(\edyn{\tau}{e'})} then @${\ccNE}
 either uses @${\rrNS} or @${\vfromdyn} to advance.

@subsection[#:tag "sec:natural:soundness"]{Soundness}

The soundness theorems for the natural embedding state two results about the
 possible outcomes of evaluating a well-typed surface language term.
First, the evaluation of a (terminating) statically-typed expression ends
 in either a well-typed value, a boundary error, or a tag error in dynamically-typed code.
Second, dynamically-typed code cannot exhibit undefined behavior.
More formally:

@twocolumn[
  @tr-theorem[#:key "N-static-soundness" @elem{static @${\mathbf{N}}-soundness}]{
    If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
      @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrND \tagerror} }
      @item{ @${e \rrNSstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "N-dynamic-soundness" @elem{dynamic @${\mathbf{N}}-soundness}]{
    If @${\wellM e} then @${\wellNE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrNDstar v \mbox{ and } \wellNE v} }
      @item{ @${e \rrNDstar \tagerror} }
      @item{ @${e \rrNDstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }
]

The theorems follow from standard progress and preservation lemmas
 for each reduction relation and the corresponding
 property judgment.
See the appendix for proofs.

The central lemmas that connect this pair of theorems are a specification for
 the @${\vfromdyn} and @${\vfromsta} functions:

@twocolumn[
  @tr-lemma[#:key "N-D-soundness" @elem{@${\vfromdyn} soundness}]{
    If @${\Gamma \wellNE v} and @${\efromdyn{\tau}{v} = e} then @${\Gamma \wellNE e : \tau}
  }

  @tr-lemma[#:key "N-S-soundness" @elem{@${\vfromsta} soundness}]{
    If @${\Gamma \wellNE v : \tau} and @${\efromsta{\tau}{v} = e} then @${\Gamma \wellNE e}
  }
]

@; Any choice of S/D that satisfies these theorems is probably OK for soundness

In other words, the implementations of @${\vfromdyn} and @${\vfromsta} establish
 an invariant about monitors occurring in dynamic and static contexts.
Every monitor in dynamically-typed code encapsulates a typed value,
 and every monitor in statically-typed code encapsulates an untyped value.

The soundness guarantee for the natural embedding is very strong.
@; with blame, TypeError at runtime is at least debuggable
One goal of soundness is to eliminate a class of errors.
The natural embedding eliminates tag errors in typed code.
It cannot eliminate boundary errors, but it brings them under control in a
 useful way.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:erasure-embedding"]{Erasure Embedding}
@include-figure["fig:erasure-reduction.tex" "Erasure Embedding"]
@include-figure["fig:erasure-preservation.tex" "Property judgments for the erasure embedding"]

@subsection[#:tag "sec:erasure:overview"]{Overview}

A second approach to migratory typing is to define soundness
 for the pair of languages as the soundness of the dynamically-typed
 host language.
@; so unclear
Instead of designing two notions of reduction and converting values at
 boundary terms, the erasure embedding comes with one notion of reduction.

@; omg this repeats the intro
From the programmers' perspective, erased types can catch static errors
 and enable tools like type-directed autocomplete.
Erased types have no relation to the semantics of a program.
For example, if an expression has the static type @${\tnat} then might
 reduce to a natural number, a negative integer, a pair, or a function.


@subsection[#:tag "sec:erasure:implementation"]{Implementation}

To implement the erasure embedding, it suffices to ignore type annotations
 and boundary terms in the surface language.
The notion of reduction @${\rrEE} in @figure-ref{fig:erasure-reduction}
 implements this idea by extending the dynamically-typed notion of reduction
 with two rule to let any value cross a boundary term and one rule to reduce
 the application of a statically-typed function to the application of a dynamically-typed
 function.
The reduction relation @${\rrEEstar} is the standard context closure of
 this notion of reduction.

The judgment in @figure-ref{fig:erasure-preservation} describes well-formed
 evaluation syntax terms.
Just like the notion of reduction, it extends a dynamically typed judgment
 with rules that ignore type annotations.


@subsection[#:tag "sec:erasure:soundness"]{Soundness}

The erasure embedding treats typed code as untyped code.
Consequently, erasure soundness for the pair of language is their lowest common
 denominator --- well-typed programs have well-defined behavior.

@twocolumn[
  @tr-theorem[#:key "E-static-soundness" @elem{static @${\mathbf{E}}-soundness}]{
    If @${\wellM e : \tau} then @${\wellEE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
      @item{ @${e \rrEEstar \tagerror} }
      @item{ @${e \rrEEstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "E-dynamic-soundness" @elem{dynamic @${\mathbf{E}}-soundness}]{
    If @${\wellM e} then @${\wellEE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
      @item{ @${e \rrEEstar \tagerror} }
      @item{ @${e \rrEEstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }
]

The proof follows from progress and preservation lemmas for the
 @${\wellEE} judgment and the @${\rrEEstar} reduction relation.
It is a weak theorem with a straightforward proof.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:locally-defensive-embedding"]{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-reduction.tex" "Locally-Defensive Embedding"]
@include-figure*["fig:locally-defensive-preservation.tex" "Property judgments for the locally-defensive embedding"]

@; The key insight is to pick a sufficiently weak notion of soundness@~cite[vss-popl-2017].

@subsection[#:tag "sec:locally-defensive:overview"]{Overview}

A third approach to soundness is to check only type constructors.
This approach needs significant motivation.
Who knows what we might eventually say here.

Checking only constructors radically changes the boundaries in a program.
See the diagram in fig N.
Unsafe to run with static notion of reduction, because of false assumptions.
Can fix by changing notion of reduction; this is probably inefficient.
A second fix is to monitor values, see the forgetful final embedding in the
 appendix, but monitors cost allocation.
Another fix, rewrite typed code to defend itself.

Do rewriting with a type-directed completion function.
In the spirit of Henglein
Produce an expression that is sure to have the right constructor given inputs
 of the right constructor.
@; static analysis, look for "maybe bad", just elimination forms


@subsection[#:tag "sec:locally-defensive:implementation"]{Implementation}

@Figure-ref{fig:locally-defensive-reduction} 

Constructors @${K} represent integers, natural numbers, pairs, functions,
 and unknown values.

The meta-function @${\tagof{\cdot}} relates a type @${\tau} to a constructor,
 and the subtyping relation @${K \subt K'} states when values of tag @${K}
 can safely be given to a context expecting values with a different tag.

Very important, dynamically-typed arguments
 to typed functions get tag-checked by the @${\mchk{K}{\cdot}} meta-function.
To prove that type-tag errors only
 occur in dynamically-typed code, we add the ``dummy'' boundary
 expressions @${(\edynfake{e})} and @${(\estafake{e})}.



@subsection[#:tag "sec:locally-defensive:soundness"]{Soundness}


@twocolumn[
  @tr-theorem[#:key "K-static-soundness" @elem{static @${\mathbf{K}}-soundness}]{
    If @${\wellM e : \tau} then 
    @${\wellM e : \tau \carrow e''}
    and @${\wellKE e'' : \tagof{\tau}}
    @linebreak[]
    and one of the following holds:
    @itemlist[
      @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
      @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
      @item{ @${e'' \rrKSstar \boundaryerror} }
      @item{ @${e''} diverges }
    ]
  }

  @tr-theorem[#:key "K-dynamic-soundness" @elem{dynamic @${\mathbf{K}}-soundness}]{
    If @${\wellM e : \tau} then 
    @${\wellM e \carrow e''}
    and @${\wellKE e''}
    @linebreak[]
    and one of the following holds:
    @itemlist[
      @item{ @${e'' \rrKDstar v} and @${\wellKE v : \tagof{\tau}} }
      @item{ @${e'' \rrKDstar \tagerror} }
      @item{ @${e'' \rrKDstar \boundaryerror} }
      @item{ @${e''} diverges }
    ]
  }
]



@;@section{Discussion}
@;
@;The performance overhead of the natural embedding comes from three sources:
@;  checking, indirection, and allocation.
@;By @emph{checking}, we refer to the cost of validating a type-tag and recursively
@; validating the components of a structured value.
@;For example, checking a list structure built from @${N} pair values requires
@; (at least) @${2N} recursive calls.
@;Function monitors add an @emph{indirection} cost.
@;Every call to a monitored function incurs one additional boundary-crossing.
@;If a value repeatedly crosses boundary terms, these type-checking layers
@; can accumulate without bound.@note{In a language with a JIT compiler,
@;  indirection may also affect inlining decisions.
@;  @; TODO does Spenser's work validate this?
@;  }
@;Finally, the @emph{allocation} cost of building a monitor value
@; also adds to the performance overhead.
@;
