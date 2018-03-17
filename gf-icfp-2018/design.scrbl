#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma tr-definition tr-proof tr-and UID++)]
@(void (UID++) (UID++))
@title[#:tag "sec:design"]{Logic and Metatheory}

@; thesis: these models reflect the 3 modes from life

@; -----------------------------------------------------------------------------

The three approaches to migratory typing can be understood as three
 semantics for @emph{embedding} dynamically-typed expressions in
 statically-typed contexts, and vice-versa.
Eagerly enforcing types corresponds to a @emph{natural}
 type-directed embedding@~cite[mf-toplas-2007].
Ignoring types corresponds to an @emph{erasure} embedding.
The transient approach of @citet[vss-popl-2017] is
 a @emph{locally-defensive} embedding.@note{@Section-ref{sec:related-work:locally-defensive}
 contrasts the names @emph{locally-defensive} and @emph{transient}.
 In short, the latter obscures a meaningful distinction.}

This section begins with the introduction of the surface syntax and typing system (@section-ref{sec:common-syntax}).
It then defines three embeddings, states their soundness theorems (@Sections-ref{sec:natural-embedding}, @secref{sec:erasure-embedding}, and @secref{sec:locally-defensive-embedding}),
 and concludes with a discussion on scaling the models to a practical implementation (@section-ref{sec:practical-semantics}).
Each embedding builds upon a common semantic framework (@section-ref{sec:common-semantics})
 to keep the technical presentation focused on their differences.
Unabridged definitions are in the appendix@~cite[gf-tr-2018].


@; -----------------------------------------------------------------------------
@section[#:tag "sec:common-syntax"]{Common Syntactic Notions}

A migratory typing system extends a dynamically-typed @mytech{host language}
 with syntax for type annotations and for declaring parts of the
 program as statically typed.
The type checker for the extended language must be able to validate mixed-typed
 programs, and the semantics must define a protocol for transporting
 values across the boundaries between typed and untyped contexts.

Regarding the semantics of boundary terms, the essential questions
 are how to enforce three kinds of types: base types, inductive types, and
 higher types.
The surface language presented in @figure-ref{fig:multi-syntax} is therefore
 a functional language with integers and pairs.
Types in this language represent integers, pairs, functions, and natural numbers.
Of these, the first three types serve as example base, inductive, and higher types.
The last type, @${\tnat}, is a subset of the type of integers; it is included
 to illustrate the set-based reasoning that dynamically-typed languages
 support via (true) union types.

An expression in the surface language may be dynamically typed (@${\exprdyn})
 or statically typed (@${\exprsta}).
Naturally, these grammars are nearly identical.
The main difference is that a statically-typed
 function must provide a type annotation for its formal parameter.
The second, minor difference is that both grammars include a different kind
 of @emph{boundary term} for embedding an expression of the other grammar.
The expression @${(\edyn{\tau}{\exprdyn})} embeds a dynamically-typed subexpression in a
 statically-typed context, and the expression @${(\esta{\tau}{\exprsta})} embeds a
 statically-typed subexpression in a dynamically-typed context.

The last components in @figure-ref{fig:multi-syntax} are the names of
 primitives.
The primitives in @${\vunop} and @${\vbinop} represent low-level procedures that
 compute in terms of bitstrings rather than abstract syntax.
For example, invoking the @${\vsum} procedure with arguments that are not
 integers is undefined behavior.

@include-figure["fig:multi-syntax.tex" @elem{Twin languages syntax}]
@include-figure["fig:multi-preservation.tex" @elem{Twin languages static typing judgments}]

@Figure-ref{fig:multi-preservation} presents a relatively straightforward typing
 system for the complete syntax, augmented with error terms.
To accomodate the two kinds of expressions, there are two typing judgments.
The first judgment, @${\Gamma \wellM \exprdyn}, essentially states that the
 expression @${e} is closed; this weak property characterizes the ahead-of-time
 checking common to dynamically-typed languages.
The second judgment, @${\Gamma \wellM \exprsta : \tau}, is a mostly-conventional static
 type checker; given an expression and a type, the judgment holds if the two match up.
The unconvential part of both judgments are the mutually-recursive rules for boundary terms,
 which invoke the opposite judgment on their subexpressions.
For example, @${\Gamma \wellM \esta{\tau}{\exprsta}} holds only if the enclosed expression
 matches the @${\tau} type.

The defined errors are of two types.
A boundary error may occur when one ``language'' sends a bad value to another;
 such an error can arise between a typed context and an untyped subexpression,
 or between a surface-language expression and the implicit language that
 implements the primitives.
A tag error may occur when the evaluation of an expression reaches a
 malformed state.

Two auxiliary components of the type system are the function @${\Delta},
 which assigns a type to the primitives, and a subtyping
 judgment based on the subset relation between natural numbers and integers.
Subtyping adds a logical distinction to the type system that is not automatically
 enforced by the untyped host language.
For example, the expression @${(\equotient{x}{y})}
 may compute a nonsensical result if @${x} and @${y} are expected to have type
 @${\tnat} but evaluate to negative integers.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:common-semantics"]{Common Semantic Notions}

Our semantic models use the Matthews-Findler multi-language approach@~cite[mf-toplas-2007].
Specifically, the semantics consists of two reduction relations, one for statically-typed
 expressions and one for dynamically-typed ones.
The set-up easily permits separate definitions for interconnecting the reduction relation
 and then modeling the common approaches.

Precisely put, the two reduction relations (@${\rrSstar} and @${\rrDstar}) must satisfy:
@; the following criteria:
@itemlist[
@item{
  @emph{soundness for a single language}: for expressions without boundary
   terms, both typing judgments in @figure-ref{fig:multi-preservation} are sound
   with respect to the matching reduction relation;
}
@item{
  @emph{expressive boundary terms}: the static and dynamic contexts can
   share values at any type; and
   @;more formally, for any type @${\tau} there must
   @;be at least four values such that @${(\edyn{\tau}{v_d}) \rrSstar v} and
   @;@${(\esta{\tau}{v_s}) \rrDstar v'};
}
@item{
  @emph{soundness for the pair of languages}: for all expressions,
   evaluation preserves some property that is implied by the surface notion of typing,
   but it is neither the same nor necessarily a straightforward generalization.
}
]
To streamline the definitions of the three multi-language semantics that follow,
 @figure-ref{fig:multi-reduction} introduces common semantic notions.
The syntactic components of this figure are expressions @${e},
 values @${v}, irreducible results @${R},
 and two kinds of evaluation context: @${\ebase} and @${\esd}.
A core context @${\ebase} does not contain boundary terms and a multi-language
 context @${\esd} may contain boundaries.

The semantic components in @figure-ref{fig:multi-reduction} are the @${\delta}
 function and the @${\rrS} and @${\rrD} notions of reduction for the core subsets of the two kinds of expressions.
The @${\delta} function is a partial mathematical specification for the
 procedures in @${\vunop} and @${\vbinop}.
It is undefined for certain arguments---to represent
 low-level undefined behavior---and raises a boundary error @${(\boundaryerror)}
 for division by zero.

The notion of reduction @${\rrS} defines a semantics for statically-typed expressions.
It relates the left-hand side to the right-hand side on an unconditional basis,
 which expresses the reliance on the type system to prevent stuck terms up
 front.
The notion of reduction @${\rrD} defines a semantics for dynamically-typed expressions.
A dynamically-typed expression may attempt to apply an integer to an argument or give
 nonsensical arguments to a primitive, hence @${\rrD} explicitly checks for
 malformed expressions and raises a tag error @${(\tagerror)} as indication that
 an @mytech{elimination form} received a value of incorrect shape.

@; maybe make this more structured? finish the draft first tho
@; ... maybe less structure, because erasure doesn't really match

The three models in the following sections build upon @figure-ref{fig:multi-reduction}.
Two of them
 define functions @${\vfromdyn} and @${\vfromsta} for transporting a value across a boundary term,
 extend the @${\rrS} and @${\rrD} notions of reduction,
 and lift the notions of reduction to reduction relations @${\rrSstar} and
 @${\rrDstar} for (multi-language) evaluation contexts.
The other model defines one reduction relation.
Lastly, the models define a (two-part) syntactic property that is
 implied by a typing property in @figure-ref{fig:multi-preservation},
 and comes with a proof that the property is sound with respect to the
 corresponding reduction relation.

@; TODO revise the above!!!

@include-figure["fig:multi-reduction.tex" @elem{Common semantic notions}]


@; -----------------------------------------------------------------------------
@section[#:tag "sec:natural-embedding"]{Natural Embedding}
@include-figure*["fig:natural-reduction.tex" "Natural Embedding"]
@include-figure*["fig:natural-preservation.tex" "Property judgments for the natural embedding"]

@; types should provide strong guarantees
@; "levels of abstraction" is a quote from J. Reynolds

The natural embedding@~cite[mf-toplas-2007] is based on the idea that types should enforce levels
 of abstraction.
In a conventional typed language, this kind of enforcement happens statically;
 types define levels of abstraction and the type checker ensures compliance.
Migratory typing can provide a similar guarantee if the type specifications for untyped
 values are checked at runtime.

The natural embedding uses a type-directed strategy to @mytech{transport} a value across
 a boundary between typed and untyped code.
If the value is untyped and entering a context that expects
 a value of a base type, such as @${\tint} or @${\tnat},
 then the strategy is to check the value against the type constructor.
If the context expects a value of an inductive type, such as @${(\tpair{\tint}{\tint})},
 then the strategy is to the check the constructor and recursively transport
 the components of the value.
Lastly, if the context expects a value of a higher type, such as
 @${(\tarr{\tnat}{\tnat})}, then the strategy is to check the constructor and
 monitor the future interactions between the value and the context.
For the specific case of an untyped function @${f} and the type @${(\tarr{\tnat}{\tnat})},
 the natural embedding transports a wrapped version of @${f} across the boundary.
The wrapper checks that every result computed by @${f} is of type @${\tnat}
 and otherwise halts the program with a witness that @${f} does not match the type.


@subsection[#:tag "sec:natural:model"]{Model}

@Figure-ref{fig:natural-reduction} presents a model of the natural embedding.
The centerpiece of the model is the pair of @mytech{boundary functions}:
 @${\vfromdynN} and @${\vfromstaN}.
The @${\vfromdynN} function imports a dynamically-typed value into a statically-typed
 context by checking the shape of the value and proceeding as outlined above.
In particular, the strategy for transporting an untyped value @${v} into a
 context expecting a function with domain @${\tau_d} and codomain @${\tau_c}
 is to check that @${v} is a function and wrap it in a monitor @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}.
Conversely, the @${\vfromstaN} function exports a typed value to an untyped context.
It transports an integer as-is, transports a pair recursively,
 and wraps a function in a monitor to protect the typed function against untyped arguments.

The extended notions of reduction in @figure-ref{fig:natural-reduction} define the complete semantics of monitor application.
In a statically-typed context, applying a monitor means applying a
 dynamically-typed function to a typed argument.
Thus the semantics unfolds the monitor into two boundary terms:
 a @${\vdyn} boundary in which to apply the dynamically-typed function
 and an inner @${\vsta} boundary to transport the argument.
In a dynamically-typed context, a monitor encapsulates a typed function and
 application unfolds into two dual boundary terms.

The boundary functions and the notions of reductions come together
 to define the semantics of mixed-typed expressions.
There are two main reduction relations: @${\rrNSstar} for typed expressions
 and @${\rrNDstar} for untyped expressions.
The difference is how they act on an expression that
 does not contain boundary terms.
The typed reduction relation steps via @${\rrS} by default, and the
 untyped relation steps via @${\rrD} by default.
For other cases, the relations are identical.

@;In principle, the one monitor value @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}
@; could be split into two value forms: one for protecting the domain of a statically-typed
@; function and one for checking the range of a dynamically-typed function.
@;The split would clarify @${\rrNS} and @${\rrND} but it would also create a
@; larger gap between the model and MODEL (@section-ref{sec:implementation}).


@subsection[#:tag "sec:natural:soundness"]{Soundness}

@Figure-ref{fig:natural-preservation} presents two properties for the natural
 embedding evaluation syntax: one for dynamically-typed expressions and one
 for statically-typed expressions.
Each property extends the corresponding judgment from @figure-ref{fig:multi-preservation}
 with a rule for monitors.
The property for dynamic expressions (in the left column) states that a
 typed value may be wrapped in a monitor of the same type.
The static property states that any untyped value may be wrapped in a monitor,
 and that the monitor is assumed to follow its type annotation.

The soundness theorems for the natural embedding state three results about
 surface-language expressions:
 (1) reduction is fully defined, (2) reduction in a statically-typed context
 cannot raise a tag error, and (3) reduction preserves the properties from
 @figure-ref{fig:natural-preservation}.

@twocolumn[
  @tr-theorem[#:key "N-static-soundness" @elem{static @${\langN}-soundness}]{
    If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
      @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrND \tagerror} }
      @item{ @${e \rrNSstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "N-dynamic-soundness" @elem{dynamic @${\langN}-soundness}]{
    If @${\wellM e} then @${\wellNE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrNDstar v \mbox{ and } \wellNE v} }
      @item{ @${e \rrNDstar \tagerror} }
      @item{ @${e \rrNDstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }@;
]@tr-proof[#:sketch? #true]{
  First, @${\wellM e : \tau} implies @${\wellNE e : \tau} because the latter
   judgment generalizes the former.
  A similar lemma holds for the dynamic typing judgment.
  The other statements in the two theorems follow from progress and
   preservation lemmas for the corresponding property and reduction
   relation@~cite[gf-tr-2018].
}

The proof of preservation depends on a notable lemma about the @${\vfromdynN}
 boundary function, namely, that its codomain is typed.

@tr-lemma[#:key "N-D-soundness" @elem{@${\vfromdynN} soundness}]{
  If @${\Gamma \wellNE v} and @${\efromdynN{\tau}{v} = e} then @${\Gamma \wellNE e : \tau}
}@;
@;
A similar lemma does not hold of the surface-language typing judgment.
The proof breaks down when @${\tau} is a function type, and thereby demonstrates
 a key tradeoff in migratory typing.
If the language is to allow values of higher type to cross a boundary,
 then it must generalize its soundness guarantee.
 @; to consider such values well-typed until proven otherwise.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:erasure-embedding"]{Erasure Embedding}
@include-figure["fig:erasure-reduction.tex" "Erasure Embedding"]
@include-figure["fig:erasure-preservation.tex" "Property judgments for the erasure embedding"]

@; types should not affect semantics.
@; "syntactic discipline" is a quote from J. Reynolds

An erasure embedding, also known as optional typing, is based on a view of
 types as an optional syntactic artifact.
Types are just a structured kind of comment and should be irrelevant for the
 evaluation of programs.
Their main purpose is to help developers read a codebase.
Their secondary purpose is to enable static type checking and to guide refactoring tools.
Whether the types are sound is incidental.
 @; , since type soundness never holds for the entirety of a practical language.

If one adopts this point of view, then the proper semantics for a migratory
 typing system is an extension of the host language's untyped semantics that ignores type annotations.
Any value may freely cross any type boundary.
The embedding uses the reductionist approach of relying on the soundness of the
 host language.


@subsection[#:tag "sec:erasure:model"]{Model}

@Figure-ref{fig:erasure-reduction} presents a semantics of the erasure embedding.
The notion of reduction @${\rrEE} defines rules for boundary
 terms and type-annotated functions, and otherwise relies on the dynamically-typed
 notion of reduction from @figure-ref{fig:multi-reduction}.
The reduction relation @${\rrEEstar} is based on the context closure of
 this notion of reduction.


@subsection[#:tag "sec:erasure:soundness"]{Soundness}

@Figure-ref{fig:erasure-preservation} extends the judgment for a well-formed
 dynamically-typed expression to accomodate type-annotated expressions.
This judgment ignores the type annotations; for any expression @${e}, the
 judgment @${\wellEE e} holds if @${e} is closed.

Soundness for the erasure embedding states that reduction is well-defined
 for statically-typed and dynamically-typed expressions.

@twocolumn[
  @tr-theorem[#:key "E-static-soundness" @elem{static @${\langE}-soundness}]{
    If @${\wellM e : \tau} then @${\wellEE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
      @item{ @${e \rrEEstar \tagerror} }
      @item{ @${e \rrEEstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "E-dynamic-soundness" @elem{dynamic @${\langE}-soundness}]{
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

@tr-proof[#:sketch? #true]{
  A well-typed term is closed, therefore @${\wellM e : \tau} implies that @${\wellEE e} holds.
  The statements about @${\rrEEstar} follow from progress and preservation lemmas@~cite[gf-tr-2018].
}

The erasure embedding is clearly unsound with respect to types for mixed-typed
 expressions.
A simple example is the expression @${(\edyn{\tint}{\vpair{2}{2}})}, which has the static
 type @${\tint} but reduces to a pair.
The embedding is sound, however, for well-typed expressions that do not
 contain boundary terms.

@tr-theorem[#:key "E-pure-static" @elem{@${\langE} boundary-free soundness}]{
  If @${\wellM e : \tau} and @${e} has the form @${\ebase[e']}, then 
   one of the following holds:
  @itemlist[
    @item{ @${e \rrEEstar v \mbox{ and } \wellM v : \tau} }
    @item{ @${e \rrEEstar \boundaryerror} }
    @item{ @${e} diverges}
  ]
}
@tr-proof[#:sketch? #true]{
  By standard progress and preservation lemmas.
  Intuitively, this theorem holds because every subexpression of @${e} is statically typed.
}


@; -----------------------------------------------------------------------------
@section[#:tag "sec:locally-defensive-embedding"]{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-reduction.tex" "Locally-Defensive Embedding"]

@; types should prevent logical stuck-ness

The locally-defensive approach is the result of two assumptions, one philosophical,
 one pragmatic.
The philosophical assumption is that the purpose of types is to prevent evaluation
 from ``going wrong'' in the sense of applying a typed elimination form to a value
 outside its domain.
For example, the elimination forms in the surface
 language are function application and primitive application.
Function application @${(\eapp{v_0}{v_1})} expects that @${v_0} is a function;
 primitive application expects arguments for which @${\delta}
 is defined.
The goal of the locally-defensive semantics is to ensure that such assumptions
 are always satisfied in typed contexts.
@; ... what about Nat? ... generalized form of tag error

The pragmatic assumption is that run-time monitoring, like that employed in
 the natural embedding, is impractical.
For one, implementing monitors requires a significant engineering effort.
Such monitors must preserve all the observations that dynamically-typed code
 can make of the original value, including object-identity tests.
@; TODO treatJS ? also cite chaperones, TS*, Retic
Second, monitoring adds a prohibitive run-time cost.

Based on these assumptions, the locally-defensive semantics employs a type-driven
 rewriting pass on typed code to defend against untyped inputs.
The defense takes the form of type-constructor checks; for example,
 if a typed context expects a value of type @${(\tarr{\tnat}{\tnat})} then a
 run-time check asserts that the context receives a function.
If this function is applied @emph{in the same context}, then a second run-time
 check confirms that the result is a natural number.
If the same function is applied @emph{in a different typed context} that expects a
 result of type @${(\tpair{\tint}{\tint})}, then a run-time check confirms that
 the result is a pair.

Constructor checks do not require monitors,
 they run in near-constant time,
 and they ensure that every value in a typed context has the correct top-level shape.
If the core notions of reduction rely only on the top-level shape of a value,
 then the latter guarantee implies that well-typed programs do not ``go wrong''
 as desired.
@; or rather, "do not apply a typed elimination form to a value outside its domain" ?


@subsection[#:tag "sec:locally-defensive:model"]{Model}

@Figure-ref{fig:locally-defensive-reduction} presents a model of the
 locally-defensive approach.
The model represents a defensive type-constructor check as a @${\vchk} expression;
 intuitively, the semantics of @${(\echk{K}{e})} is to reduce @${e} to a value
 and affirm that it matches the @${K} type constructor.
Type constructors @${K} include one constructor @${\tagof{\tau}} for each
 kind of type @${\tau}, and the technical @${\kany} constructor, which
 does not correspond to a static type.

The purpose of @${\kany} is to reflect the weak invariants of the locally-defensive
 semantics.
In contrast to types @${\tau}, type constructors say nothing about the
 contents of a structured value.
The first and second components of a generic @${\kpair} value can have any shape,
 and the result of applying a function of constructor @${\kfun} can be any
 value.@note{Since the direct result of function application is an expression,
  the model includes the ``no-op'' boundary term @${(\edynfake{e})}
  to support the application of an untyped function in a typed context.
  The @${(\estafake{e})} boundary serves a dual purpose. The two forms facilitate
  the proofs of the progress and preservation lemmas.}
Put another way, the @${\kany} constructor is necessary because information about
 type constructors does not compose under the algebra of expressions.

@; TODO more parallel structure with the previous paragraph?
In the context of the model, the above-mentioned type-driven rewriting pass corresponds
 to the judgment @${\Gamma \vdash e : \tau \carrow e'}, which states that @${e'}
 is the checked @emph{completion}@~cite[h-scp-1994] of the surface language expression.
The rewritten expression @${e'} includes @${\vchk} forms around three kinds of typed
 expressions: function application, @${\vfst} projection, and @${\vsnd} projection.
For any other expression, the result is constructed by structural recursion.

The semantics ensures that every expression of type
 @${\tau} reduces to a value that matches the @${\tagof{\tau}} (type) constructor.
The boundary function @${\vfromdynK} checks that an untyped value
 entering typed code matches the type constructor of the expected type.
This function defers to a more general function @${\vfromany}, which checks
 that a given value of constructor @${\kany} matches a more precise type constructor.
The boundary function @${\vfromstaK} lets any kind of typed
 value---including typed fuctions---cross into an untyped context.
The notions of reduction consequently treat the type annotation @${\tau} on
 the formal parameter of a typed function @${(\vlam{\tann{x}{\tau}}{e})}
 as an assertion that its actual parameters match the constructor @${\tagof{\tau}}.@note{Design alternatives:
  extend the syntax of the core language to express domain checks@~cite[vss-popl-2017],
  or encode domain checks into the completion of a typed function in the spirit of
    @${(\vlam{\tann{x}{\tau_d}}{e}) \carrow
       (\vlam{\tann{x}{\tau_d}}{(\eapp{(\eapp{(\vlam{y}{\vlam{z}{z}})}{(\echk{\tagof{\tau_d}}{x})})}{e})})}
  }
In order to protect a typed function in an untyped context, the @${\rrKD}
 notion of reduction includes rules that check the constructor of an untyped
 argument to a typed function.
The static @${\rrKS} notion of reduction includes similar rules to protect typed
 functions against @emph{typed} arguments.
This protection is necessary for typed functions that return from an untyped context,
 because a static--dynamic--static round trip is essentially a type cast.
The following well-typed example applies an integer function to a pair:

@dbend[
  @warning{
    \wellM (\eapp{(\esta{(\tarr{\tpair{\tint}{\tint}}{\tint})}{(\edyn{(\tarr{\tint}{\tint})}{(\vlam{\tann{x}{\tint}}{\esum{x}{x}})})})}{\vpair{0}{0}}) : \tint
  }
]

@exact{\noindent}The remaining rules of @${\rrKS} give semantics to the application of an
 untyped function and to the @${\vchk} type-constructor checks.

Finally, the @${\rrKSstar} and @${\rrKDstar} reduction relations define
 a multi-language semantics for the model.
These relations are similar to those of the natural embedding, though they include
 no-op transitions to let values cross unannotated boundary terms.


@subsection[#:tag "sec:locally-defensive:soundness"]{Soundness}

@Figure-ref{fig:locally-defensive-preservation} presents two judgments that express
 the invariants of the locally-defensive reductions.
The first judgment, @${\Gamma \wellKE e}, holds for closed untyped
 expressions.
The second judgment is a constructor-typing system that formalizes the intuitions stated above.
In particular,
 the value of a typed variable is guaranteed to match its type constructor,
 the @${\vfst} projection can produce any kind of value,
 and the result of a @${\vchk} expression matches the
 given constructor.

Soundness for the locally-defensive embedding is a statement about the completion
 of a surface-language expression.
Intuitively, the reduction of any defended expression is well-defined and
 furthermore reduction in any typed context cannot raise a tag error.

@include-figure*["fig:locally-defensive-preservation.tex" "Property judgments for the locally-defensive embedding"]

@twocolumn[
  @tr-theorem[#:key "K-static-soundness" @elem{static @${\langK}-soundness}]{
    If @${\wellM e : \tau} then
    @${\wellM e : \tau \carrow e''}
    and @${\wellKE e'' : \tagof{\tau}}
    @linebreak[]
    and one of the following holds:
    @itemlist[
      @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
      @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @${e' \rrKD \tagerror} }
      @item{ @${e'' \rrKSstar \boundaryerror} }
      @item{ @${e''} diverges }
    ]
  }

  @tr-theorem[#:key "K-dynamic-soundness" @elem{dynamic @${\langK}-soundness}]{
    If @${\wellM e} then
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
@tr-proof[#:sketch? #true]{
  By standard progress and preservation arguments for the @${\wellKE} property.
}

@; --- completion lemmas
@;@twocolumn[
@;  @tr-lemma[#:key "K-S-completion" @elem{static @${\carrow} soundness}]{
@;    If @${\Gamma \wellM e : \tau} then
@;    @linebreak[]
@;    @${\Gamma \vdash e : \tau \carrow e'} and @${\Gamma \wellKE e' : \tagof{\tau}}
@;  }
@;
@;  @tr-lemma[#:key "K-D-completion" @elem{dynamic @${\carrow} soundness}]{
@;    If @${\Gamma \wellM e} then
@;    @linebreak[]
@;    @${\Gamma \wellM e \carrow e'} and @${\Gamma \wellKE e'}
@;  }
@;]

@; --- check lemma
@;@tr-lemma[#:key "K-check" @elem{@${\vfromany} soundness}]{
@;  If @${\mchk{K}{v} = v}
@;   @linebreak[]
@;   then @${\wellKE v : K}
@;}

@; --- boundary-free soundness
@;  @tr-theorem[#:key "E-pure-static" @elem{@${\langE} boundary-free soundness}]{
@;    If @${\wellM e : \tau} and @${e} does not contain a sub-term of the form
@;     @${(\edyn{\tau'}{e'})} then one of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrEEstar v \mbox{ and } \wellM v : \tau} }
@;      @item{ @${e \rrEEstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ]
@;  }


@section[#:tag "sec:practical-semantics"]{From Models to Implementations}

@; AKA threats to the validity of the models

@; TODO
@; - type-constructor checks suffice to prevent stuck-ness

By far the biggest gap between the models and implementations of migratory typing
 is visible in the natural and locally-defensive models.
These models use @emph{two} reductions, one for the typed and one for the untyped
 fragments of code.
By contrast, any practical migratory typing system compiles typed expressions to the
 (dynamically-typed) host language.
In terms of the models, this means @${\rrD} is the only core notion of reduction,
 and statically-typed expressions are rewritten so that @${\rrDstar} applies.
The technical appendix demonstratess how to bridge this gap systematically@~cite[gf-tr-2018].

@;To resolve this challenge, it suffices to build a reduction relation based on @${\rrD}
@; and conservatively guard @${\vsta} boundaries with the @${\vfromdyn} boundary
@; function.

Replacing the two notions of reduction with one raises a question
 about the performance of the host reduction relation on typed code.
In particular, the former reduction for statically-typed code could safely
 ignore the possibility of a tag error and use the more efficient @${\vfromsta}
 boundary function.
These performance losses may be (partially) recovered with a type-based, ahead-of-time optimizer.
One pass of the optimizer can mark applications of primitives in typed code
 so the evaluator knows they are safe from tag errors.
A second pass can simplify the types in boundary terms.
For every term of the form @${(\edyn{\tau}{e})}, it is safe to ignore
 first-order types in negative positions of @${\tau} because the enclosing typed context
 is statically known to respect such types.
For every term of the form @${(\esta{\tau}{e})}, it is safe to ignore
 first-order types in positive positions for the same reason.
As a concrete example, the expression @${(\esta{\tint}{e})} may be optimized
 to @${(\estafake{e})}, as soundness ensures that @${e} evaluates to a well-typed
 value.

A secondary semantic issue concerns the rules for the application of a typed
 function in the locally-defensive embedding.
As written, the @${\rrKD} notion of reduction implies a non-standard protocol
 for function application @${(\eapp{v_0}{v_1})}, namely:
 (1) check that @${v_0} is a function;
 (2) check whether @${v_0} was defined in typed code;
 (3) if so, then check @${v_1} against the static type of @${v_0}.
The conservative work-around is to extend the completion judgment to add a constructor-check
 to every typed function.
Using pseudo-syntax @${e_0;\,e_1} to represent sequencing, a suitable completion rule is:
@exact|{
  \begin{mathpar}
  \inferrule*{
    \tann{x}{\tau}, \Gamma \wellM e \carrow e'
  }{
    \Gamma \wellM \vlam{\tann{x}{\tau_d}}{e} \carrow \vlam{\tann{x}{\tau_d}}{\vchk{\tagof{\tau_d}}{x};\,e'}
  }
  \end{mathpar}
}|@;
Both Reticulated and our implementation of this semantics use a variant of this rule.

Lastly, the models do not mention union types, universal types,
 and recursive types---all of which are common tools for reasoning about
 dynamically-typed code.
To extend the natural embedding with support for these types, the language
 must add new kinds of monitors to enforce type soundness for their
 elimination forms (or lack thereof).
The literature on Typed Racket presents one strategy for handling such types@~cite[stff-oopsla-2012 tfdfftf-ecoop-2015].
To extend the locally-defensive embedding, the language must add unions @${K \cup K}
 to its grammar of constructor checks and must extend the @${\tagof{\cdot}} function.
For a union type, let @${\tagof{\tau_0 \cup \tau_1}} be @${\tagof{\tau_0} \cup \tagof{\tau_1}},
 i.e., the tags of its members.
For a universal type @${\tall{\alpha}{\tau}} let the constructor be @${\tagof{\tau}},
 and for a type variable let @${\tagof{\alpha}} be @${\kany} because there are
 no elimination forms for a universally-quantified type variable.
For a recursive type @${\trec{\alpha}{\tau}}, let the constructor be
 @${\tagof{\vsubst{\tau}{\alpha}{\trec{\alpha}{\tau}}}}; this definition is
 well-founded if all occurrences of the variable appear under some type
 @${\tau'} such that @${\tagof{\tau'}} has a non-recursive definition.

