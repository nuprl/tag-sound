#lang gf-icfp-2018
@require[(only-in "techreport.rkt" tr-theorem tr-lemma tr-definition tr-proof tr-and UID++)]
@(void (UID++) (UID++))
@title[#:tag "sec:design"]{Logic and Metatheory}

@; thesis: these models reflect the 3 modes from life

@; TODO
@; - define/explain "getting stuck", (a b) and (op1 a) and (op2 a b)

@; -----------------------------------------------------------------------------

The three approaches to migratory typing can be understood as three
 semantics for @emph{embedding} dynamically-typed expressions in
 statically-typed contexts, and vice-versa.
Eagerly enforcing types corresponds to a @emph{natural}@~cite[mf-toplas-2007]
 type-directed embedding.
Ignoring types corresponds to an @emph{erasure} embedding.
The transient approach of @citet[vss-popl-2017] is
 a @emph{locally-defensive} embedding.@note{@Secref{sec:related-work:locally-defensive}
 contrasts the names @emph{locally-defensive} and @emph{transient}.
 In short, the latter obscures a meaningful distinction.}

This section begins with the introduction of the surface syntax and typing system (@secref{sec:common-syntax}).
It then defines three embeddings and states their soundness theorems
 (@secref{sec:natural-embedding}, @secref{sec:erasure-embedding}, and @secref{sec:locally-defensive-embedding}).
Each embedding builds upon a common semantic framework (@secref{sec:common-semantics})
 to keep the technical presentation focused on their differences.
Unabridged definitions appear in the technical appendix@~cite[gf-tr-2018].


@; -----------------------------------------------------------------------------
@section[#:tag "sec:common-syntax"]{Common Syntactic Notions}

A migratory typing system extends a dynamically-typed @mytech{host language}
 with syntax for type annotations and for declaring parts of the
 program as statically typed.
The type checker for the extended language must be able to validate mixed-typed
 programs, and the semantics must define a protocol for transporting
 values across the boundaries between statically-typed and dynamically-typed contexts.

When it comes to the semantics of boundary terms, the essential questions
 are how to enforce three kinds of types: base types, inductive types, and
 coinductive types.
The surface language presented in @figure-ref{fig:multi-syntax} is therefore
 a functional language with integers and pairs.
Types @${\tau} in this language represent integers, pairs, functions, and natural numbers.
Of these, the first three types serve as example base, inductive, and coinductive types.
The last type, @${\tnat}, adds a logical distinction to the type system that
 is not automatically enforced by the host language; with this distinction,
 a program that avoids undefined behavior can still compute a nonsensical result
 if evaluation does not respect the types.
@; TODO nat is there to represent union types, and the naive set theory that untyped programers use !!!!!!!!!!!
@Secref{sec:implications} illustrates this point with concrete examples.

An expression in the surface language may be dynamically typed (@${\exprdyn})
 or statically typed (@${\exprsta}).
Naturally, these grammars are nearly identical.
The main difference between @${\exprdyn} and @${\exprsta} is that a statically-typed
 function must provide a type annotation for its formal parameter.
The second, minor difference is that both grammars include a different kind
 of @emph{boundary term} for embedding an expression of the other grammar.
The expression @${(\edyn{\tau}{e})} embeds a dynamically-typed expression in a
 statically-typed context, and the expression @${(\esta{\tau}{e})} embeds a
 statically-typed expression in a dynamically-typed context.

The last components in @figure-ref{fig:multi-syntax} are the names of
 primitives and possible run-time errors.
These primitives in @${\vunop} and @${\vbinop} represent low-level procedures that
 compute in terms of bitstrings rather than abstract syntax.
For example, invoking the @${\vsum} procedure with arguments that are not
 integers is undefined behavior.
The defined errors are of two types.
A boundary error may occur when one ``language'' sends a bad value to another;
 such an error can arise between typed and untyped parts of an expression,
 or between a surface-language expression and the implicit language that
 implements the primitives.
A tag error may occur during when an expression reaches a malformed state during
 evaluation.
@Secref{sec:common-semantics} gives concrete examples of these errors.

@include-figure["fig:multi-syntax.tex" @elem{Twin languages syntax}]
@include-figure["fig:multi-preservation.tex" @elem{Twin languages static typing judgments}]

@Figure-ref{fig:multi-preservation} presents a relatively straightforward typing
 system for the complete syntax.
To accomodate the two kinds of expressions (@${\exprsta} and @${\exprdyn}),
 there are two typing judgments.
The first judgment, @${\Gamma \wellM e}, essentially states that the expression @${e} is
 closed; this weak property characterizes the ahead-of-time checking
 common to dynamically-typed languages.
The second judgment, @${\Gamma \wellM e : \tau}, is a mostly-conventional static
 type checker; given an expression and a type, the judgment holds if the two match up.
The unconvential part of both judgments are the mutually-recursive rules for boundary terms,
 which invoke the opposite judgment on their sub-expression.
For example, @${\Gamma \wellM \esta{\tau}{e}} holds only if the enclosed expression
 is well-typed.

Two auxiliary components of the type system are the function @${\Delta},
 which assigns a (dependent) type to the primitives, and a subtyping
 judgment based on the subset relation between natural numbers and integers.
@; TODO point back to the thing about naive set theory!!!!


@; -----------------------------------------------------------------------------
@section[#:tag "sec:common-semantics"]{Common Semantic Notions}

@; TODO only 1 reduction for erasure!

An embedding defines a semantics for the surface language.
Since the typing system distinguishes two kinds of surface-language expression,
 it is convenient to define a semantics through two reduction relations:
 one for statically-typed code and one for dynamically-typed code.
This multi-language approach@~cite[mf-toplas-2007] simplifies the proofs of
 soundness and explains one role of type-driven optimizations in a practical
 migratory typing system (see @secref{sec:practical-semantics}).

Precisely put, the two reduction relations in an embedding (@${\rrSstar} and @${\rrDstar}) must satisfy:
@; the following criteria:
@itemlist[
@item{
  @emph{soundness for a single language}: for expressions without boundary
   terms, both typing judgments in @figure-ref{fig:multi-preservation} are sound
   with respect to the matching reduction relation;
}
@item{
  @emph{expressive boundary terms}: the static and dynamic contexts can
   share values at any type; more formally, for any type @${\tau} there must
   exist at least two values @${v_d} and @${v_s} such that @${(\edyn{\tau}{v_d}) \rrSstar v_s}
   (similarly for @${\vsta}); and
}
@item{
  @emph{soundness for the pair of languages}: for all expressions,
   evaluation preserves some property that is implied by the surface notion of typing.
}
]
To streamline the definitions of the three multi-language semantics that follow,
 @figure-ref{fig:multi-reduction} introduces common semantic notions.
The syntactic components of this figure are expressions @${e},
 irreducible results @${R}, and two kinds of evaluation context: @${\ebase} and
 @${\esd}.
A basic context @${\ebase} does not contain boundary terms; a multi-language
 context @${\esd} may contain boundaries.

The semantic components in @figure-ref{fig:multi-reduction} are the @${\delta}
 function for primitives and the @${\rrS} and @${\rrD} notions of reduction.
The @${\delta} function is a mathematical specification for the
 procedures in @${\vunop} and @${\vbinop}.
It is undefined for certain arguments---to represent
 low-level undefined behavior---and raises a boundary error @${\boundaryerror}
 for division by zero.

The notion of reduction @${\rrS} defines a semantics for statically-typed expressions (@figure-ref{fig:multi-preservation}).
    @; first theorem: \vdash (op1 v) : \tau implies delta(op1, v) is defined
The notion of reduction @${\rrD} defines a semantics for dynamically-typed expressions.
A dynamically-typed expression may attempt to apply an integer to an argument or give
 nonsensical arguments to a primitive, hence @${\rrD} explicitly checks for
 malformed expressions and raises a tag error @${\tagerror} as indication that
 an @mytech{elimination form} received a value of incorrect shape.

@; maybe make this more structured? finish the draft first tho
@; ... maybe less structure, because erasure doesn't really match

The three embeddings in the following sections build upon @figure-ref{fig:multi-reduction}.
Two of the embeddings support a form of type soundness; the other embedding is simpler.
The sound embeddings
 define functions @${\vfromdyn} and @${\vfromsta} for transporting a value across a boundary term,
 extend the @${\rrS} and @${\rrD} notions of reduction,
 and lift the notions of reduction to reduction relations @${\rrSstar} and
 @${\rrDstar} for (multi-language) evaluation contexts.
Lastly, the sound embeddings define a (two-part) syntactic property that is
 implied by a typing property in @figure-ref{fig:multi-preservation},
 and comes with a proof that the property is sound with respect to the
 corresponding reduction relation (static-static vs dynamic-dynamic).

@; TODO revise the above!!!

@include-figure["fig:multi-reduction.tex" @elem{Common semantic notions}]


@; -----------------------------------------------------------------------------
@section[#:tag "sec:natural-embedding"]{Natural Embedding}
@include-figure*["fig:natural-reduction.tex" "Natural Embedding"]
@include-figure*["fig:natural-preservation.tex" "Property judgments for the natural embedding"]

@; types should provide strong guarantees

@subsection[#:tag "sec:natural:overview"]{Overview}

@; "levels of abstraction" is a quote from J. Reynolds

The natural embedding is based on the idea that types should enforce levels
 of abstraction.
In a conventional typed language, this kind of enforcement happens statically;
 types define levels of abstraction and the type checker ensures compliance.
Migratory typing can provide a similar guarantee if the types on untyped
 values are checked at runtime.

The natural embedding uses a type-directed strategy to @mytech{transport} a value across
 a boundary between typed and untyped code.
If the value is untyped and entering a context that expects
 a value of a base type, such as @${\tint} or @${\tnat},
 then the strategy is to check the value against the type constructor.
If the context expects a value of an inductive type, such as @${\tpair{\tint}{\tint}},
 then the strategy is to the check the constructor and recursively transport
 the components of the value.
Lastly, if the context expects a value of a coinductive type, such as
 @${\tarr{\tnat}{\tnat}}, then the strategy is to check the constructor and
 monitor the future interactions between the value and the context.
For the specific case of an untyped function @${f} and the type @${\tarr{\tnat}{\tnat}},
 the natural embedding transports a wrapped version of @${f} across the boundary.
The wrapper checks that every result computed by @${f} is of type @${\tnat}
 and otherwise halts the program with a witness that @${f} does not match the type.


@subsection[#:tag "sec:natural:model"]{Model}

@Figure-ref{fig:natural-reduction} presents a model of the natural embedding.
The centerpiece of the model is the pair of boundary functions:
 @${\vfromdynN} and @${\vfromstaN}.
The @${\vfromdynN} function imports a dynamically-typed value into a statically-typed
 context by checking the shape of the value and proceeding as outlined above.
In particular, the strategy for transporting an untyped value @${v} into a
 context expecting a function with domain @${\tau_d} and codomain @${\tau_c}
 is to check that @${v} is a function and wrap it in a monitor @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}.
Conversely, the @${\vfromstaN} function exports a typed value to an untyped context.
It transports an integer as-is, transports a pair recursively,
 and wraps a function in a monitor to protect it against untyped arguments.

The notions of reduction define the semantics of monitor application.
In a statically-typed context, applying a monitor means applying a
 dynamically-typed function to a typed argument.
Thus the semantics unfolds the monitor into two boundary terms:
 a @${\vdyn} boundary in which to apply the dynamically-typed function
 and an inner @${\vsta} boundary to transport the argument.
In a dynamically-typed context, a monitor encapsulates a typed function and
 so the process is reversed: the argument crosses into a typed context and
 the result crosses back into the original untyped context.

The boundary functions and the notions of reductions come together
 to define the semantics of mixed-typed expression.
There are two main reduction relations: @${\rrNSstar} for typed expressions
 and @${\rrNDstar} for untyped expressions.
The difference between the two relations is how they act on an expression that
 does not contain any boundary terms.
The typed reduction relation steps via @${\rrS} by default, and the
 untyped relation steps via @${\rrD} by default.
For other cases, the relations are identical.

@;In principle, the one monitor value @${(\vmonfun{(\tarr{\tau_d}{\tau_c})}{v})}
@; could be split into two value forms: one for protecting the domain of a statically-typed
@; function and one for checking the range of a dynamically-typed function.
@;The split would clarify @${\rrNS} and @${\rrND} but it would also create a
@; larger gap between the model and MODEL (@secref{sec:implementation}).


@subsection[#:tag "sec:natural:soundness"]{Soundness}

@Figure-ref{fig:natural-preservation} presents two properties for the natural
 embedding evaluation syntax: one for dynamically-typed expressions and one
 for statically-typed expressions.
Each property extends the corresponding judgment from @figure-ref{fig:multi-preservation}
 with a rule for monitors.
The property for dynamic expressions (in the left column) states that a
 typed value may be wrapped in a monitor of the same type.
The static property states that any untyped value may be wrapped in a monitor,
 and that monitor is assumed to follow its type annotation.

The soundness theorems for the natural embedding state three results about
 well-typed / well-formed expressions:
 (1) reduction is fully defined, (2) reduction in a statically-typed context
 cannot raise a tag error, and (3) reduction preserves the properties from
 @figure-ref{fig:natural-preservation}.

@twocolumn[
  @tr-theorem[#:key "N-static-soundness" @elem{static @|NE|-soundness}]{
    If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
      @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}}} and @linebreak[] @${e' \rrND \tagerror} }
      @item{ @${e \rrNSstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "N-dynamic-soundness" @elem{dynamic @|NE|-soundness}]{
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

@tr-proof[#:sketch? #true]{
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
If the language is to allow values of coinductive type to cross a boundary,
 then it must generalize its soundness guarantee.


@; -----------------------------------------------------------------------------
@section[#:tag "sec:erasure-embedding"]{Erasure Embedding}
@include-figure["fig:erasure-reduction.tex" "Erasure Embedding"]
@include-figure["fig:erasure-preservation.tex" "Property judgments for the erasure embedding"]

@; types should not affect semantics.

@subsection[#:tag "sec:erasure:overview"]{Overview}

@; "syntactic discipline" is a quote from J. Reynolds

The erasure embedding is based on a view of types as a (strictly) syntactic discipline.
Types are just a structured kind of comment and should be orthogonal to the
 evaluation model of a language.
Their main purpose is to help developers read a codebase.
Their secondary purpose is to enable static type checking and IDE tools such
 as type-based autocompletion.
Whether or not the types are sound is incidental; type soundness
 never holds for the entirety of a practical language.

If one adopts this point of view, then the proper semantics for a migratory
 typing system is an extension of the host language's untyped semantics that ignores type annotations.
Any value may freely cross any type boundary, and thus the embedding uses
 the reductionist approach of relying on the soundness of the host language.
The embedding uses the reductionist approach of relying on the soundness of the
 the dynamically-typed host language.


@subsection[#:tag "sec:erasure:model"]{Model}

@Figure-ref{fig:erasure-reduction} presents a model of the erasure embedding.
The notion of reduction @${\rrEE} defines rules for boundary
 terms and type-annotated functions, and otherwise uses the dynamically-typed
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
  @tr-theorem[#:key "E-static-soundness" @elem{static @|EE|-soundness}]{
    If @${\wellM e : \tau} then @${\wellEE e} and one
    @linebreak[]
    of the following holds:
    @itemlist[
      @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
      @item{ @${e \rrEEstar \tagerror} }
      @item{ @${e \rrEEstar \boundaryerror} }
      @item{ @${e} diverges}
    ] }

  @tr-theorem[#:key "E-dynamic-soundness" @elem{dynamic @|EE|-soundness}]{
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
  Intuitively, this theorem holds because every sub-expression of @${e} is statically typed.
}


@; -----------------------------------------------------------------------------
@section[#:tag "sec:locally-defensive-embedding"]{Locally-Defensive Embedding}
@include-figure*["fig:locally-defensive-reduction.tex" "Locally-Defensive Embedding"]
@include-figure*["fig:locally-defensive-preservation.tex" "Property judgments for the locally-defensive embedding"]

@; types should prevent logical stuck-ness

@subsection[#:tag "sec:locally-defensive:overview"]{Overview}

The locally-defensive embedding is the result of two assumptions: one philosophical,
 one pragmatic.
The philosophical assumption is that the purpose of types is to prevent evaluation
 from ``going wrong'' in the sense of applying a typed elimination form to a value
 outside its domain.
For example, the elimination forms in the surface
 language are function application and primitive application.
Function application @${(\eapp{v_0}{v_1})} expects that @${v_0} is a function;
 primitive application expects arguments for which @${\delta}
 is defined.
The goal of the locally-defensive embedding is to ensure that such assumptions
 are always satisfied in typed contexts.
@; ... what about Nat? ... generalized form of tag error

The pragmatic assumption is that run-time monitoring, like that employed in
 the natural embedding, is impractical.
For one, implementing ``transparent'' monitors requires a significant engineering
 effort.
Second, monitoring adds a prohibitive run-time cost.

Based on these assumptions, the locally-defensive embedding rewrites typed code
 to defend itself against untyped inputs.
The defense takes the form of type-constructor checks; for example,
 if a typed context expects a value of type @${(\tarr{\tnat}{\tnat})} then a
 run-time check asserts that the context receives a function.
If this function is applied @emph{in the same context}, then a second run-time
 check confirms that the result is a natural number.
If the function is applied @emph{in a different typed context} that expects a
 result of type @${(\tpair{\tint}{\tint})}, then a run-time check confirms that
 the result is a pair.

Constructor checks do not require monitors,
 they run in near-constant time,
 and they ensure that every value in a typed context has the correct top-level shape.
If elimination forms only rely on the top-level shape of a value,
 then the latter guarantee implies that well-typed contexts do not ``go wrong''
 as desired.
@; or rather, "do not apply a typed elimination form to a value outside its domain" ?


@subsection[#:tag "sec:locally-defensive:model"]{Model}

@Figure-ref{fig:locally-defensive-reduction} presents a model of the
 locally-defensive embedding.
The model represents a defensive type-constructor check as an @${\vchk} expression;
 intuitively, the semantics of @${(\echk{K}{e})} is to reduce @${e} to a value
 and affirm that it matches the @${K} type constructor.
Type constructors @${K} include one constructor @${\tagof{\tau}} for each
 kind of type @${\tau}, and the exceptional @${\kany} constructor, which
 does not correspond to a static type.

The purpose of @${\kany} is to reflect the weak invariants of the locally-defensive
 embedding.
In contrast to types @${\tau}, type constructors say nothing about the
 contents of a structured value.
The first and second components of a generic @${\kpair} value can have any shape,
 and the result of applying a function of constructor @${\kfun} can be any
 value.@note{Since the direct result of function application is an expression
  and not a value, the model includes the ``no-op'' boundary terms @${(\edynfake{e})}
  and @${(\estafake{e})} to support the application of a typed function in an untyped
  context, and vice-versa.}
Put another way, the @${\kany} constructor is necessary because information about
 type constructors does not compose under the algebra of expressions.

To ensure that the evaluation of a typed expression does not lead to undefined
 behavior, the @emph{completion} judgment @${\Gamma \vdash e : \tau \carrow e'}
 rewrites a surface-syntax expression to a similar, safe expression.
The rewritten expression includes @${\vchk} forms around three kinds of typed
 expressions: function application, @${\vfst} projection, and @${\vsnd} projection.
For any other kind expression, the completion is constructed from the completion
 of its sub-expressions.


The completion of any other expression, including dynamically-typed expressions,
 the made of the completion of its components.


 @note{The full definition of @${\carrow} depends on a similar judgment for dynamically-typed
  expressions. That judgment does not insert checks in dynamically-typed code.}





The syntax of the embedding extends the evaluation syntax from @figure-ref{fig:multi-reduction}
 with new expressions, new contexts, and a grammar @${\kappa} for type constructors.
The expression @${(\edynfake{e})} encapsulates the body of an untyped function
 applied in a typed context; there is no type annotation for this boundary
 term because (as we shall see) the evaluator does not know what type to expect.
The expression @${(\estafake{e})} conversely encapsulates the body of a typed
 function applied in an untyped context; again there is no type annotation.
The expression @${(\echk{\kappa}{e})} associates a typed expression @${e} with an
 expected type constructor.
If we have the typed expression @${\wellM (\eapp{f}{0}) : \tnat} and @${f} evaluates
 to an untyped function @${(\vlam{x}{\esum{x}{1}})} then the immediate result
 of the application must be @${\echk{\tnat}{\edyn{(\esum{0}{1})}}}.
@; TODO do example first, to motivate the dyn and sta
The extended definitions of contexts @${\ebase} and @${\esd} accomodate the
 new expression forms.

Constructors @${\kappa} are first-order properties of values:
 a value may be a number (@${\kint} or @${\knat}), a pair (@${\kpair}),
 a function (@${\kfun}), or something else (@${\kany}).
For instance, the first component of any @${\kpair} value is a @${\kany} value.
The meta-function @${\tagof{\cdot}} maps a type to a constructor by ``truncating''
 the contents of the type.@note{Notation from @citet[vss-popl-2017].}

The judgment @${\Gamma e : \tau \carrow e'} states that @${e'} is the
 checked @emph{completion}@~cite[h-scp-1994] of the typed expression.
This completion is identical to the surface expression @${e} except that it
 adds @${\echk{\tagof{\tau}}{\cdot}} forms around every function application
 expecting a result of type @${\tau}, and around every call to @${\vfst} and
 @${\vsnd} expecting a result of the same type.
@Figure-ref{fig:locally-defensive-reduction} demonstrates the rules for
 application and @${\vfst}; the rule for @${\vsnd} is similar, and the other
 rules recursively take the completion of their sub-expressions.

@; TODO this should parallel the discussion in natural embedding
The dynamic boundary function @${\vfromdynK} computes the constructor of the given type
 and invokes a generic boundary-crossing function @${\vfromany} to check that
 the given value matches the constructor.
The function @${\vfromstaK} does nothing (justified in the next section).
Lastly @${\efromany{\kappa}{v}} checks that the value @${v} matches the given
 type constructor.
If not, it raises a boundary error.

The notions of reduction @${\rrKS} and @${\rrKD} define the semantics of
 @${\vchk} expressions and function application.
A @${\vchk} expression in typed code steps to the result of the @${\vfromany}
 boundary-crossing function.
A @${\vchk} expression in untyped code is stuck.
Typed and untyped functions can appear anywhere, so @${\rrKS} includes a
 rule for dynamically-typed application and @${\rrKD} includes rules for
 statically-typed application.
The application rules for a statically-typed function raise a boundary error
 if the argument does not match constructor of the function's domain type.
 
The reduction relations @${\rrKSstar} and @${\rrKDstar} are analogous to those
 of the natural embedding, but include transitions for un-annotated boundary
 terms.


@subsection[#:tag "sec:locally-defensive:soundness"]{Soundness}

@Figure-ref{fig:locally-defensive-preservation} presents two judgments for
 expressions internal to the locally-defensive evaluator.
The main theorem for this embedding is that these properties are sound with
 respect to the @${\rrKSstar} and @${\rrKDstar} reduction relations.

@twocolumn[
  @tr-theorem[#:key "K-static-soundness" @elem{static @|KE|-soundness}]{
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

  @tr-theorem[#:key "K-dynamic-soundness" @elem{dynamic @|KE|-soundness}]{
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

In other words, a ``well-constructed'' expression @${\wellKE e'' : \kappa} can
 reduce to either: a well-constructed value, a tag error (in untyped code), or
 a boundary error.
The link between well-constructed expressions and the surface syntax is the
 completion judgment; a key lemma for the previous theorems is that the
 completion judgment meets the following specification:

@twocolumn[
  @tr-lemma[#:key "K-S-completion" @elem{static @${\carrow} soundness}]{
    If @${\Gamma \wellM e : \tau} then
    @linebreak[]
    @${\Gamma \vdash e : \tau \carrow e'} and @${\Gamma \wellKE e' : \tagof{\tau}}
  }

  @tr-lemma[#:key "K-D-completion" @elem{dynamic @${\carrow} soundness}]{
    If @${\Gamma \wellM e} then
    @linebreak[]
    @${\Gamma \wellM e \carrow e'} and @${\Gamma \wellKE e'}
  }
]

Any judgment that satisfies this spec could be substituted for the @${\carrow}
 judgment.
@; what are you going to improve without changing \wellKE ?

The other main lemma is that boundary-crossing via @${\vfromany} is sound
 with respect to the property judgment.

@tr-lemma[#:key "K-check" @elem{@${\vfromany} soundness}]{
  If @${\mchk{K}{v} = v}
   @linebreak[]
   then @${\wellKE v : K}
}

@;A standard type soundness theorem holds of expressions that do not contain
@; boundary terms.
@;
@;  @tr-theorem[#:key "K-pure-static" @elem{@${\langE} static soundness}]{
@;    If @${\wellM e : \tau} and @${e} does not contain a sub-term of the form
@;     @${(\edyn{\tau'}{e'})} then one of the following holds:
@;    @itemlist[
@;      @item{ @${e \rrEEstar v \mbox{ and } \wellM v : \tau} }
@;      @item{ @${e \rrEEstar \boundaryerror} }
@;      @item{ @${e} diverges}
@;    ]
@;  }


@section[#:tag "sec:practical-semantics"]{From Models to Implementations}

@; TODO
@; - type-constructor checks suffice to prevent stuck-ness
@; - monitors ... how to implement? how to represent types?
@; - one reduction relation
@; - 

The models (except for erasure) define a multi-language semantics.
A real programming language doesn't work like this.
In real life there is one dynamically-typed host language and everyone uses its
 reduction relation.
Can we scale our models to a practical implementation?
Yes, because the static reductions are basically a subset of the dynamic reduction.
There is probably a theorem to state about this.
Okay and with that foundation, and with soundness still being true, we see
 that soundness means the dynamically-typed reduction does more-work-than-necessary
 in statically typed code.
An optimizing compiler can remove those checks; maybe by replacing the standard
 dynamically-typed @${\vsum} with an unsafe version that does not check for errors.




Recall the embedding goals:
@itemlist[
@item{
  @emph{soundness for a single language}
}
@item{
  @emph{expressive boundary terms}
}
@item{
  @emph{soundness for the pair of languages}
}
]

First goal, made formal by typical progress and preservation arguments
 for @${\wellM} (@figure-ref{fig:multi-preservation}) and the reduction relation
 (effectively restricted to basic evaluation contexts).

Second goal, made formal with easy theorems of the form:
 for all @${\tau} exists @${v} and @${v'} such that @${\mathcal{F}(\tau, v) = v'}.
(Not a great argument, but basic path coverage.)

Third goal, already stated above.



This space reserved for discussing similarities or connections between the models.

@tr-definition[#:key "boundary-types" @elem{boundary types @${B(e)}}]{
  Let @${B(e)} be the set of type annotations on boundary term in @${e},
   namely, @${\{\tau \mid \edyn{\tau}{e'} \in e \vee \esta{\tau}{e'} \in e\}}.
}

@tr-definition[#:key "bisimilar-reduction" @elem{bisimilar reduction}]{
  @${(e_0, \rightarrow_0)} and @${(e_1, \rightarrow_1)} are bisimilar if there
   exists a relation @${R} such that @${(e_0, e_1) \in R} and either:
  @itemlist[
  @item{
    @${e_0 \rightarrow_0 e_0'} and @${e_1 \rightarrow_1 e_1'}
    and @${(e_0', \rightarrow_0)} and @${(e_1', \rightarrow_1)} are bisimilar;
  }
  @item{
    @${e_0 \rightarrow_0 e_0'}
    and @${(e_0', \rightarrow_0)} and @${(e_1, \rightarrow_1)} are bisimilar;
  }
  @item{
    @${e_1 \rightarrow_1 e_1'}
    and @${(e_0, \rightarrow_0)} and @${(e_1', \rightarrow_1)} are bisimilar.
  }
  ]
}

@tr-theorem[#:key "NK-base-type" @elem{@|NE|/@|KE| base type equivalence}]{
  If @${\wellM e : \tau} and @${B(e) \subseteq \{\tint, \tnat\}}
  and @${\wellM e : \tau \carrow e''}, then
  @${(e, \ccNS)} and @${(e'', \ccKS)} are bisimilar.
}

The proof follows from the fact that boundary terms of base type have the same
 semantics in both embeddings.
More precisely, for any value @${v} the function @${\efromdynK{\tint}{v}} yields
 the same result in the natural and locally-defensive embeddings.

@; TODO do the proof, but should be easy
@; - D(t,v) = D(t, v) and S(t,v) = S(t,v) across embeddings
@; - stuttering simulation because of chk terms
@; - all checks pass in the LD term ... because every value is "actually typed"

Helpful to compare the canonical forms and inversion principles in each language.

@; natural
@twocolumn[
  @tr-lemma[#:key #false @elem{@|NE| canonical forms}]{
    @itemlist[
      @item{
        If @${\wellNE v : \tpair{\tau_0}{\tau_1}}
        then @${v \eeq \vpair{v_0}{v_1}}
      }
      @item{
        If @${\wellNE v : \tarr{\tau_d}{\tau_c}}
        then either:
        @itemlist[
          @item{
            @${v \eeq \vlam{\tann{x}{\tau_x}}{e'}
               @tr-and[]
               \tau_d \subteq \tau_x}
          }
          @item{
            or @${v \eeq \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'}
                  @tr-and[]
                  \tarr{\tau_d'}{\tau_c'} \subteq \tarr{\tau_d}{\tau_c}}
          }
        ]
      }
      @item{
        If @${\wellNE v : \tint}
        then @${v \in \integers}
      }
      @item{
        If @${\wellNE v : \tnat}
        then @${v \in \naturals}
      }
    ]
  }

  @tr-lemma[#:key #false @elem{@|NE| inversion}]{
    @itemlist[
      @item{
        If @${\wellNE \vpair{v_0}{v_1} : \tpair{\tau_0}{\tau_1}}
        then @${\wellNE v_0 : \tau_0
        @tr-and[] \wellNE v_1 : \tau_1}
      }
      @item{
        If @${\wellNE \vlam{\tann{x}{\tau_x}}{e'} : \tarr{\tau_d}{\tau_c}}
        then @${\tann{x}{\tau_d} \wellNE e' : \tau_c}
      }
      @item{
        If @${\wellNE \vmonfun{(\tarr{\tau_d'}{\tau_c'})}{v'} : \tarr{\tau_d}{\tau_c}}
        then @${\wellNE v'}
      }
    ]
  }
]@;
@;
@; erasure
@twocolumn[
  @tr-lemma[#:key #false @elem{@|EE| canonical forms}]{
    If @${\wellEE v}
    then either:
    @itemlist[
      @item{
        @${v \eeq \vlam{x}{e'}}
      }
      @item{
        @${v \eeq \vlam{\tann{x}{\tau_x}}{e'}}
      }
      @item{
        @${v \eeq \vpair{v_0}{v_1}}
      }
      @item{
        @${v \in \integers}
      }
    ]
  }

  @tr-lemma[#:key #false @elem{@|EE| inversion}]{
    @itemlist[
      @item{
        If @${\wellEE \vpair{v_0}{v_1}}
        then @${\wellEE v_0 @tr-and[] \wellEE v_1}
      }
      @item{
        If @${\wellEE \vlam{\tann{x}{\tau_x}}{e'}}
        then @${\tann{x}{\tau_x} \wellEE e'}
      }
      @item{
        If @${\wellEE \vlam{x}{e'}}
        then @${x \wellEE e'}
      }
    ]
  }
]@;
@;
@; locally-defensive

@exact{\newpage}
@twocolumn[
  @tr-lemma[#:key #false @elem{@|KE| canonical forms}]{
    @itemlist[
      @item{
        If @${\wellKE v : \kpair}
        then @${v \eeq \vpair{v_0}{v_1}}
      }
      @item{
        If @${\wellKE v : \kfun}
        then either:
        @itemlist[
          @item{
            @${v \eeq \vlam{\tann{x}{\tau}}{e'}}
          }
          @item{
            @${v \eeq \vlam{x}{e'}}
          }
        ]
      }
      @item{
        If @${\wellKE v : \kint}
        then @${v \in \integers}
      }
      @item{
        If @${\wellKE v : \knat}
        then @${v \in \naturals}
      }
    ]
  }

  @tr-lemma[#:key #false @elem{@|KE| inversion}]{
    @itemlist[
      @item{
        If @${\wellKE \vpair{v_0}{v_1} : \kpair}
        then @${\wellKE v_0 : \kany @tr-and[] \wellKE v_1 : \kany}
      }
      @item{
        If @${\wellKE \vlam{\tann{x}{\tau_x}}{e'} : \kfun}
        then @${\tann{x}{\tau_x} \wellEE e' : \kany}
      }
      @item{
        If @${\wellKE \vlam{x}{e'} : \kfun}
        then @${x \wellKE e' : \kany}
      }
    ]
  }
]
