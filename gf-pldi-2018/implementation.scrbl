#lang gf-pldi-2018
@title[#:tag "sec:implementation"]{Scaling the Model to an Implementation}

@; Notes:
@; - separate compilation
@; - near-constant time checks
@; - no space
@; - "minimize" checks, fully-typed should be fast

@; -----------------------------------------------------------------------------

The general recipe for scaling the model of the locally-defensive embedding
 to an implementation in a practical language has three steps:
 (1) define a type-tag for each static type,
 (2) tag-check the actual parameters of every typed function,
 and (3) tag-check the result of every elimination form.
In practice, there are some design decisions to consider.

@; hints for implementors?
@; lessons
@; clarifications
@; ... ?

@section{???}

Mutable is no problem
Objects, check the fields
Functions, design choices

@subsection{Invariant Types}

Invariant datatypes, such as those representing a mutable array,
 pose no extra difficulty.
A mutable data structure must be tag-checked the same way as an immutable one;
 all reads must be guarded.
This defense means that writes can be unguarded.

Put another way, an array is just like a function that accepts any input.
Writing to an array is the same as calling a total function.
The write can never fail, so there is no need to interpose a tag check.


@subsection{Function Types}

The model has exactly one kind of function type, and assigns it a simple tag.
Real languages may have many function types,
 N-ary functions,
 variable-arity functions,
 and functions expecting keyword arguments.

For the Racket implementation, we check the number of args and kwards.
Performance is fine, as long as we avoid contract combinators.


@section{Non-trivial Type Constructors}

The types @${\tau} in the model all have simple canonical forms.
For example, the pair type @${(\tpair{\tau_0}{\tau_1})} corresponds to
 values of the form @${\vpair{v_0}{v_1}}; these match the tag @${\kpair}.

@; TOO MEANDERING

A type is @emph{trivially tagged} if the definition of @${\tagof{\tau}} is not
 recursive.
Some common types are not trivially tagged.
We describe how to handle these below.


@subsection{Untagged Union}

@; unions
@; recursive types
@; parametric polymorphism

Any surprises with base types?

Untagged unions need union-tags.
Tidiness: must be discriminative --- wait not sure that matters.


@subsection{Parametric Polymorphism}

If a statically-typed expression has type @${\tall{\alpha}{\tau}}, the type
 checker ensures that @${e} is defined for any substitution for @${\alpha}.
A function from @${\tarr{\alpha}{\tau}} is defined for any input,
 and @${e} cannot assume anything about the result of @${\efst{z}} where
 @${z} has type @${(\tpair{\alpha}{\tau'})}.
This leads to a simple definition of type tags for all-types:

@${\hfill \tagof{\alpha} = \kany \qquad \tagof{\tall{\alpha}{\tau}} = \tagof{\tau} \hfill}

Any client code that instantiates @${\alpha} with a concrete type
 will come with its own tag checks to make sure that @${e} is actually polymorphic.
This delays errors just like the co-natural embedding.


@subsection{Recursive Types}

The type-tag for a recursive type @${\trec{\alpha}{\tau}} is simply the tag
 of @${\tau} after unfolding the recursive type:

@${\hfill \tagof{\trec{\alpha}{\tau}} = \tagof{\vsubst{\tau}{\alpha}{\trec{\alpha}{\tau}}} \hfill}

To ensure the above definition is well-founded, all recursive types must
 be contractive.
That is, any occurrence of @${\alpha} in @${\tau} must be guarded by a type
 constructor and that constructor cannot be
 @${\tunion}, @${\forall}, or @${\mu}.


Did not implement for objects and classes,
 a few questions about how to do in reasonable time.


@subsection{User-Defined Types}

Make sure eliminators for user-defined types are recognized as such.


@section{Completion, Error Messages}


@section{Compilation}


@section{Require}

Check required data.

@;@section{Further Improvements}
@;@; trusted cod
@;@; already-checked dom (unify?)
@;Redundant tag checks, remove.
@;Slogan is, @emph{you can trust the tags}.
