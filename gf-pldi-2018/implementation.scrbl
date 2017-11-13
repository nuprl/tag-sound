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
 (1) implement a constant-time tag for each type,
 (2) tag-check the actual parameters of every typed function,
 and (3) tag-check the result of every elimination form.

@; hints for implementors?
@; lessons
@; clarifications
@; ... ?


@section{Invariant Types}

Invariant datatypes, such as those representing a mutable array,
 pose no extra difficulty.
A mutable data structure must be tag-checked the same way as an immutable one;
 all reads must be guarded.
This defense means that writes can be unguarded.

Put another way, an array is just like a function that accepts any input.
Writing to an array is the same as calling a total function.
The write can never fail, so there is no need to interpose a tag check.


@section{Function Types}

The model has exactly one kind of function type, and assigns it a simple tag.
Real languages may have many function types,
 N-ary functions,
 variable-arity functions,
 and functions expecting keyword arguments.

For the Racket implementation, we check the number of args and kwards.
Performance is fine, as long as we avoid contract combinators.


@section{Untagged Union}

@; unions
@; recursive types
@; parametric polymorphism

Any surprises with base types?

Untagged unions need union-tags.
Tidiness: must be discriminative --- wait not sure that matters.

Forall types, must be guarded.

Recursive types, must be guarded / contractive.

Point of restrictions is to have a tag for each type.


Did not implement for objects and classes,
 a few questions about how to do in reasonable time.


@section{User-Defined Types}

Make sure eliminators for user-defined types are recognized as such.


@section{Require}

Check required data.

@;@section{Further Improvements}
@;@; trusted cod
@;@; already-checked dom (unify?)
@;Redundant tag checks, remove.
@;Slogan is, @emph{you can trust the tags}.
