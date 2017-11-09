#lang gf-pldi-2018
@title[#:tag "sec:implementation"]{Scaling the Model to an Implementation}

@; Purpose: lessons of tags for a real language,
@;   if you try extension XXX, here's what to look out for.

@; Notes:
@; - separate compilation
@; - near-constant time checks
@; - no space
@; - "minimize" checks, fully-typed should be fast

@section{More Types}

@; unions
@; recursive types

Any surprises with base types?

Untagged unions need union-tags.
Tidiness: must be discriminative --- wait not sure that matters.

Forall types, must be guarded.

Recursive types, must be guarded / contractive.

Point of restrictions is to have a tag for each type.


Did not implement for objects and classes,
 a few questions about how to do in reasonable time.


@section{Formal Model}

PLT Redex, see tech report?

Modules, require provide, store.

@;@section{Further Improvements}
@;
@;@; trusted cod
@;@; already-checked dom (unify?)
@;
@;Redundant tag checks, remove.
@;Slogan is, @emph{you can trust the tags}.
