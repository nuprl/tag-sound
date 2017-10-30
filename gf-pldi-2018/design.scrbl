#lang gf-pldi-2018
@title[#:tag "sec:design"]{The Forgetful, First-Order Embedding}

@section{Reducing Cost}

@; O(1) at boundary
@; forget wrapped monitors
@; type soundness


@section{Removing Monitors}

@; no allocation
@; put guard wherever a monitor might need to check IN TYPED CODE
@; clarify "might" with a type system
@; completion
@; type-tag soundness
@; - this is definitely worse than monitors,
@;   because lost checks in untyped code



@section{Further Improvements}

@; trusted cod
@; already-checked dom (unify?)

Redundant tag checks, remove.
Slogan is, @emph{you can trust the tags}.
