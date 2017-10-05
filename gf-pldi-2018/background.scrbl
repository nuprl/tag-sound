#lang gf-pldi-2018

@; TODO
@; remember, no soundness without semantics

@title[#:tag "sec:background"]{Sound Gradual Typing is Dead Slow}

Gradual typing idea is simple, controlled channels of communication
 with untyped code.
Sadly, many ways to communicate.
Sadly, adding control adds runtime overhead.

In principle, one thing to do = check untyped input.
But input comes from many places.

@; this is easy to explain

A gradual typing system delays some type checking until run-time.
What becomes of type soundness?

First order vs. higher-order data.

Example programs, litmus tests.
To frame the discussion, consider the following programs.

TBA


@section{Typed Racket, Generalized Soundness}

Principles, particulars, answer to the programs.


@section{Reticulated, Tag Soundness}

Principles is no proxies, only rewrite typed code, only check "tags".
Particulars, answers TBA.


@section{Performance}

High-level comparison, I guess "low-level" compare FSM performance.

