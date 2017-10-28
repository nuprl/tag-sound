#lang gf-pldi-2018
@title[#:tag "sec:background"]{Migratory Typing through Language Interoperability}

@; TODO
@; - remember, no soundness without semantics
@; - make sure Sec 1 lists all tradeoffs
@;   also Sec (related-word)
@;   also Sec 1, more guarantees = more optimization but apparently not much at stake
@; OUTLINE
@; - interop, boundary terms, guards
@; - identity embedding, dyn soundness
@; - natural embedding, type soundness
@; - extension to generalized datatypes
@;   * recur into structured values
@;   * monitor for "higher-order" values, e.g. writable
@; - silent failures! use the Reynolds example
@; - performance cost! plot results for typed racket
@; - TR vs Racket
@; - 


The goal of a migratory typing system is to allow safe interaction between
 statically typed code and dynamically typed code.
The key tradeoffs at play are the guarantees and the performance.
@; TR is "full guarantees" aka perfectly type sound,
@; TS is "full performance" aka no penalty for interaction
@;  I think penalty is the right way --- though low-level --- way to think
@;  about performance because then there's no question of optimizations,
@;  that's a separate question more tied to the guarantees
The purpose of this section is to explain the key ideas of
 migratory typing as a language interoperability problem,
Examine the benefits and drawbacks for previous approaches,
 set the stage for the first-order embedding formalized in the next section.



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

@section{A Theory of Macro-Level Gradual Typing}

Static typing like normal,
 runtime environment can have monitored values,
 special runtime typing for progress and preservation, get conventional type soundness.


@section{Typed Racket, Generalized Soundness}

Principles, particulars, answer to the programs.


@section{Reticulated, Tag Soundness}

Principles is no proxies, only rewrite typed code, only check "tags".
Particulars, answers TBA.


@section{Performance}

High-level comparison, I guess "low-level" compare FSM performance.

