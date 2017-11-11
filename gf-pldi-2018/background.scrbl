#lang gf-pldi-2018
@title[#:tag "sec:background"]{Background}

@; @parag{Assumptions}
@; (0) no lump embedding! want observationally-equal values across boundaries
@; (1) boundaries are explicit in syntax
@; (2) no Dyn type, no type compatibility
@; (3) all values can cross boundary
@; (4) at least one ``infinite'' value
@; (5) type system makes finer distinctions than primops
@; (6) same values, don't need to convert floats to ints etc.

@; -----------------------------------------------------------------------------

The goal of migratory typing is to retrofit a static typing system to
 a dynamically-typed host language.
A well-designed migratory typing system provides some of the benefits of static
 typing at little cost to programmers.
Such benefits can include static detection of logical errors and guarantees
 about programs' run-time behavior.
The costs can include the human cost of writing type annotations
 and the performance overhead of enforcing static types at run-time.
@; I think this is in the ballpark

Existing migratory typing systems include
 @;StrongTalk,
 Typed Racket,
 TypeScript,
 and
 Reticulated.
@; ^^^ sorted by release date
These systems are diverse.
Each is tailored to a particular dynamically-typed host language
 and each offers different benefits to programmers.

There are, however, two unifying characteristics among existing migratory
 typing systems.
First, each system extends the syntax of the host language with support
 for type annotations.@note{In principle, migratory typing based on type
  inference does not require explicit annotations.
  Nevertheless, explicit annotations may help programmers debug type
   errors and understand unfamiliar code.}
@; cite ML error
@; cite Wright's thesis
@; TODO say something better about "readability"
Second, each system is compatible with dynamically-typed code from the host
 language.
@; illustrate these?
A statically-typed TypeScript function, for example, may use JavaScript
 libraries to compute its result.

Consequently, a migratory typing system for a dynamically-typed host language @${\langD}
 consists of two parts:
 (1) a statically-typed language @${\langS},
 and (2) a typed foreign-function interface (FFI) between the languages.
The language @${\langS} must support a large subset of the host language,
 and add syntax for explicit type annotations.
The FFI is typically part of a runtime system that monitors interactions
 between statically-typed and dynamically-typed values.
Our focus is the FFI.


@section{The Problem: Language Embedding}

Given a safe dynamically-typed language @${\langD} and a type-safe statically-typed language
 @${\langS} that adds syntax for type annotations, the challenge is to design a multi-language
 in which @${\langD} expressions may be embedded in @${\langS} expressions (and vice-versa).
The embedding must provide a safety guarantee,
 and it must add minimal performance overhead to preserve safety at run-time.
@; TODO but we haven't talked about how such overheads arise!!!!!!
@; TODO really want to say "key tradeoffs: soundness, performance, (expressiveness)"

An @emph{embedding} in this sense may consist of static and dynamic components.
On the static end, the multi-language may add expression and value forms,
 as well as typing rules for the new additions.
At a minimum, the extension must include so-called @emph{boundary terms}
 to distinguish code from either source language.
The boundary terms we use are:

@$|{ \hfill \edyn{\tau}{e} \qquad \esta{\tau}{e} \hfill }|

A @${\vdyn} expression embeds a dynamically-typed expression @${e} in a
 statically-typed context.
Likewise, a @${\vsta} expression embeds a statically-typed expression @${e}
 in a dynamically-typed context.

On the dynamic end, the multi-language needs runtime support for any new
 values and for boundary terms.
For boundary terms, we require type-directed strategies for moving value forms
 across boundary terms.
These can take the form of metafunctions:

@exact|{
  $\hfill\fromdyn : \tau \times v \rightarrow v\hfill$

  $\hfill\fromsta : \tau \times v \rightarrow v\hfill$
}|

These metafunctions are the key part of an embedding.
They determine what kinds of values may cross boundaries,
 they enforce type safety,
 and they determine the performance overhead of sharing values.

How to define them?
That is the main question.
A language could leave them undefined and thus prohibit sharing.
A language could define them only for sequence-of-bits kinds of values,
 such as integers and characters, to allow a limit form of sharing.
These choices are obviously safe, but inexpressive.
We want embeddings that are at least partially defined for all types in
 the language.


@;@section{Summary, Glossary}
@;
@;mixed
@;configuration
@;monitors
@;accountability
