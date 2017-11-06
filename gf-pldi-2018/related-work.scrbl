#lang gf-pldi-2018
@title[#:tag "sec:related-work"]{Related Work}

@parag{Multi-Language Semantics}

Matthews-Findler originated.
Dimoulas for complete monitoring.


@parag{Migratory Typing}

Tobin-Hochstadt, Typed Racket.


@parag{Type-Tag Soundness}

@citet[vss-popl-2017] present a compiler from type-annotated source code
 to a dynamically typed host language.
They prove that the generated code is tag sound.
First implementation of the forgetful, first-order embedding.

@;... in a way, our Section 3 is adding the missing "why" from their paper,
@;I mean they give high-level motivation, but that's all besides "proofs worked out".
@;Very frustrating.
@;There are many design choices, important to know why this particular set
@; makes sense for what context.
@;Because it's not always going to be true for all contexts.
@;
@; 2017-11-05 : trouble reverse-engineering the model, whence the story

@; Question: does reticulated follow the model?
@;  Yes basically. Something's wrong checking [] twice but the same problem
@;   doesn't happen with integers so I guess its fine.

@;Like types@~cite[bfnorsvw-oopsla-2009] are annotations with no semantics.
@;@citet[rnv-ecoop-2015] apply the idea to TypeScript; TypeScript has only like types,
@; and their work gives programmers the choice of using (concrete) types that
@; are enforced at run-time.



@; progressive types
@; redex
@; redex-check
@; levity polymorphism, ideas for compiling functions that MIGHT need checks
