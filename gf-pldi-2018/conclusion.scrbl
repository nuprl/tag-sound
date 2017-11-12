#lang gf-pldi-2018
@title[#:tag "sec:conclusion"]{Why Types?}

@; NOTE
@; further "refinements" besides Nat? ... what to do when type cannot be
@;  computed from value at runtime, such as "terminating function" or
@;  "stream of even numbers"?

@; -----------------------------------------------------------------------------

Tribes seeking the elusive goal, of code that is easy to write
 read verify maintain.
TypeScript state-of-the-art for writing and reading,
 Typed Racket state-of-the-art for static reasoning.
What do programmers prefer?
Need to ask them.
Does tag soundness strike a balance?
We'll see.

Soundness costs time and money, here is a new point on the Laffer curve.

The big question, what are types good for?
Best for static checking, for IDE completion?
For making partial operations total,
 reasoning about code,
 optimization?
Conventional conference wisdom and conventional industry wisdom
 are polar opposites,
 the performance work suggests they will never meet in the middle.
This paper is one idea for a compromise, interested to hear others.

@; Future work:
@; - precise cost of boundaries
@; - infer types, help with conversion
@; - RTTI for TR, the models have (mon T v) but reality is (mon K,K v)
@; - static analysis, to pick natural vs. co-natural for a boundary (for efficiency)
@; - JIT for tagged, other things to reduce tag checks
