#lang gf-pldi-2018
@title[#:tag "sec:design"]{The Descent}

The identity embedding is unacceptable to programmers who want to use types
 to reason about the behavior of their programs.
The natural embeddings is unacceptable to programmers with performance
 requirements.
This section presents an embedding that represents a compromise.
In theory, this embedding has significantly better performance than the
 natural embedding --- each boundary crossing and eliminator incurs one
 near-constant time check.
The shallow performance cost enables an equally shallow safety theorem:
 if you pay for tag checks, you can trust the type-tags of all values.

In the natural embedding, type boundaries suffer three kinds of costs.
The costs are (1) checking a value, (2) allocating a monitor, and (3)
 the indirection cost of monitors.
@; TODO what about the later checks for each monitor?
@;   this story is not really cohesive
We will systematically reduce these costs in three steps.
First we introduce new monitors to avoid traversing a data structure
 at a type boundary.
Second we reduce indirection at the cost of "forgetting" past boundaries.
Third we remove monitors altogether with a rewriting scheme;
 saves performance but loses error messages in untyped code.

All this in the context of our lambda calculus (?).


@section{Lazy Boundary Checks}

First we deal with the linear-time cost of checking pairs at a boundary.
The goal is to make this a near-constant cost.
No more recursion.

Can apply the same strategy used for functions.
For functions we were forced to be lazy because it was impossible to check
 exhaustively.
For pairs, laziness is the "right" choice.
(Okay maybe this version isn't performant. I don't know. But it's on the
 road to a performant implementation.)

Add new kind of value, new typing rules, new reduction relation.
Figure to demonstrate.
Instead of eagerly checking the pair, delay until reads.

Note, could be far more expensive than just checking the pair, consider a function
 that performs two reads.
The function is twice as slow with the new guards.

@exact|{
 $$(\vlam{(x:\tpair{\tint}{\tint})}{(\efst{x} + \efst{x})})$$
}|

But this is arguably bad style, requires two data stucture accesses as well.
Maybe a compiler should re-write (CSE) before inserting the tag checks.

@emph{Type soundness} does not change by making checks lazy,
 it only delays value errors from "immediately at the boundary" to
 "only until access".
Allows somewhat latent type errors,
 but nothing serious because if an access happens to read a bad value,
 this will be reported.
No matter where it happens.


@section{Forgetful Monitors}

Previous step was uncontroversial in terms of soundness,
 questionable in terms of performance.
Now going further, definitely to gain performance and lose something
 of soundness (though the same theorem can be proved).

New semantics for monitors, "mon mon" reduces to "mon".
This is the forgetful space-efficient semantics formalized by Greenberg.

Quick discussion about how this is sound?
Probably obvious, but probably good to give intuition for the tech report proof.


@section{Removing Monitors}

Another controversial step.
Replace monitors with inlined checks.
Only rewrite in typed code.

Two rules:
@itemlist[
@item{
  Typed code that @emph{reads} from a possibly-untyped value must tag-check
   the result.
}
@item{
  Typed values that receive @emph{writes} from possible-untyped contexts must
   be prepared to accept any kind of input.
}
]

For reads, the solution is to insert a check between a data structure and
 its clients.
For writes in the form of function application, the function must tag-check
 its input.
Other writes --- for example writes to a mutable data structure --- do not
 need to check their input provided the language runtime supports writing
 any kind of value to the data structure (should be no problem in a dynamically-typed language).

More efficient.
Loses codomain errors in untyped code.
Does more checks than necessary in typed code.


@section{Further Improvements}

@; trusted cod
@; already-checked dom (unify?)

Redundant tag checks, remove.
Slogan is, @emph{you can trust the tags}.
