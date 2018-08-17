talk
===

TODO

[ ] outline
[ ] draft slides
[ ] give presentation
[ ] blog post


- - -
# OUTLINE

1. folklore I II
2. untyped, error paths
3. typed, error paths unused by types proven unused by soundness
  - origins of folklore ... no benefit of unsoundness, just means paths get used ... lol bug
  - more types clearly better can remove more paths
  - DONT FORGET RUNTIME LIBRARY
4. gradual , problem statemnt, 3 neighboring villages
5. H E 1 same surface languages all different runtime type system different abstractions anti-folklore
6. 3 choices ... simplicity & compatibility & explainability ... and performance ->
7. flagged paths need checks, checks depend on types, predict costs
8. measured for Racket + TR surface language ... setup impls benchmarks results
  - for mixed-typed usually E < 1 < H
  - for nearly-typed usually H < E < 1 wow
9. picture is mixed, quite mixed
   cannot just optimize because boundaries and abstractions
10. future

- - -
# SCRIPT

This work is about gradual typing, but the talk is really about two pieces of
folklore. As you know folklore can be true and can be false, and its often
much simpler than the full picture. Onward.

The first folklore proposition is that soundness, in the sense of type
soundness, is a binary proposition.  Either a language is sound or unsound, and
there's no place for grey areas in between. This, I claim, is just false for a
language that mixes typed and untyped code. Or rather, its not a useful way of
thinking.

The second folkore proposition is that adding type information to a program can
only improve performance.  The idea being, there's no downside to adding type
information and a smart compiler can leverage the types. This is also
misleading-at-best in a language that allows typed and untyped code.

Look, its another world out there and things don't just work like they did
before. Your standard interoperability story.

Lets explain the situation. A gradually typed language is split into two
(like the cold war) two languages, two concrete syntaxes, and two definitions
for typed and untyped expressions.

For now, I want to just share the essence of the problem The easiest way to do
that is to tell you a story. Once upon a time there was a little pond and a big
river. The pond was home to a rare breed of fish, the golden tuna. In fact
every fish in the pond was a golden tuna, and every egg in the pond was a gold
tuna egg. People would come from far and wide to visit the little pond with the
remarkable golden tuna invariant.

The river was home to all kinds of fish, including some golden tuna but also
including many other fish of different shapes colors and sizes. Instead of the
golden tuna property, the river had a weaker, "just fish", invariant. Other things
being equal, the river is always going to contain fish.

One day the river changed direction and started to flow into the pond. The
villagers hired three ecologists to decide what to do about the impending
merger of the pond and the river. That is, given that the waters are going to
mix, what if anything is to be done to preserve the golden tuna invariant.

The first scientist, Dr. H, wants to preserve the golden tuna property. Dr H's
plan is to put a scanning machine at the edge of the pond. If a fish enters the
scanner, the machine performs a DNA test to check that the fish is both golden
and tuna. If an egg enters the scanner, the machine wraps it in a little
scanner; when the egg hatches then the little scanner performs a DNA test and
either releases the fish or sounds an alarm. With the scanner in place, fish
can flow in from the river and we have the invariant that everything in the
pond is either a golden tuna, a golden tuna egg, or a monitored egg.

The second scientist, Dr. E, is not concerted about the golden tuna invariant.
Dr E suggests letting the river fish flow in with no checks. This strategy is
very simple and does not require any scanners, but can only guarantee that the
pond has ``just fish'' like the river.  Its a lowest-common-denominator
property.

The third scientist, Dr 1, suggests a compromise. Dr 1's plan is to install a
few cameras around the pond and one at the entrance. The camera at the entrance
looks at everything flowing in and sounds an alarm if it sees a non-golden
fisr. Other fish and eggs are free to go. The cameras around the pond check
every egg-hatching. If a non-gold fish pops out, the cameras sound an alarm.
This guarantees a "golden fish" invariant.

The three ecologists got together to decide what to do, but unfortunately they
all spoke different languages and are still arguing to this day. The end.

In this story, the river represents an untyped piece of code. The ``just fish''
property means the code is ready to run --- no mismatched parentheses or
misused keywords. The pond represents well-typed code according to a sound type
system. The connection between the river and the pond corresponds to an import
statement, where the typed code expects either golden tuna or golden tuna eggs.
The golden tuna represetnts an immutable data structure, such as a list or a
tree. The eggs represent thunks -- that might return gold tuna or some other
fish.

type gold_tuna = integer safe
type egg = unit -> fish
type fish = gold_tuna | red_tuna | swordfish | ....

(A safe is like a list, but has not elimination forms. Simple!)

Of course a real language will have more than two kinds of first-order data and
1 kind of function. But this is enough to explain the ecologists 3 plans.

In terms of these datatypes, the Dr. H plan is to check first-order data with a
deep structural traversal and to check higher-order data using higher-order
contracts to express delayed obligations. Typed Racket is one language that
implements this approach. 

The Dr E plan is to allow any kind of untyped value to flow into typed code, in
spite of the type annotation at the boundary. TypeScript is one language that
implements this plan.

The Dr 1 plan is the really interesting one. At the boundary, the strateyy is
to check that incoming data is a function or a safe. If its a safe then its
free to go with no check on its contents. If its a function its also goes free
--- but every function application in typed code must factor through a check
that the application produced a safe. Reticulated Python implements this plan.

The last things to explain are the three invariants. The golden tuna invariant
corresponds to a generalized notion of type soundnenss that admits monitored
funcitions and boundary alarms. The ``just fish'' property basically says that
the program has a well-defined semantics. And finally the ``gold fish''
property is a soundness at the level of type constructors. Every value in typed
code matches the constructor of its static type.

With this I can now make the point that soundness is not a binary proposition
for a language that can mix typed and untyped code. There are at least these
three alternatives (and the appendix of the paper states two others).
nteresting choices that offer different guarantees and require different levels
of sophistication to implement.

`` soundness is not binary when we move from one language to a pair of languages''

the second folklore result we started with claims that adding type information
to a program can only improve its perfroance. If we begin with an untyped
program made of a few components and add types to some, the idea is that a
smart optimzizer should be able to leverage the types in each component.

Already therea re two issues with this picture. First it does not account for
the cost of interaction between components. As we've seen a typed component
needs to check values provided by an untyped component if it wants to provide
some kind of type soundness. Second, it assumes that a typed component is
always safe to leverage its types. This is only true if the types are sound.

So as you add types going to increase typed/untyped interaction and maybe
cannot make use of types in optimizations. HMM

To measure performance we implemented an extension to Typed Racket. In Normal
Typed Racket starts with a Racket/TR program, compiles higher-order enforcement
of types, and runs on the Racket bytecode and VM. Our extension adds two
alternate compiler pipelines: one that erases the types and another that
enforces type constructor soundness with first-order checks. For any program
this gives three ways of running it. 

Then, to measure the effect of adding types, we start with a fully-typed
program and systematically remove all the type annotations. This is easy going
module-at-a-time, start fully typed because the reverse direction comes with
awkward principal types question) Now for one program we can repeat this
performance lattice experiment three times and see how performance changes with
the numner of type annotations. We ran this experiment on 10 functional
programs (with refs) The details are in the paper. For now I want to summarize
the conclusions.

For the H strtategy we found that increasing the number of type annotaitons
leads to an umbrella kind of shape. That is performance can spike depending on
the typed/untyped interaction in the program. But then as typed/untyped
interaction is less those optimizations start to pay off (enabled by soundness)
even in the presence of untyped code H-protected programs can run faster

For the E strategy types are erased and have no effect on performance. Types
are not enforces so theres no slowdon at the boudnary. And types are not sound
so theres no optimizing because its unsafe. No matter the annotations.
Performance is always the same as if there were no types.

For the 1 strategy, performance seems to be a lineary function of the number of
type annotations. The first half of this curve should not be surprising ---
adding types to some modules means the typed/untyped interaction has a cost ...
a moderate cost because the boundary-checks are simple first-order checks. On
the right, this is more surprosing. Even a fully-typed program is pretty slow.
Theres no boundary interacction on the right. The slowdown comes from
elimination forms (function call, list ref) in typed code. Since typed can only
trust the constructor, this is an overapproximation to be safe. Now that's not
100% true because if we apply a typed function we know for sure what the result
will be so there is no need for the check. TLDR we have some basic optimizations
that somewhat mitigate the cost ... but overall still slow.

To summarize here our full picture for performance. H pays to enforce interactions
Sometimes that cost is huge but standard type-driven optimizations do apply.
For E performance is just as untyped. For 1 there no extreme case but its an
inevitable cost (words here are very important to get right)

Theres a lot more work to be done in this performance space. Pycket suggests we
can change the landscape. Even if we cannot might be possible to find the point
where its best to switch between H and 1. At any rate, the relative performance
of these typed/untyped strategies is not a simple picture and its certainly not
the case that if one adds more type information then a compiler can just go
ahead and improve performance.

To summarize we saw three strategies for typed/untyped interaction
corresponding to impleentations (TR TS RP) the existence of these 3
fundamentally different approaches means that soundness is not a binary thing
we also saw that performance for these is more subtle

Next up .. speed up H 1 ... look for other strategies ...

go forth and do good science (be good scientists?)



- - -
# QUESTIONS

soundiness is a "sound up to X" statement, where X is a set of language features
http://soundiness.org/
https://cacm.acm.org/magazines/2015/2/182650-in-defense-of-soundiness/fulltext


for us we have two "soundiness" theorem:

- theorem i1 : soundness up to typed/untyped interaction (if no interaction
               then fully sound)

- theorem i2 : soundness up to functions and pairs across boundaries (if no
               pairs cross, then first-order is equal to higher-order)

Thorn invented a soundiness with theorem i2.

- - -

careful! performance is only up-to the same design decisions as reticulated
... but adding wrappers will only save cost of checking input for non-exported

- - -

shout out to Vitousek etal for working on a fix, set-based analysis?

- - -

  interop, non-binary soundness:
  - PLDI16 type providers
  - 

- - -

Back to PLs, the fish are immutable data the eggs are thunks.
The paper goes beyond thunks and allows two-way interaction 


- - -

Q. What do the names mean?

See the paper for H E 1

Q. What about Pycket?

In theory, Pycket demonstrated that a tracing JIT can solve the issues with H
and might solve any issues with 1.
In practice, there are constant factors and low-level issues in the way.
Until those practical issues are resolved --- which might be soon --- I believe
its still worthwhile to investigate across-the-board improvements to H and 1.



- - -

Q. (variational) First off, this technique is still interesting despite its
application to Reticulated being not so interesting. Second, in a language
with subtyping there might be more than one way to type a program or expression.
Have you thought about extending the technique to compare different ways of
typing the same program?
