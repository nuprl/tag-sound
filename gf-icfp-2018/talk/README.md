talk
===

TODO

[ ] outline
[ ] draft slides
[ ] give presentation
[ ] blog post

- - -

Hello I'm Ben going to talk about gradual typing, language design, type
soundness, and performance.

That's the technical overview. At a higher level the talk, and the paper,
deals with two pieces of folkore --- the kind of things you might hear in the
hallway, or know without knowing (implicitly accept as truth).

1. soundness is a binary proposition
   (TypeScript is unsound but ``Nevertheless the world of unsoundness is not a shapeless, unintelligible mess'')
2. adding type constraints to a program improves performance

The high-level point of the paper is to analyze these two statements in the
context of gradual typing (or more accurately migratory typing)

Lets set the stage. Or: What I mean is this. Have two languages, one untyped
language and one typed language. Both have similar expressions, values, and
semantics. Both have a type system (or well-formed judgment) but one is
stronger than the other in a sense that I'm not going to make precise basically
good(e) implies good(e'). Doesn't matter for the talk --- have two similar
languages, but one has stronger guarantees than the other. The gradual/migratory
typing question is, what happens when we combine them?

What do we do to combine?
What happens to soundness?
What happens to performance?

In the paper, we start with a pair of lambda-calculus languages and go into
detail with three strategies for combining typed and untyped code.  To a first
approximation, these strategies come from TypeScript, Reticulated Python, and
Typed Racket. (Of course, many others do the TS and TR approaches, still others
are similar to RP.) Leads to three pairs of soundness theorems in our formal
model, and leads to three implementations of Racket / Typed Racket that we
measure performance for. 

That's all very good, but you don't need all this formal machinery to
understand the three strategies. So let's forget about functional programming
for a minute, and instead of two languages, we'll have two bodies of water.

On the right we have a small closed-off pond. This pond is home to a pair of
fish, red snapper fish to be precise (Lutjanus campechanus). Its a small world
in this pond and over time the fish meet, exchange their software, and then
the pond is not so empty anymore but also has little fish eggs. To be precise
these are red snapper eggs, made by a pair of red snappers, and if they hatch
they'll hatch into a little copy of their parents (same genus, same species).
If these are the only two processes in our pond:
- RSF + RSF --> RSE + RSF + RSF
- RSE --> RSF
then we can guarantee that at any point in the future, the pond contains only
red snapper fish and red snapper eggs (defined as 'eggs that hatch into snappers')
I call this the red snapper property.

On the left we have a flowing river. All kinds of fish and fish eggs live in
the river, depending on the time of year. Consequently we can't prove a red
snapper property for the river. The analogous property is much weaker; namely,
at any point in time its all fish and fish eggs.

There's our ecosytem. Two disconnected bodies of water with two populations
that satisfy two different properties. (The property on the right is stronger
than the property on the left --- that doesn't actually matter.)

One day three biologists visit the pond and discover it is dangerously low
on entropy. Something must be done else the fish are going to die. They all
agree, the best course of action is to divert the nearby river to flow into
our little pond. They disagree on whether something else should be done to
preserve the existing red snapper population.

Dr. H insists that the red snapper property be preserved. His plan is to put
an inspection station between the river and the pond. Whenever a fish arrives,
perform a DNA test to ensure its a red snapper otherwise send it back.
Whenever an egg arrives, well, they don't have the techology to inspect an
egg but Dr. H has prepared with an ingenious monitoring device that can
incubate the egg until it hatches, keeping the new organism separate from the
pond until a technician can perform a DNA test. With the inspections + monitors,
Dr. H claims we have a straightforward generalization of the red snapper property:
in the future every fish is a red snapper and every egg is either a red snapper
egg or a monitored egg. 

Dr. E doesn't understand all the fuss about the red snapper property. She
proposes to open the pond and let nature run its course. Both bodies of water
then satisfy the weak fish soundness property and we're done. Nice and simple.
(Simple as possible and no simpler.)

Dr. 1 is torn. On one hand, he is sympathetic towards Dr. H's plan, because his
office overlooks the little pond and he enjoys watching the red snappers. It
just wouldn't be the same aesthetic with different fish swimming around. On the
other hand, he finds the inspection station and monitors to be impractical.
See he's already thinking ahead to our next topic, performance, and wondering
how much time and $$$ its going to cost to preserve red snapper soundness.
So Dr. 1 proposes a compromise. We add an inspection station that just checks
the color of incoming fish. Red fish are ok, other fish go back. For the eggs,
all eggs pass the inspection but the pond gets a supervisor who checks the
color of every hatchling. If its not red, goodbye. This, Dr 1 says, guarantees
a "red fish" property. Its stronger than the fish property, but weaker than
the original red snapper property.

The point of this fish story is to show that if we combine two systems with
different guarantees, there are at least 3 properties that we might try to
preserve in the combined system. In the context of gradual typing systems,
Dr. H corresponds to the higher-order approach taken by systems like
Typed Racket TPD Gradualtalk. This higher-order enforcement can guarantee
a natural generalization of a standard type soundness theorem. Types enforce
levels of abstraction.
Dr. E's erasure approach is similar to what happens in TypeScript, Hack, PyType,
Strongtalk .... where the optional types are used only for static analysis
and have no effect on program behavior.
Finally Dr. 1's approach matches Reticulated Python, which ensures that
typed code doesn't get stuck by sprinkling first-order checks around every
elimination form in typed code
(wow, quite a lot to illustrate in this paragraph)

Just as the doctors were worried about complexity, designers of gradual typing
systems were also worried about performance when they introduced alternatives.



[Conclusion] Soundness for a pair of languages is different than soundness for a single
language. For a pair, 




# OLD

The second major component of the paper has to do with performance.
Specifically about how these three checking strategies relate to one another.
One would expect (yes this low-level is probably right for a draft until M sees it):
- higher-order can have a serious cost, but soundness means optimizations
- erasure no cost
- first-order little cost even if optimized

Touches on a second folklore: adding constraints improves performance. Here
the types are the constraints.

To test this, we have three implementations for one surface language (typed racket).
This is not a perfect comparison because the first-order has little optimizations
and nothing for error messages, so let me just sketch what we found.
(as a function of increasing types)
erasure = flat,
first-order = line,
higher-order = umbrella

what does this mean? first the conjectures are right to some extent,
higher-order is the only extreme one and it is quite extreme, erasure is flat,
first-order is not extreme (well I already said that)

but the deeper meaning, first higher-order is fastest at right --- even when NOT
100% typed --- because things inside the boundary can run full-speed++.

   Diagram:

   |   ______
   |  /      \
   | ------------
   |           \_
   |______________ t
               !!!!

second the cost of first-order is more-or-less linear in the number of type
annotations! each type annotation may add a check, just like the hatching eggs
need to conservatively guard every elimination form in typed code! Adds up.
Typically adds up slower than higher-order, but thats not always the case we
found ONE counterexample.

(in the paper you'll find ....)
Lets wrap up. We put different checking strategies for gradual typing into
a common theoretical framework and a common implementation. Its 3 back-ends
for one surface language. With this we can articulate the three differnt
notions of soundness that these can be show to satisfy, and we can formulate
relational theorems, first about soundiness and second about errors.
(We can also give the first alternate semantics for transient)
and compare the performance of three implementations of a full language

What do we learn? Soundness is not a binary proposition for pair of languages,
there are compelling reasons for an intermediate statement. Thats just what GT
deals with ... other settings benefit too I'm sure.
Also the performance story is much more subtle than previously expected.
(than the literature would lead one to believe). Check the data in the
paper and form your own conclusions, but to me see a need for:
- optimize transient (go Vitousek)
- algorithmic higher-order improvements (revive Pycket?)

go forth and do good science (be good scientists?)

- - -

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
