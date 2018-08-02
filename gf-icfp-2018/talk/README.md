talk
===

TODO

[ ] outline
[ ] draft slides
[ ] give presentation
[ ] blog post

- - -

This is a talk about folklore as you all know folklore can be true can be false

Concerned with two pieces of folklore today. First soundness is binary proposition,
either sound or unsound. Now yes maybe that's not the whole story maybe that maybe
is clear already there are murmerings in the hallway (soundiness unrelated) and how
TypeScript is unsound but ``Nevertheless the world of unsoundness is not a shapeless,
unintelligible mess''

whats up well first the background [RESEARCH]
any programmer could say this is not the whole story because what about this
and that other ways to interface aren't these soundness holes but I guess its
okay what about PLDI16 type providers hm hm
academics dont seem to appreciate the question its debatable and anyway enough
to be done on the sound side in the binary world so nevermind

gradual typing makes the question important and you can see from the start (from
the start!) papers struggling to jive with ye olde type soundness. The cannonical
forms are diffent have new kinds of values to ... getting a little detailed
here ... anyway this soundness is NOT that soundness because exists untyped
code lost the closed-world assumption lost ALL TRACES of that assumption!
goes much further with work on typescript where you see lines like ``integration
with a formal semantics of jabascript is future work'' wtf brooo thats a big
if --- and hasn't come around yet. And then is the reticulated paper which
for lack of a better phrase has a type soundness theorem thats nothing much
like soundness at all, can have a term of type List(Int) and get a list of
real numbers furthermore can extract a real number from the list in typed
code! okay I am simplifying but all this is true. Its not soundness in ye olde
sense that much is clear. But the argument is this is reasonable because typed
code basic assumptions are preserved (and nothing goes wrong)

In the paper we state three notions of type soundness and we prove a
few properties relating them. I'd like to give you a preview of that now,
but instead of laying the formal groundwork and talking about type soundess,
I'm going to illustrate by talking about fish instead. Start with a body of
water add a pair of special red fish these are red snappers they fall in love
lay some eggs hatch babies live happily ever after. Now for this body of water
I claim it possible to prove a very strong fish soundness property, namely a
red snapper soundness that every fish at any point in time is a red snapper
fish and every egg is a red snapper egg how do you like that. This matches
ye olde binary soundness. Things change when we decide, for whatever reason,
that its expedient to open a gate between the lake and another unknown body
of water. What now of red snapper soundness? Its an interesting question.
So to mitigate the ecological impacts of the new foreign waterway the owners
of the pond enlists three emininent biologists (ecologists?) Dr A Dr B Dr C

Dr A is very concerned with the red snapper population, for their continued
success he wants to preserve the red snapper soundness at all costs and proposes
a plan where every fish incoming from the new water is subject to a full
anatomical screening. Nonsnappers go out the other side never enter the lake
for fish cant perform the same inspection without risking the larvae so invents
and ingenious cage-like device to wrap the eggs, so they hatch without issue
and can be inspected when old enough. Should be clear, this preserves the
red snapper property modulo these caged eggs

Dr B is the hands-off type. Proposes to do nothing with the lake, let nature
run its couse. When asked about red snapper soundness says "covfefe" all that
really matters is having an ecosystem

Dr C is sympathetic towards Dr A's plan but finds it outrageous, offers a compromise.
Instead of this full physical who knows how expensive lets just check the color
allow any red fish to arrive. If its not red, goodbye. If its not a fish, goodbye.
If its an egg, well its tricky because could be an egg containing a non-fish
or a non-red so to be safe check everything that hatches. If the egg floats
on, no big deal and we didn't lose one of the expensive cages. Overapproximates
but the work for each is so little shouldn't matter.

There you have it three expert opinions on how to connect the two ponds,
three variants of fish soundness: (deep) red snapper soundness,
(shallow) red soundness, and (erasure) ecosystem soundness.
Each independent and useful for different reasons, each based on different
border control. takeaway from this story is that soundness for a pari of
languages is quite different from soundness for a single language; the binary
point of view is inadequate to show the full range of useful options.

in the paper, have a higher-order erasure first-order checking strategies
the relation theorems ... if disconnected from outside, equal ... if
only first-order from outside then HO = FO ... in general error implication
(no comment on how easy or how folklore?)

thus concludes the first piece of folklore

The second major component of the paper has to do with performance.
Specifically about how these three checking strategies relate to one another.
One would expect (yes this low-level is probably right for a draft until M sees it):
- higher-order can have a serious cost, but soundness means optimizations
- erasure no cost
- first-order little cost even if optimized

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

Lets wrap up. We put different checking strategies for gradual typing into
a common theoretical framework and a common implementation. Its 3 back-ends
for one surface language. With this we can articulate the three differnt
notions of soundness that these can be show to satisfy, and we can formulate
relational theorems, first about soundiness and second about errors.
(We can also give the first alternate semantics for transient)
and compare the performance of three implementations of a full language

What do we learn? Soundness is not a binary proposition, there are compelling
reasons for an intermediate statement. Also the performance story is much
more subtle than previously expected. (than the literature would lead one to
believe)


??? is that really the end?


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
