talk
===

TODO

- [X] outline
- [X] draft keynote slides
- [X] draft slideshow slides
- [ ] give presentation
  - [X] torture (2018-08-24 10:00am NEU 366 WVH)
  - [X] nepls   (2018-08-27 10:00am Harvard G115)
  - [ ] icfp 1:30pm Wed Eric Tanter 22.5 min total, speak for 18.5
- [ ] blog post

- - -
# SCRIPT

Hi everyone. To get started today, I have two OLD questions on the screen.
The first question asks whether there could be an interesting point between
type soundness and unsoundness. The second question asks how type soundness
affects the performance of typed programs.

In a normal, fully-typed language these questions are closed. But if we move
from a typed language to one that mixes typed and untyped code, then we'll see
that the questions on the slide are the central questions guiding the research.

Before we get to that, lets begin at the beginning.
I am interested in migratory typing, which is the idea of starting with an
existing dynamically typed language, designing a static type system to reason
about programs written in this language and arriving at a pair of languages ---
a statically typed language and the original untyped language.

If you are familiar with gradual typing, migratory typing is very similar;
the main difference is this constraint of starting with a dynamically-typed
language, which leads to important distinctions.

With that said, gradual typing migratory typing and optional typing all face
similar challenges, so its helpful to look at the whole design space for
organizing principles.

Here are a few of the languages in this space, arranged in no particular order.
There are a lot of names.

Here are the same names, organized by when the first appeared. On the left we
have the oldest mixed-typed languages, on the right we have the newest. Again
its a lot of languages, and they seem to be multiplying into a small tower of
babel.

At this point I would like to organize the space based on some principles these
languages have in common, but unfortunately there is not much be to said.

We can try grouping by where the languages came from. About half, on the left,
are academic research projects. The others, on the right, came from industry
teams.

We can next try grouping the languages that claim to be type-sound, on the left,
with the ones that use types only for static analysis on the right. At first
glance this is better, but if you read the actual soundness claims of each
language on the left they're often very different! For example Gradualtalk
on the top, preserves types during evaluation, but Grace Pyret and Reticulated
preserve something more like type constructors than full types. So this grouping
is also not very informative.

One last idea is to try grouping by performance. We need to be extremely careful
in making performance claims across languages, but at the very least we can
agree that Typed Racket is "dead" and the others are more-or-less alive.

Ok you get the point, the design space is chaos --- disorganized.

TODO gradual guarantee?

To my knowledge there has been one effort to characterize existing systems,
and thats the work on KafKa by Ben Francesco Paley and Jan. KafKa presents
four translations from a mixed-typed language to a typed cast language, and
talks about how the translations relate to existing systems.

Today I'm going to show you a different way to organize, which is to start
with a mixed-typed language and present three different ways of running the
programs.

The three semantics are called the higher-order semantics, first-order
semantics, and erasure semantics. The names are meant to evoke the essential
part of each semantics, which is the strategy they use to enforce types at the
boundaries between typed and untyped code.

To be clear, one main contribution of our paper is a model for one mixed-typed
language, one surface-level type system, and three formal semantics. So then we
can take one well-typed program and compare its behaviors.

A second contribution is a meta-theory for these semantics. Each one enforces
different invariants, and these correspond to the different notions of soundness
in the literature.

The third and last contribution is that we used the model as a guide to implement
the three semantics for Typed Racket. Using this implementation we conducted
the first-of-its-kind controlled experiment to measure the performance of each
approach.

We have apples-to-apples soundness, and apples-to-apples performance.

Lets dive in to the model.
We have a small grammar of types, and a matching grammar of values.
The types include a coinductive type for functions, an inductive type for
pairs, a base for integers, and a type for natural numbers that is a subtype
of the type of integers.
On the value side, the natural-number literals are a subset of
the integer literals.

This subset relation is extremely important. It reflects how programmers use
predicates to identify a subset of the value domain and make a logical
distinction that is useful for people, but the underlying language doesn't care
about. This is the kind of thing that happens in dynamically typed languages
that a migratory typing system ought to support. Also its a statement that the
he language of types should not be limited by the kinds of values the runtime
system knows about.

And finally we have a simple language of expressions. The non-standard part
of the expression language are these two boundary terms. A dyn expression
embeds a dynamically typed expression in statically typed code, and a stat
expression embeds a statically-typed expression in dynamically-typed code.
The type system reasons about boundaries in a straightforward way.

In this model we can write well-typed programs that mix typed and untyped
code, like this, or with more readable syntax like this. On the left we have
three statically typed contexts and on the right three dynamically typed
expressions. All three are well-typed, so we can run them and see what the
semantics says about these three type mismatches.

First, lets do the higher-order semantics. The higher-order approach enforces
types at the boundaries. If the types expect a natural number and untyped code
sends an integer, higher order raises a runtime error. Similarly, if we're
expecting a pair of natural numbers and receive a pair of negative numbers,
then higher order raises an error because the components of the pair don't match
the type. Finally if we're expecting a function on natural numbers and receive
an untyped lambda, higher-order conditionally accepts the value. That's what
the lock is trying to indicate.

TODO explain details


TODO: checks all first-order properties immediately and all higher-order properties in a delayed fashion

And here, I know of 4 existing systems that implement the higher-order semantics.

Now we come to the number 1, for first-order. The goal here is to enforce some
parts of the types, but avoid the higher-order lock we had before. For our
running examples, the first-order semantics we give in the paper rejects the
first one, where a negative number meets a nat boundary, but accepts the other
two. Because in the second case we expect a pair and got a pair, and in the
third case we expect a function and got a function. Theres more to say about
what happens when typed code goes to use the pair or function, but this is the
main idea, to enforce type constructors at the boundary.

TODO: explain defense in typed code ... checks first-order properties at boundary,
 but has wider notion of boundary

This first-order semantics I've sketched is very similar to what Reticulated
Python does. In fact Reticualted was the inspriation for this --- first-order
is me trying to understand the essence of what they did. But other systems also
fit in this space. Pallene and Grace are vaguely similar to Reticulated's
first-order strategy. The others that I'm calling first=order do something a
little different, and all have stars next to their names because of that.
The star means these languages put restrictions on the untyped code. In short,
every value comes with a type, so its possible to check types at a boundary
with a subtyping test.

Next up is E for erasure. As the name suggests, the erasure semantics ignores
types at runtime, so all three examples go through despite the apparent type
mismatch. Many systems implement the erasure semantics. To its credit, it adds
the benefits of static type checking and type-based IDE tools and its very easy
to add this semantics to an existing language --- just use the existing language!

With that, we've just about organized the names we started with. There are three
missing ---- and here they are, StrongScript Pyret and Thorn fall between a
pair of semantics because they let a programmer choose to erase some types.

s43
Now lets revisit our question from before, about whether there might be different
useful notions of type soundness. I've sketched for you three ways of running
a program. All three act differently when typed and untyped code interact.
Do you think they all satisfy the same notion of type soundness?

No! of course not! In fact we had to develop three runtime-level properties
to capture what these semantics preserve. The higher-order judgment is a
proposition about types, the erasure judgment is just about well-formed expressions,
and the first-order judgment is about this K-of-t, which pulls out the top-level
type constructor from a type. Each semantics satisfies progress and preservation
lemmas for the matching judgment, but none of these are exactly like standard
type soundness.

...


Lets move to the implementations. Like I said in the beginning, we used the
models as a guide to implement the three semantics for Typed Racket. The
implementation for higher-order was already there --- for this we reused
Typed Racket's back end which macro-expands a program, checks types, compiles
types to higher-order contracts, and performs some ahead-of-time type-driven
optimizations. For erasure we re-used to expander and type checker, but then
erase the types. For first order, we again reuse the typechecker and then
enforce type constructors.

Neither erasure or first-order have an optimizer. For erasure this mostly makes
sense, because the types are not guaranteed to make any sense at runtime. But
for first-order you might be wondering whether its possible to use the type
constructors to optimize. That's true, but our first priority in this work
was to reproduce first-order as its described in the literature, to test the
informal claims that you see in those papers. Adding an optimizer to first-order
Racket is future work.

TODO as in the literature

With these implementations in hand, we set out to measure the overhead of
mixing static and dynamic code. For this we used an existing set of benchmarks.
We picked 10 programs, that range in size from 2 to 10 modules each, and measured
all possible mixed-typed configurations. Since TR allows any module to be typed
or untyped, this means we measured 2-to-the-4 to 2-to-the-10 configurations each.
To a sense of scale, I think it took less than 1 month to run all the benchmarks.
This URL has more details about the benchmark suite.

We present lots of results in the paper. The one that I found most interesting
is how the running time of a program changes (along the y-axis, higher is worse)
as the number of type annotations increases. On the next slide I'll show some
real data, but in general what we see is this --- higher order can have some
extreme costs when typed and untyped code interactions, but benefits significantly
from the optimizer. Erasure is just a flat line because types dont affect a
program's behavior. And first-order has a basically linear phenonemon, where
adding types adds overhead.

Lets see the data. These are points instead of lines, except for the green.
These y-axes aren't normalized in any way, so sometimes the cost of higher-order
dwarfs everything else.

I'm sure there's questions about these, but lets move on to the conclusions.

From the model, we saw three ways of running a program each with a different
notion of soundness. The higher-order approach preserves types and the others
preserve something weaker. As we know from theory, the purpose of type soundess
is to rule out certain illegal behaviors. Using the models, we can prove that
the weaker semantics catch fewer illegal behaviors, in the sense that whenever
erasure detects an error, first-order detects the same or an earlier error.
Similarly for first-order and higher-order --- that's what these superset
symbols indicate, the one on the left detects the most logical errors.
These are proper containment relations, and the examples we used to demonstrate
each semantics are proof of that. Bottom line, we have some meta-theory that
relates these different approaches.

TODO guaranteed same expressiveness of types

Regarding performance, we've seen that adding types can add overhead to a program
if those types need to be enforced at runtime. These bullet points are recommendations
based on the data we have --- in a higher-order system, its best to avoid type
boundaries by adding types to tightly-connected clusters of modules. That's
what I mean by packages. For first-order, I suggest adding types sparingly,
only to modules where correctness is crucial. And finally for erasure, you
can add types wherever you like, just keep in mind those types don't mean
anything at runtime.

The end.

(go forth and do good science)


- - -
# QUESTIONS

Q. you talked about a spectrum of soundness --- do you mean ``soundiness'' ?

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

Q. whats the connection to KafKa? didn't they already do this?

by contrast: (1) our paper starts with a common surface language and type system
and demonstrates three semantics, each of which preserves different properties
(2) KafKa starts with a common surface language and demonstrates three translations
into a common core language

instead of direct semantics, encode things in the KafKa type system

the paper is missing a connection between surface typing and core typing, and
the translations change type annotations in a program making it
much harder to identify a violation of the static types

also the surface language is limited (no untyped objects) and so its hard to see
the distinction between transient and concrete ... sometimes not possible to use
subtyping to check a value
aka
KafKa doesn't have untyped values ... part of the challenge is to get a value
from untyped code and figure out what it is; this is not a challenge in KafKa
because every higher-order value comes with a type spec. Still maybe useful for
semantics of a gradual language, but not for working with untyped code

2018-09-17
interesting question unfortunately so complicated to explain need to look at paper
no formal connection between source and target languages

- - -

Q. What about Pycket?

Pycket demonstrated that a tracing JIT can solve the issues with H
and might solve any issues with 1.
There are constant factors and low-level issues in the way of reusing Pycket.
Until those practical issues are resolved --- which might be soon --- I believe
its still worthwhile to investigate across-the-board improvements to H and 1.

- - -

Q. too many soundnesses

yes itd be great to do work case-by-case but look, the meta-statement in this
paper is ... too many unfounded general statements ... analogy to chemistry?
"meaningful distinctions deserve to be maintained"

- - -

Q. superceded by Vitousek at DLS?

thats an inspiring work, but doesn't present a formal semantics and doesnt
systematically compare ... they claim to have 3 implementations by do not
compare the performance

- - -

Q. why not F for first-order?

because we used 1 in the paper, because we used F to name a different underground
semantics in the appendix, because that semantics is very similar to Michael
Greenbergs "forgetful" semantics for space-efficient manifest contracts, because
"forgetful" starts with an "f"

... because F was taken. In the process of developing the first-order semantics
as inspired by transient, we realized there were at least two alternative
higher-order semantics that fit between these two in terms of errors. One of
these alternatives is very similar to M. Greenberg's _forgetful_ semantics for
space-efficient contracts, so we used F for that one.

- - -

Q. relation to Swords Sabry TH ICFP'15 / JFP'17

related, orthogonal --- thats about when to check, we're about what to check
(and we have soundess as guiding principle, they're exploring the space more
generally)

- - -

Q. Cython

Cython type checks Python/C code and extracts to C. Seems to be sound by limiting
OR delaying interactions to first-order types

e.g. cannot assign a Python list to a `cdef` array
     can assign an element of a Python `[int]` to a `cdef int`, and the assignment
      is guarded with a runtime check
