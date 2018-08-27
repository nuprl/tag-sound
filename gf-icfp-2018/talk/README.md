talk
===

TODO

[X] outline
[X] draft keynote slides
[ ] draft slideshow slides
[ ] give presentation
  - [X] torture (2018-08-24 10:00am NEU 366 WVH)
  - [ ] nepls   (2018-08-27 10:00am Harvard G115)
  - [ ] icfp
[ ] blog post

- - -
# SCRIPT

s2
Hi. To start off, here are two questions. The first asks if type soundness is
a binary notion --- in other words, a language is either sound or unsound, and
anything in between is not important. The second asks whether adding type
information to a program can have a negative effect on its performance. At a
glance it seems like the answer to that one should be ``no'', because more types
should give an optimizer more to work with, and nothing else.

But as scientists, its our job to investigate questions like this systematically

Thats all I want to say about these for now, and we'll come back to the ideas
later.

s3
ok so I am interested in migratory typing which is the idea of starting with an
existing dynamically typed language desigining a static type system to reason
about programs written in this language and arriving at a pair of languages ---
one statically typed, one dynamically typed, that can interact

if youve heard of gradual typing, its very similar, but this constraint of
starting from a dynamically typed language is very important to me

with that said, related work on gradual typing systems and really any language
that combines static and dynamic typing is a good source of inspiration and the
work I'm here to present today started with me trying to make sense of this space

so the swimming pool here represents the design space of languages that combine
static and dynamic typing here are a few of the languages in the space, arranged
in no particular order. There are a lot of names. Unfortunately, theres not much
we can do to organize. One idea is to sort them by release date, from oldest on
the left to newest on the right, where the y-axis doesn't mean anything, but
this doesn't tell us much except some growth trend. We can try grouping by
where they came from. On the left is a cluster of research languages and on the
right are languages that came out of industry. Again the y-axis doesn't mean
anything, and the second column on the left is only because the first column
ran out of space. (Lets move on, this isn't a very useful distinction.) The
next thing I thought to try is grouping the languages by whether they claim to
be type sound, or whether they erase types at runtime. This is a little more
interesting, but if you dig deeper the papers that describe these type soundnesses
often have very different theorems! In the SafeTS paper for example, soundness
is just for the statically-typed part of the language ... theres no soundness
for programs that mix typed and untyped code. Another thing we can try is
grouping by performance, somehow. We need to be careful in comparing across
languages, but to a first approximation we can say Typed Racket is dead and
everything else I guess is not dead.

s13
You get the point, the space is a zoo.

s14
I'm aware of just one other work that attempts a scientific comparison, and
thats KafKa by Ben Chung and others.  Ben is here today, if you want to learn
more about that.

s15
Our work presents a way to organize this space by semantics. In the paper we
have three formal semantics for a common surface language, called the
higher-order, erasure, and first-order semantics. The names come from the most
important part of each, which is the strategy they use to enforce types at the
boundary between statically typed and dynamically typed code.

To be clear, one main contribution of our paper is a model for one mixed-typed
language, one surface-level type system, and three formal semantics. So then we
can take one program, validated by one static typing system, and compare the
results of running the same code three different ways.

Then using the model as a guide, we took Typed Racket as the surface language
and added two new compilers. The second main contribution of the paper is a
performance evaluation comparing the three semantics extracted from the
literature on equal source programs. This is the first evaluation of its kind
and I'm excited to tell you about it.

s21
But first, lets explain the model. We have a small grammar of types, and a
matching grammar of values. I claim these types are the simplest possible to
ask all the interesting questions about typed/untyped interaction; in particular
we have a coinductive type for functions, an inductive type for pairs, a base
type for integers, and a type for natural numbers that is a subtype of the type
for integers. On the value side, the natural-number literals are a subset of
the integer literals.

This subset relation is extremely important. It reflects how programmers can use
predicates to identify a subset of the value domain and make a logical distinction
between values that is useful for people, but the underlying machine doesn't
care about. In other words the language of types should not be limited by the
kinds of values the runtime system knows about.

And finally we have primitive operations and expressions. The non-standard part
of the expression language are these two boundary terms. A dyn expression
embeds a dynamically typed expression in statically typed code, and a stat
expression embeds a statically-typed expression in dynamically-typed code.

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
the lock is trying to indicate. In the model we monitor the untyped function
and check that every value it returns, forever more, is a natural number. If
not then higher-order can trace the violation back to this boundary. And that's
all you need to know to understand the higher-order semantics. It checks types
eagerly when possible, and lazily when necessary.

And here, I know of 4 existing systems that implement the higher-order semantics.

Next up is E for erasure. As the name suggests, the erasure semantics ignores
types at runtime, so all three examples go through despite the apparent type
mismatch. Many systems implement the erasure semantics. To its credit, it adds
the benefits of static type checking and type-based IDE tools and its very easy
to add this semantics to an existing language --- just use the existing language!

Now we come to the number 1, for first-order. The goal here is to enforce some
parts of the types, but avoid the higher-order lock we had before. For our
running examples, the first-order semantics we give in the paper rejects the
first one, where a negative number meets a nat boundary, but accepts the other
two. Because in the second case we expect a pair and got a pair, and in the
third case we expect a function and got a function. Theres more to say about
what happens when typed code goes to use the pair or function, but this is the
main idea, to enforce type constructors at the boundary.

This first-order semantics I've sketched is very similar to what Reticulated
Python does. In fact Reticualted was the inspriation for this --- first-order
is me trying to understand the essence of what they did. But other systems also
fit in this space. Pallene and Grace are vaguely similar to Reticulated's
first-order strategy. The others that I'm calling first=order do something a
little different, and all have stars next to their names because of that.
The star means these languages put restrictions on the untyped code. In short,
every value comes with a type, so its possible to check types at a boundary
with a subtyping test.

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
more severly the translations change type annotations in a program making it
much harder to identify a violation of the static types

also the surface language is limited (no untyped objects) and so obscures the
distinction between transient and concrete ... sometimes not possible to use
subtyping to check a value
aka
KafKa doesn't have untyped values ... part of the challenge is to get a value
from untyped code and figure out what it is; this is not a challenge in KafKa
because every higher-order value comes with a type spec. Still maybe useful for
semantics of a gradual language, but not for working with untyped code

- - -

Q.  ???

  interop, non-binary soundness:
  - PLDI16 type providers
  - 

- - -

Q. What about Pycket?

In theory, Pycket demonstrated that a tracing JIT can solve the issues with H
and might solve any issues with 1.
In practice, there are constant factors and low-level issues in the way.
Until those practical issues are resolved --- which might be soon --- I believe
its still worthwhile to investigate across-the-board improvements to H and 1.


- - -

Q. (for variational) First off, this technique is still interesting despite its
application to Reticulated being not so interesting. Second, in a language with
subtyping there might be more than one way to type a program or expression.
Have you thought about extending the technique to compare different ways of
typing the same program?

- - -

Q. Thorn / Nom / SafeTS

of course another way to deal with the cost of higher-order enforcement is to
just eliminate it, restrict the boundary types to first-order checkable things
at least three groups have worked out a theory of this its compelling but needs
more practical evaluation for me at least I don't see much point in combining
typed and untyped code unless there is some untyped (and actually untyped) code
you want to work with if not just pick one of the many excellent typed
languages and live at a higher level of abstraction ... hard to picture a
neutered untyped language being compelling

- - -

Q. combinatorial explosion

yes itd be great to do work case-by-case but look, the meta-statement in this
paper is ... too many unfounded general statements ... analogy to chemistry?
"meaningful distinctions deserve to be maintained"

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

Q. you say gradual but where is dyn

short answer: dyn is an orthgonal issue

long answer: I tried to avoid the word gradual, because the modern interpretation
is a static type system with a special dynamic type that has specific properties
the work I presented is not concered with static typing; we're about _if_ you
have a well-typed program with static and dynamic components, what happens at
run-time between those parts

- - -

Q. superceded by Vitousek at DLS?

thats an inspiring work, but doesn't present a formal semantics and doesnt
systematically compare ... they claim to have 3 implementations by do not
compare the performance

- - -

Q. please explain how transient first-order changes the boundaries
