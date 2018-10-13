talk
===

TODO

- [X] outline
- [X] draft keynote slides
- [X] draft slideshow slides
- [X] give presentation
  - [X] torture (2018-08-24 10:00am NEU 366 WVH)
  - [X] nepls   (2018-08-27 10:00am Harvard G115)
  - [X] icfp 1:30pm Wed Eric Tanter 22.5 min total, speak for 18.5
- [X] blog post

- - -

- - -
# SCRIPT

Hello everyone I'm Ben and I'm here to talk about A Spectrum of Type Soundness
and Performance

To start, here are two old questions. One asks wehter type soundness is a binary proposition, or whether there might be a useful property between full type soundness and unsoundness the second question asks about the relation between typ soundness and performance these are old questions in the context of a statically-typed language in the sense that we've had answers to these for decades bu I claim that in the context of gradual typing, these questions are extremely important

stepping back I'm interested in mgratory typing. Migratory typing is the idea of starting with an existing, dynamically-typed language and then designing a type system to reason about programs written in the language. The combination of the existing language and the new type system leads to two very similar languages and the goal is for these languages to share values with one another for example a typed context on the left that expects a function must be able to import an untyped function from the righht 

so thats a brief overview of migratory typing if youve heard of gradual typing or optional typing or concrete typing, they all fit in the same research langscape of mixing typed and untyped code within this broad landcsape we fortunately have some implementations of the ideas . in fact we have a lot . here are the names of a few languages that allow some combination of static and dynamic typing within this .. swimming pool .. of languages unfortunately its difficult to make meaningful distinctions in this space as a prime example, many mixed-typed languages claim to be type-sound so theres some agreement that type soundness is a useful property but if you look closely many of these guys state different soundness theorem of course the other prime example is performance every language wants to be fast, or at least not-dead, so again we have a zoo of individual claims the state of the art in comparing different approaches takes this form: that one language appears to be better than another, based on an ad-hoc translation of benchmark programs

in this paper, we break from tradition and perform a controlled study of these
diverse implementations heres what we do, we start with one mixed-typed
language and define three semantics, based on systems from the literature with
this setup, we can compare the theory of different semantics on common ground
then, using the model as a guide, we arrived at three implementations for the
typed racket surface language now we have three ways of running the same program
well see all of that today

first, the model we have a simple-as-possible grammar of types featuring a
coinductive type for functions an inductive type for pairs and two base types,
for integers and natural numbers finally, and this is very important, the type
for naturals is a subtype of the type for integers note that this disctinction
between naturals and integers is typically not enforced by the language runtime
or the underlying vm its a logical distinction --- something that types should
be able to do next we have a grammar of values that matches the types what you
should see here is a higher-order value, a data structure, and two atomic
values that are in a sub-set relation with one another this subset relation is
extremely important for migratory typing it reflects the way that
dynamically-typed programs use predicates to identify ad-hoc subsets of the
value domain
next we have a mostly-standard grammar of expressions the interesting part are
these two boundary terms, that let an expression mix typed and untyped code
finally there are two typing judgments and he rules here show how they depend on one another

in this model, we can write some curious well-typed expressions
in a context where fib is afunction expecing a natural number, norm is a function
expecing a pair of naturals, and map expects afunction on naturals, we can write
wel typed expressions that apply these functions to dynamically-typed values

after moving the untyped vlaues to the right and the typed contexts to the left,
we arrive at this pictorial representation. clearly, the types that the contexts
expect do not quite match the incoming values --- so theres a question, what to
do at runtime

I'm going to explain three approaches to enforcing types at runtime. as we go,
I'll show how systems from the earlier slide gravitate towards these strategies

first, we have the H for higher-order approach the goal of the higher-order semantics
is to enforce full types at the boundary betwene typed and untyped code
for our examples, if typed code epxects a natural number but receives an integer
the semantics throws a runtime error if typed code expects a pair of naturals
but recieves a pair of negative numbers, again the untyped value is rejected
if typed code expects a function on naturals but recives some untyped lambda,
ten the value is conditionally accepted provided it lives up to the type
in particular the function is allowed to cross the boundary in monitored form
if typed code applies this function to an argument, then the argument is rtansported
back to untyped-land, the untyped function is allowed to compute,
and the result then crosses back, along a boundary, to typed code. in this case
the result does not match the type, so the higher order semantics can point to
the boundary at the top of this slide to say that either the function or the
type annotation needs to change

that this higher-order approach and again the intuition is to enforce full types I know of four systems that implement this approach

next is 1 for first-order the goal here is to ensure that the evaluation of typed
code doesn't get stuck by checking type constructors at the boundary
so if typed code expects a natural and receives a negative number, thats rejected
as a type-constructor mismatch but if typed code expects a pair and receives a pair,
its accepted and simiilary if typed code expects a function and receives a function
in both cases, the outermost shape of the value matches the outermost shape of the type

things get a bit more complicated when typed code interacts with one of these structured values
for the case of a pair, whats happened at the boundary is that we let two negative integers sneak into typed code in general there could be anything hidden inside that pair, so I've colored the first and second component differently --- typed code cannot trust them
as the computation proceeds, and this pair hits a selector

(revisions end here)






TODO gradual guarantee?

TODO hard to get fair and insightful comparison across languages

TODO no more unsubstantiated claims we want to do science more than that
don't want just a classification scheme for cataloguing what exists want
a predictive model to guide and anticipate future work in the area

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

  ;; seen 3 ways of running the same programs, 3 different behaviors
  ;; what does this mean for type soundness?
  ;; [slide H 1 E at top (1/5), 3 columns with shrunken picts]
  ;; classic soundness, 3 clauses
  ;; 3 columns H 1 E soundness
  ;; folklore : all-or-nothing? NO for a mixed-typed language
  ;; ... at least three points in the design space [back to 3-columns]
  ;;     the all-or-nothing view confuses 1 with erasure whether or not you find
  ;;     the middle soundness useful, its certainly different (meaningful distinction)
  ;; we can say more about the differences ... let me make this more precise
  ;;  all know practical benefit of soundness is ruling out runtime behaviors
  ;; a typed language rules out all such errors
  ;; higher-order gets some --- in particular ...
  ;; erasure gets a few (in the typed code)
  ;; first order gets a few more ... 

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
