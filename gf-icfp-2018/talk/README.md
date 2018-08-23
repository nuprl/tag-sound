talk
===

TODO

[X] outline
[X] draft keynote slides
[ ] draft slideshow slides
[ ] give presentation
  - torture (2018-08-24 10:00am NEU 366 WVH)
  - nepls   (2018-08-27 10:00am Harvard G115)
  - icfp
[ ] blog post

- clarify, don't actually have semantics for everything in the figure


- - -
# OUTLINE

1. folklore I II
2. disorganized space, attempts to organize
3. main contribution: order via semantics
   other contribution: theory, systems, developers
5. 3 semantics, position systems
   (Pyret etc. in between, blanks = future)
6. 3 implementations
   (equipped with new understanding ... added points to figure)
7. relative performance results
8. what does this mean
   - for theory = different soundness, for a pair, missing!
   - for systems = performance consequences of the semantics,
                   can we improve? idk,
                   can we trade/swap idk
   - for developers = need to know semantics for debugging
9. the end thanks


- - -
# SCRIPT

1
to get us started here are two folklore statements about type systems first
type soundness is all-or-nothing; either a type system is sound (perhaps up to
certain features), or it is unsound and its not worthwhile to make further
distinctions second is that adding type information to a program can only improve
its performance; in other words a typed program might run faster if a compiler
can leverage the types for now think about whether you believe these are true
and we'll revisit near the end of the talk

2
the paper is about languages that combine typed and untyped code
here are the names of a few such languages
there are a lot of names these are organized by date because
right now, at the start of this talk, there aren't many better options
we could organize by language but thats not much better than discrete topology,
we could group by origin academic-lab vs industry-lab ... also not useful,
we could group by those with claims to a type soundness guarantee but theres
 an issue the soundnesses are different heres TR vs. Reticulated (pasted from
 papers) and they are different!,
we could also try to group by performance ... fine, slow, dead ... but this
 is worst of all because its across different languages AND different benchmarks

3
the main contribution of this paper is to categorize different systems by
their semantics; in particular, by the strategy they employ at the boundaries
between typed and untyped code

conceptually, we start with a mixed-typed program, split it into statically
typed and dynamically-typed parts, and focus on what happens when values cross
between the two components (parts? principals?) at runtime

to clarify, our approach to modeling is to start with one surface language
with notions of statically typed and dynamically typed code and then define
three semantics that are basically equal up to their strategy for checking
values at a boundary for each semantics we can then talk about its soundness
with respect to the surface typing systems and make formal comparisons between
the systems

we then used the models as a guide to build three implementations so that we
could perform the first apples-to-apples comparison between three approaches
on identical program

between the models and implementations this lets us compare the theory,
performance, and practical consequences of each approach in a scientifically
sound manner

(somewhat proud to say, this is the first controlled experiment of its kind)

5
back to the outline slide, we have three semantics the main differences between
them is what they do at the boundary between typed and untyped code ... when
an untyped value crosses in, what happens?

to explain I need a little formal machinery a small language with a static typing
system and a dynamic typing system

... types for natural numbers integers pairs and functions the type Nat is a subtype
of the type Int this is very important later for values need natural numbers
integers pairs and functions the set of natural numbers is a subset of the set
of integers functios are split into two parts, typed and untyped take as given
a language of expressions the critical part is two boundary expressions dyn/stat
these interact with the typing systems ... a statically typed epxression can
embed untyped code and a dynamically-typed expression can embed statically-typed
code ... and now we can talk about program that combine stiatic and dynamic
typing, for example this program that applies a statically typed function to a
dynamically typed value this program is well typed but as you can see something
interesting is going to happen when we run the program ... this value (-1,-2) is
going to cross a boundary from the dynamically-typed world into the statically
typed world, and the static world expects a pair of naturals

wouldn't be well typed, but questionable what to do at runtime

NATURAL
now onto the three approaches the higher-order approach rejects this interaction,
if (-1,-2) meets a boundary expecting (Nat,Nat) then rejected because components
are not natural numbers more generally higher-order enforces a pair type by
asserting the value is a pair and recursively checking its components for other
types, accepts natural numbers for Nat accepts integers for Int thats
straightforward and for functions checks the value is a closure and wraps it
in a new closure that encapsulates the boundary if youre familiar with contracts
for higher-order functions this is exactly that other combos are errors

bottom fully enforces types --- either by exhaustive checking if possible and
by monitoring future behaviors otherwise

back to the outline, TR GT TSC are examples of higher-order gradual typing
systems

ERASURE
next erasure the erasure approach does not check anything at the boundary
for our example program, it invokes the function with the ill-typed pair
come what may more generally for pairs anything goes for naturas and integers
anything goes and for functions anything goes more simply anything goes

thats erasure and its a popular way to combine static and dynamic typing
many systems take this approach and not just for laziness, its based on a view
of static types as a pure syntactic artifact

FIRST-ORDER
finally the third approach is the first-order as the name suggests the idea is
to check first-order properties at boundaries and do not use monitors ...
before with higher-order we saw a wrapping-lambda to check the future behaviors
of a function; nothing like that for first order all checks that are going to
happen, happen right at the boundary the literature has a few strategies for
making due with first order checks the one we focus on is the transient strategy
implemented in reticulated python because its the only one that handles untyped
values the others restrict untyped code so for example cannot define a function
back to our running example when this pair reaches a boundary expecing a pair
of naturals the transient first-order approach says OK and lets the pair through
more generally the strategy is to enforce type constructors at the boundary
this is looking to establish an invariant that every value in typed code matches
its static type constructor

this alone is of course not enough to preserve the invariant because back to our
example if the function extracts an eleemnt from the untyped pair its going to
have a integer where the type annotations expect a natural number so in addition
to the normal boundaries transient conservatively treats every selector operation
(like first, function application, etc) as a boundary that way the result of
first gets a check and we're invariant

the details are not so imporatnt, suffice to say theres an extended notion of
boundary and these are the boundary checks

this completes the picture ... other first-order systems are nom and dart but
these have stronger type soundness because they restrict the untyped code ...
in between approaches we have thorn and pyret and strongscript

6
with this understanding in hand we added two points to the space building off
typed racket (blip, blip)

to explain how we added these implementations, it helps to know a little about
typed racket given a program TR expands the macros, type checks the expanded
program, optimizes the typed code, compiles the types to boundary checks, and
runs the generated racket code

TR-E is a type-erased racket ... the back end is different it type-checks
but does not optimize (because the types are not enforced!) and runs the plain
extracted program

TR-1 is a transient racket it type checks changes the boundaries and runs
the erased un-optimized program the lack of optimizations is AN ISSUE

with three implementations (3 compilers?) we can now take one program that mixes
typed and untyped code and directly compare the performance of three semantics
this prepares the way for us to answer a more interesting question as a programmer
explores the space of mixed-typed programs how does the choice of semantics
affect performance? 

(there is a threat to validity with how we pick one type assignment, but it
 seems unlikely that threat should affect relative performance of
 implementations)


with three backends have 3 ways of running a program so we did just that for
a systematic performance evaluation took 10 functional programs mostly from
proir work on typed racket ... these programs range in size, they're not very big
the largest in lines had xxx the largest in modules had yyy for each program
considered all ways of adding types and measured the full lattice

8
the most interesting result is what happens to a typical program as we add types
on the x-axis is discrete scale of number of typed modules if program has 3 modules
here's the histogram ... the y-axis is overhead relative to untyped so theres
speedup and slowdown

for higher-order the curve is an umbrella shape middle region: when typed and
untyped code interact there is a cost and it can be very high usually many
configurations have the cost right region: fully typed or nearly typed benefit
from optimizations and dont suffer the costs made possible by type invariants /
types are enforced

for erasure performance is uniform across the board on the right this means
nothing to be done optimizing because cannot assume the value matches its
static type (you could optimize C++ with undefined behavior ... or assuming
fully-typed but then why not use one of the ecellenet typed languages to me
gradual typing really only makes sense if you have untyped code you want to
work with and support)

for firts order perofrmance goes down as the number of types goes up on the left
this should make sense boundaries have  acost on the right its more surprising
this is the cost of those modified boundaries the unit cost for every selector
and elimination form in typed code

with all three lines down there are two very intersting points on this graph
for lots of mixed-typed programs E < 1 < H but as number of typed components
increases likely to get E < H < 1 a flip and going further its quite possible
H fastest of all

what this means is, the current performance landscape is subtle too soon to
generalize and theres much to be done predicting the cost of typed untyped
interaction

8
in the beginning I posed two folklore results hope its now clear that these
are not true in a language that allows typed and untyped code in terms of ...

in a language that mixes typed and untyped code these are not the whole story
not entirely true

... soundness we saw three ways of mixing that preserve different invariants
in terms of performance adding types can enable the optimizer but it can also
add boundaries with cost ... at minimum replace mental model with
Perf ~ Inv(t) * Opt/Dyn performance is based on the invariants those types imply,
and it proportional to the optimizations the invariants enable and inversely
proportional to the cost of establishing those invariants

what does this all mean?

for the theoretician, it means the literature is too narrow on type soundness
for gradual languages theres multiple ways to do soundness each with different
tradeoffs and in general its a question of soundness for a pair of languages
rather than soundness for one language

for the language implementor, performance is difficult to predict for H and
complicated invariants interactions ... adding types to a program not necessarily
good but we're lacking guidance for users

for the working programmer, the main implications are for debugging in H the
error points to a boundary in E the search space is the whole program but not
guaranteed to detect in 1 ditto --- whole program and might not detect

9
going forward look for new soundness  new combinations  more performance ...

idk

the end thanks

go forth and do good science (be good scientists?)



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
