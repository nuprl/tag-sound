talk
===

TODO

[X] outline
[X] draft keynote slides
[ ] draft slideshow slides
  X basic components (ugly if necessary)
  - basic show
  - animated components (ugly if necessary)
  - decide color scheme
  - nice
[ ] give presentation
  - torture
  - nepls
  - icfp
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
  - picture is mixed, quite mixed
    cannot just optimize because boundaries and abstractions
9. future

- - -
# SCRIPT

1
Hello this paper is about gradual typing but this talk is really about two
pieces of folklore folklore I is the belief that type soundness is a yes-or-no
proposition namely a langauge is either type-sound, unsound, or has a bug ---
the space in between is useless folklore II is the belief that adding type
information to a program can only improve performance in that it gives a
compiler more information about invariants and nothing else as you know the
thing about folklore is it can be true and useful or false and misleading the
goal of this talk is to show that neither claim is very true (or useful) for a
language that allows types and utnyped code to interact and that said to
substitute an accurate picture based on the content of our paper


2
(lets get started) this is a function the label on the left says that this
function expects triangles as input and the label on the right says it produces
triangles as output and yes if we run it on a triangle we get back a new
triangle (tri -> green tri) if we run it on something that is not a triangle,
say a square or a list of triangles or --- since this is a higher-order
language --- another function, then the result is undefined it might crash our
function and it might compute a nonsense output so theres a danger of crashes
and silent failures

this is a larger function its label says it expects any kind of input and may
compute any kind of result if we look inside this function we see its composed
of a few other functions, some total some partial and so we see that a function
can be composed of other functions and really a program is just one big
function composed of moving parts that handle and transform values

of course a program can go badly if one of the functions inside receives an
invalid input what we have here is an unsafe language that is a categorical bad
lets move on and focus on safe languages a language is safe if every labeled
function in a running program is guaranteed to get a correct input

one way to build a safe language is to limit the partial functions to one
built-in set require that every user-defined function be total over the value
domain and protect these partial functions with a scanner that checks the basic
shape of input to the partial functions if the scanner finds invalid input it
raises an alarm to halt the program pros: (1) this technique gives a safe
language (2) it offers some flexibility in gluing together programs cons:
(1) these scanners add a little overhead to look at values (2) and the user
doesnt have the freedom to make labeled function this strategy is called
dynamic typing and thats all I want to say about that for now

3
a second way to build a safe language is to add rules for how these components
can fit together starting with the delta functions add labels assume correct (!)
then labels for user-defined functions to make sure every labeled function gets
correct input this severly limits the set of programs the language can express
but offers two benefits first user-defined functions can (must?) have labels
and second since were guaranteed correct input theres no need to check the
input to the primitives we can use the partial functions directly additionally
the language of labels can go beyond the scanners language to anything that
fits in our logic as opposed to what we can efficiently decide at runtime in
contrast to the previous approach this is called static typing one comment
before we move on if the type system was unsound then it would not be true that
every function gets correct input and unless the primitives are once again
guarded theres a change the program goes horribly wrong so this is where that
first piece of folklore comes from --- an unsound static type system is missing
one of the main benefits that a programmer can trust the types its just a bug

4
now for the main event weve talked about static typing and dynamic typing lets
talk about ways to combine the two safe-language strategies in one-and-the-same
language the goal is simple just allow unlimited connects between the two any
statically typed function can now receive its input from a dynamically typed
context how now do we do safety?

in practice, three reasonably-successful strategies have emerged I'm going to
call these the higher-order erasure and first-order strategies ... the paper
spells out their connection to existing languages (?)

5
(zero a first thing we could try is inferring labels for the dynamically typed
bits and checking that all the labels are respoected people have tried this the
problem is called type reconstruction and its difficult thats all for today)

the higher-order appraoch keeps the dynamic and static components as they are
and guarads the boundary between with new conversion functions depending on the
direction the boundary functions either check that an untyped value matches a
type or protects a typed value its best to go through some examples if
expecting a triangle use a camera to check triangle? if expecting a list of
triangles check that input is a list and check triangle? for each element if
expecting a function on triangles then return a new function that checsk the
output more generally a function needs to protect its input and check its
output so lets talk about protection the reverse direction for a triangle
protection is a no-op same for a list of triangles and for a function on
triangles check that input is a triangle thats all with these higher-order
enforcement at boundaries its guaranteed that every value in static code has
the correct label --- with the caveat that some functions are now partial in a
new way and so both sides have exactly the same benefits as before

implemented in TR gradualtalk tpd ? ... they really deserve a shout-out

the erasure approach is a much simpler way to build a safe langage instead of
enforcing the boundaries with special treatment it allows any value to cross
between this means typed code can receive input that doesnt match the label so
the solution is to drop the labels and use checked primitives instead of
unchecked ones this is now safe for the same reason the dynamic language was
safe the types are still useful for static analysis and overall its much
simpler the main complain i have about this approach is that types no longer
mean anything at runtime you begin with a statically well typed program and
nothing about the types is guaranteed preserved the types do not define
abstractions nobody can build abstractions limited to runtime abstractions but
again its safe mission accomplished

implemented in typescript hack and many others

now for the first order approach I think the main insight to understand is that
we want a safe program and the static-typed code is safe provided the unchecked
primitives dont get input outside their domain (2) the domain is based on the
top level structure of the data suppose we have a simple typed function expects
a triangle well this is safe if guarded with a shape check suppose its a little
more complicated expecting a function apply primop to the result then safe if
check that input is a function-shape and its result has triangle-shape more
generally the first-order approach guards the boundary with first-order checks
and then guards elimination forms --- cod! --- with more first-order checks
this gives the invariant that every value in typed code has the same top-level
shape as its label and yes this is enough for safety limited optz limited
abstractions

implemented in reticulated and pioneered by vitousek (maybe henglein gets
credit hard to say)

[[ punch line didn't talk about language for primitives it was untyped all along ? ]]

6
so weve seen there are at least three ways to make a combined safe language
from typed and untyped sub-languages I claim that each of these approaches has
merits the higher-order approach gives the strongest guarantees the erasure
approach is trivial to implemnet and easy to explain to a programmer the
first-order approach is simple to implement and might provide enough assurance
for everyday use (unknown) one very important thing is that first-order doesnt
require proxies and no matter how useful proxies are they are still rare and
even when implemented "correctly" theyre still probably not contextually
equivalent (the worry is not equivalence the worry is FFI segfaults)

if you agree with me about the merits then youll agree type soundness for such
a language is not a yes-or-no proposition but rather there is at least one
useful statement in between in fact theres a whole family of statements the
paper gives two more (in appendix) and I can think of a few more all depends on
how to enforce types

... three choices with consequences for simplicity compatibility explainability
and also performance

folklore 1 is out ... folklore II is about performance so lets focus on that

7
suppose we start with a fully dynamic program and one-by-one move componets
into the statically typed region this is one way of adding type information to
a program if there are N components then we have 2^N ways (gosh this is bad)
combinations, which I'll call configurations from now on, at a glance we can
make some conjectures about performance for higher-order typed code has strong
invariants for optimization but the cost at boundaries may be expensive for
erasure no invariants but no cost at boundaries will be parity with
dynamically-typed (THE BASELINE) and for first-order have weak invariants and
unit costs spread throughout in fact the literature has such conjectures

but the only way to really know is to measure so that is what we did for this paper

we started with racket and typed racket the standard typed racket compiler
compiles types to higher-order contracts erasing types is straightforward and
we added a new compiler that takes the types disables the normal optimizer and
adds first-order protection checks now for one program we can run it three ways
and compare the results apples to apples

we took 10 functional programs ranging in size from A to B lines of code and C
to D modules for each program we ran all configurations the #mods tells you
this was a modest-sized experiment I dont think it took more than 1 month to
collect all the data

great

8
the results were a bit surprising heres two axis the x is the number of type
annotations, increasing, the y is overhead relative to fully untyped now going
to plot representative results for the three strategies for erasure obviously
adding more types does not hurt performance a little less obviously it doesnt
improve performance either now you could take a closed-world assumption and
optimize based on the erased types but if that assumption is ever broken were
back to dangerous unsafe land for higher order we see a serious umbrella shape
depending on the trace of the program if values frequently cross between typed
and untyped code and the data is big or the boundary is higher order then
theres quite a cost but on the other hand if the program is fully typed or
nearly so then those optimizations made possible by type soundness start to
outweigh the costs we see a payoff for trustworthy types now for first order
the overhead is roughly a linear function of the number of type annotations the
left half of this figure should not be surprising because obviously first order
pays a unit cost for boundaries its something always but never severe (never
traverse a list etc) but the right half of the figure this is saying even with
no boundaries theres quite a cost of checking the elimination forms in typed
code it adds up the fully-typed configuration usually not the worst because we
do some optimizing (could definitely do more) but not much further than type
constructors because thats all soundness guarantees in the graph thusly there
are two funny inflection points, first where H exceeds 1 and second where H
exceeds E .... (silence on purpose)

at any rate, adding type information is 

9
allright time for new folklore

1. soundness is a statement about the ability to create new abstractions;
   this may or may not be desirable --- for simplicity, ease-of-use, cost of
   enforcement

2. Perf \propto Inv(t) * (Opt / Dyn)
   instead of performance proportional to the number of types, with implication
   `Perf \propto t * Opt`, truer formula is this one --- consider the invariants
   those types establish, multiply by ability to optimize, and divide by the
   cost of dynamically establishing invariants on untyped components. In a
   statically typed language Dyn is close to 1 (not exactly for input data) so
   fair to ignore and Inv is identity function, but look its missing the point
   for gradual

10
where to we go from here???????

first explore other soundnesses unclear whether to useful in practice

second try changing the performance landscape

third probably useful to combine approaches choose 1 vs H depending on the
perforamnce consequences

ayyy


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

