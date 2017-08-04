pi-2017
===

Talk for PI meeting, August 7 2017.

Title: Transient Typed Racket

Time: 11:30am -- 12:00am ... ok darn that is kind of long



Thoughts
---

Wise person once said ...
mix barrel of wine, ounce of sewage ...
result is sewage

plays out over and over again ...
math proof, fatal error ...
P != NP proof, but for one mistake ...
Coq proof with an Admitted ...

(politics? other examples of the opposite?)
(systems security, one weak link)

you all know, an ounce of sewage is garbage

gradual typing, in the sense of mixing statically typed code
and dynamically typed NONSENSE in the same program ...
is an instance of wine and sewage ...

- - -

1. `e : t` been thinking about this
2. because Retic paper challenged me
3. TypeScript is sound, according to Retic
4. funny soundness, still merits (AA triangle), I never'd have thought of this
5. here's how I think of soundness, Typed Racket ....
6. ... sewage
7. research agenda, blame vs. soundness
8. design criteria : types === fast! optimizer! no rewriting!

X. challenge for transient, typed and untyped equally fast
   you just cant ... typed code needs to be defensive
   ... I think JIT technology to generate one of the 2**N configs would work,
   ... but yeah idk ... maybe there's anoterh way to goabout


Reynolds, types are a syntactic discipline for enforcing levels of abstraction.
 - complex numbers
 - queue
 - picture
 - string
 i.e. simple to talk about, some difficulty to implement

How does it work?
 everything annotated,
 everything checked,
 no exceptions.

If you do all that, and are careful about the meaning of types vs.
 the semantics of programs, then you can prove a useful theorem like soundness.


Soundness
---

1. Machine-Tag Sound

if e:t then e ~> c:k and either:
- e -->* v and v:k
- e diverges
- e -->* RuntimeError
- e -->* CheckError(v,k)

Need a completeness theorem ... guards every place where first-order values
 drop to primitive functions.

Gee maybe check the ICFP 2016 paper?

Can prove an efficiency theorem,
 with static typing you only get more efficient programs


2. Machine-Tag Sound, with Blame

if e:t then e ~> c:k and either:
- e -->* v and v:k
- e diverges
- e -->* RuntimeError
- e -->* CheckError(v,k',src)
  where `src` is one of the boundaries between typed and untyped code

How? By completely monitoring the interface between typed and untyped code.
You only _check_ flat values,
 but you monitor any other kind of value (procedures, lists, hashtables, ...)


3
  ???


4. Static Sound, with Blame (Typed Racket)
if e:t then either:
- e -->* v and v:t
- e diverges
- e -->* RuntimeError
- e -->* TypeError(v,t',src)

Need a complete monitor,
 complete monitors prevent the ounce of sewage

Can prove optimization?


Ergonomic Errors
---

Is there a word for the errors that your type system doesn't catch?
