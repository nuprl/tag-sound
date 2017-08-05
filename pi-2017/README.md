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

If "preservation types" and "blame" are 2 dimensions, then there are 4 soundnesses

### 00. machine-tag sound

#### soundness

if ⊢ e : τ then e compilesto c and ⊢ c : k and either:
- c -->* v and ⊢ v : k
- c diverges
- c -->* Ω
- c -->* CheckError(v' k')

#### stuck

define stuck configurations,
 not stuck iff never break preservation


#### efficiency

if e0 ⊑ e1 then e0 <~ e1
aka. if no fewer types, then no less efficient (perhaps more efficient)


#### static types not preserved

∃ e . ⊢ e : τ
and running e yields a value with an incompatible type


### 01. machine-tag with blame

#### soundness

if ⊢ e : τ then e compilesto c and ⊢ c : k and either:
- c -->* v and ⊢ v : k
- c diverges
- c -->* Ω
- c -->* CheckError(v' k' src)
  where src refers to the static boundary where v entered typed code


#### stuck

define stuck, same as 00


#### efficiency

chaperones allow optimizations

chaperones also have cost, so programs can slow down in another sense


#### static types not preserved


### 10. type-sound
- nondescript runtime type errors
- not tracking blame ~> more space efficient (coarser equality on contracts)
- never stuck, with respect to "interpreter" on static types
- complete monitoring ~> no sewage
- chaperones => more unsafe ops, but more allocation & indirection


### 11. type-sound with blame
- runtime type errors point to one static boundary
- harder to collapse contracts
- otherwise same properties as 10
