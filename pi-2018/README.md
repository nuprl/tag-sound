pi2018
===

Presentation for PI meeting, 2018-04-23

TODO
---

[ ] is baseline actually the same for all (except jpeg)?
[ ] 


EXTRA TODO
---

[ ] where would monotonic fit? is it just implementation?
[ ] critique the name "guarded"
[ ] REALLY need a name ... 'fishtank soundness' is not great
[ ] check kafka

Notes
---

### Important Points

soundness for pair of language
specification vs. implementation
3 soundness theorems
  - constructors, forgetful boundaries
apples-to-apples performance
  - go way out, to X-max
  - jpeg different
  - 2 baselines
"perp" programs
N LD equal for base types
LD E un-equal for base types (LD is a little more than eager dynamic typing)
unequal for error messages
equal for no boundaries

#### less important, but still points

migratory vs. gradual
tag vs. constructor
implementation,
 flat-named-contract <=/c vs. lambda <=
 list? vs pair?
 arity vs procedure? 
"transient" sub-optimal name because combining three important ideas
 - only check constructor
 - forget previous type (Michael Greenberg)
 - static rewrite instead of monitors

### Future

occurrence typing ... extension of constructor-typing system
building these for typed racket, what happens when composed


### Ask for help

missing any types?
missing any expressions, in model?


