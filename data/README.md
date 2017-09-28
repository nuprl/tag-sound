data
===

Performance data for Tagged Racket

### Summary

- `laptop/` data from Ben's laptop, don't trust it too much
- 



### Notes / Conclusions

- early `zombie` performance issues due to making chaperone for `name/sc` contracts,
  this was because the names depended on a mutable table of extra defs,
  and I wasn't converting those to tags
- FSM 1000 0001 are much slower than TR, about 2x slower
  - 1000 probably because automata.rkt is typed with untyped clients
    - API contracts are tag checks (so SR has no savings on the provides)
    - dynamic-typechecks probably account for the slowdown
    - BUTTTTT I was unable to reproduce the slowdown by manually adding checks,
      see fsm-typed-1000.tar.gz
  - 0001 I guess b/c util is so slow
    - can reproduce? NO, after adding tag checks + domain checks, still ~120
    - tagged ~400
    - very distressing
