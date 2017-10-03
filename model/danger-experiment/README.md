danger-experiment
===

Q. what is the annotation overhead of making all exported functions use
   "danger types"?

   If we make the user discharge the type checks, how much work will they have to do?

Matthias says this might be like Henglein.
But remember it might not always work!!!

- - -


### Method

- For all non-OO benchmarks
- Take fully typed version
- Change all domain types to (Option T), add asserts
  - Free to change other types, to have more "Option"s
- Does it type-check?
- Compare lines of code
- Compare performance

### Interesting Things

from fsm
```
 (: match-up* (-> (Option DangerPopulation) (Option Natural) DangerPopulation))
 (: death-birth (-> (Option DangerPopulation) (Option Natural) [#:random (Option (U False Real))] DangerPopulation))
```

from tetris
```
;; Determine if the block is in the set of blocks.
(: blocks-contains? (-> (Option DangerBSet) (Option Block) Boolean))
(define (blocks-contains? bs b)
  (ormap (λ: ([c : (Option Block)]) (block=? b c)) (assert bs list?)))

;; is every element in bs1 also in bs2?
(: blocks-subset? (-> (Option DangerBSet) (Option DangerBSet) Boolean))
(define (blocks-subset? bs1 bs2)
  (andmap (λ: ([b : (Option Block)]) (blocks-contains? bs2 b)) (assert bs1 list?)))

;; Determine if given sets of blocks are equal.
(: blocks=? (-> (Option DangerBSet) (Option DangerBSet) Boolean))
(define (blocks=? bs1 bs2)
  (and (blocks-subset? bs1 bs2)
       (blocks-subset? bs2 bs1)))
```


Before / After table

| benchmark | # exports | success? | perf % increase | bytes % increase |
|-----------+---
| fsm       |           | yes | 
| suffixtree |   | yes | 128622 tagged, 4150 typed, 4635 danger
| sieve | | yes | 9589 danger, 9888 pre-danger, 9585 typed
| morsecode | | yes | 484 danger, 410 typed
| zombie    |           | no - world | 
| snake | | yes | danger2 831, typed 669, tagged\list 788 835 |
| synth | | yes | danger2 (288 268 271 277 279), typed (242 285 280 272 262)
