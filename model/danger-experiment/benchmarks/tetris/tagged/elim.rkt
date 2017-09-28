#lang typed/racket

(require
  "base-types.rkt"
  "bset.rkt"
  "consts.rkt")

;; Eliminate all full rows and shift down appropriately.
(: eliminate-full-rows (-> (Option DangerBSet) DangerBSet))
(define (eliminate-full-rows bs)
  (elim-row bs board-height 0))

(: elim-row (-> (Option DangerBSet) (Option Integer) (Option Integer) DangerBSet))
(define (elim-row bs i offset)
  (assert i integer?)
  (cond [(< i 0) empty]
        [(full-row? bs i)   (elim-row bs (sub1 i) (add1 (assert offset integer?)))]
        [else (blocks-union (elim-row bs (sub1 i) offset)
                            (blocks-move 0 (assert offset integer?) (blocks-row
                                                   bs i)))]))
(provide
 eliminate-full-rows)
