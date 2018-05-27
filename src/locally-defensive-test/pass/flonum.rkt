#lang typed/racket/base #:locally-defensive

;; Test case-> type

(require racket/flonum)

(: flprobability? (case-> (Flonum -> Boolean) (Flonum Any -> Boolean)))
(define (flprobability? p [log? #f])
  (cond [log?  (and (p . fl>= . -inf.0) (p . fl<= . 0.0))]
        [else  (and (p . fl>= . 0.0) (p . fl<= . 1.0))]))
