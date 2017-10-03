#lang typed/racket/base

(require
  "structs-adapted.rkt"
  "benv-adapted.rkt"
)

;; ---

(provide
  time-zero
  k
  tick
  alloc
)

;; =============================================================================

;; ---
(define-type Value Closure)

(: take* (All (A) (-> (Option (Listof A)) (Option Natural) (Listof A))))
(define (take* l n)
  (for/list ([e (in-list (assert l list?))]
             [i (in-range (assert n exact-nonnegative-integer?))])
    e))

;; ---

(: time-zero Time)
(define time-zero '())

(: k (Parameterof (Option Natural)))
(define k (make-parameter 1))

(: tick (-> (Option Stx) (Option Time) Time))
(define (tick call time)
  (define label (Stx-label (assert call Stx?)))
  (take* (cons label (assert time list?)) (assert (k) exact-nonnegative-integer?)))

(: alloc (-> (Option Time) (-> (Option Var) Addr)))
(define ((alloc time) var)
  (Binding var time))

