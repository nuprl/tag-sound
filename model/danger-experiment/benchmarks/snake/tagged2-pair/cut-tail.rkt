#lang typed/racket

(require "data-adaptor.rkt")
;; NeSegs is one of:
;; - (cons Posn empty)
;; - (cons Posn NeSegs)

;; cut-tail : NeSegs -> Segs
;; Cut off the tail.
(: cut-tail : (-> (Option (NEListof (Option Posn))) (Listof Posn)))
(define (cut-tail segs)
  (assert segs pair?)
  (let ([r (cdr segs)])
    (cond [(empty? r) empty]
          [else (cons (assert (car segs) posn?) (cut-tail r))])))

(provide
 cut-tail)
