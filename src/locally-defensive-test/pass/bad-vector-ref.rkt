#lang racket/base

;; Test applications of `vector-ref` that should fail due to mis-matched
;;  values and type constructors

(module t typed/racket #:locally-defensive
  (: f (-> (Vectorof Natural) Natural))
  (define (f x)
    (+ (vector-ref x 0)
       (vector-ref x 1)))
  (: g (-> (Vectorof (Vectorof Natural)) Natural))
  (define (g x)
    (define v (vector-ref x 0))
    (+ (vector-ref (vector-ref x 0) 0) (vector-ref v 1)))
  (: h (-> (Vector Natural Symbol) Natural))
  (define (h x)
    (vector-ref x 0))

  (provide f g h))

(require 't racket/contract rackunit)

(check-exn #rx"dynamic-typecheck"
  (λ () (f (vector 4 'A 4 4))))

(check-exn #rx"dynamic-typecheck"
  (λ () (g (vector 3))))

(check-exn #rx"dynamic-typecheck"
  (λ () (h (vector 1 'two 3))))
