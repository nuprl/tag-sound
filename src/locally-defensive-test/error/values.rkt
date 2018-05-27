#lang typed/racket/base #:locally-defensive

(module u racket/base
  (provide f)
  (define (f x)
    (values x x)))

(require/typed 'u
  (f (-> Natural (Values Symbol Natural))))

(define-values [a b] (f 2))
