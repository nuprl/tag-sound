#lang racket/base

;; Test providing a value to an untyped context

(module a typed/racket/base
        (provide f)
        (define (f (x : (Boxof (Boxof Integer))))
          (unbox (unbox x))))

(module b racket/base
        (provide bbx)
        (define bbx (box 0)))

(module c typed/racket/base #:locally-defensive
        (require (submod ".." a))
        (require/typed (submod ".." b) (bbx (Boxof (Boxof Integer))))
        (f bbx))

(require 'a)
(f 0)
(require 'c)
