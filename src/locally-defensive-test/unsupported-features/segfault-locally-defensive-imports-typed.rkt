#lang racket/base

;; Unsupported: exporting a value from Typed Racket to Locally-Defensive Racket
;;  the TR export is not protected and can be lead to a segmentation fault, see:

(module a typed/racket
        (provide f)
        (define (f (xs : (Listof (Boxof Integer)))) (unbox (car xs))))

(module c racket/base
        (provide xs)
        (define xs '(null)))

(module b typed/racket #:locally-defensive
        (require (submod ".." a))
        (require/typed (submod ".." c) (xs (Listof (Boxof Integer))))
        (f xs))

(require 'b)
