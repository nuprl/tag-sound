#lang typed/racket/base #:locally-defensive

(module u racket/base
  (define x* (list "OOPS"))
  (provide x*))

(require/typed 'u
  (x* (Listof Integer)))

(+ (car x*) 1)
