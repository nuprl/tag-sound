#lang racket/base

;; Test providing value to untyped

(module a typed/racket/base #:locally-defensive
        (provide f)
        (define (f (x : (Boxof Integer)))
          (unbox x)))

(require 'a rackunit)
(check-exn #rx"dynamic-typecheck"
  (lambda () (f 0)))
