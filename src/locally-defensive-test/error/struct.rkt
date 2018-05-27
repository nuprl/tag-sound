#lang racket/base

(module t typed/racket #:locally-defensive
  (struct A ((x : Integer) (y : (Listof Integer)) (z : (-> Integer Integer))))
  (: f (-> (Listof A) Integer))
  (define (f x)
    (define mya (car x))
    (A-x mya))

  (provide (struct-out A) f))

(require 't)

(define a (A 'NaN '() add1))

(f (list a))
