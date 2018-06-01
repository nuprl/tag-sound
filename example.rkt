#lang racket/base

;; Quick test for TR_N and TR_LD, run with:
;; 
;;  ./raco test example.rkt
;;
;; Should print "2 tests passed"

;; Racket module, provides a function that returns a pair of integers
(module untyped racket/base
  (provide make-integers)
  (define (make-integers)
    (cons -2 -2)))

;; TR_N (Typed Racket, natural embedding) module, expects a pair of _natural_ numbers.
;; Raises an exception when the pair reaches the context.
(module TR_N typed/racket
  (require/typed (submod ".." untyped)
    (make-integers (-> (Pairof Natural Natural))))
  (require typed/rackunit)
  (check-exn exn:fail:contract?
    (lambda () (make-integers))))

;; TR_LD (Typed Racket, locally-defensive embedding) module, also expects a
;;  pair of natural numbers.
;; Does not raise an exception until the pair is accessed.
(module TR_LD typed/racket #:locally-defensive
  (require/typed (submod ".." untyped)
    (make-integers (-> (Pairof Natural Natural))))
  (require typed/rackunit)
  (define nats (make-integers))
  (check-exn #rx"dynamic-typecheck"
    (lambda () (car nats))))

(require 'TR_N 'TR_LD)
