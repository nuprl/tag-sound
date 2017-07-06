#lang mf-apply racket/base

;; Simple model of Typed Racket.

;; Soundness (from SNAPL 2017):
;;   If `⊢ e : τ` then either
;;   - `e` reduces to `v` and `⊢ v : τ`
;;   - `e` diverges
;;   - `e` raises a runtime error (bad value given to partial primitive)
;;   - `e` raises a boundary error `b` that points to a _specific location_
;;     where an untyped value entered typed code.

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; -----------------------------------------------------------------------------

