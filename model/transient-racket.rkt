#lang mf-apply racket/base

;; Simple model of Transient Racket
;; - typecheck program
;; - use types to insert runtime checks & blame collaboration
;; - no monitors

;; Soundness:
;;   If `⊢ e : τ` then `⊢ e : tag(τ)` either
;;   - `e` reduces to `v` and `⊢ v : tag(τ)`
;;   - `e` diverges
;;   - `e` raises a runtime error (bad value given to partial primitive)
;;   - `e` raises a boundary error `b*` that points to a **set** of boundaries,
;;     one of which might be the source of the error

;; MT1 is weaker, MT2 is weaker

;; (maybe can improve 'boundary error' to a sound overapprox)

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


