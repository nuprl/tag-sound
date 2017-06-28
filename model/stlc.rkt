#lang mf-apply racket/base

;; Workspace for a type sound RST, based on simply-typed λ calculus

;; =============================================================================

(require
  racket/set
  redex/reduction-semantics)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse))
)

;; =============================================================================

