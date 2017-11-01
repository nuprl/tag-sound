#lang mf-apply racket/base

;; TODO maybe want this broken across files, or submodules

;; Little model of N embeddings:
;; - identity
;; - natural
;; - lazy natural
;; - lazy forgetful natural
;; - type-tag

(require
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================
