#lang typed/racket/base

(require
  "structs-adapted.rkt"
  "benv-adapted.rkt"
  "time.rkt"
)

;; ---

(provide
  time-zero
  k
  tick
  alloc
  Value
)

;; =============================================================================

;; -- time.rkt
(define-type Value Closure)

