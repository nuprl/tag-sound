#lang typed/racket/base

(require
  require-typed-check
  "structs-adapted.rkt"
  "benv-adapted.rkt"
  "time-adapted.rkt"
  "denotable.rkt"
)

;; ---

(provide
  Denotable
  Store
  (struct-out State)
  d-bot
  d-join
  empty-store
  store-lookup
  store-update
  store-update*
  store-join
)

;; =============================================================================

(define-type Denotable (Setof Value))
(define-type Store (HashTable Addr Denotable))

