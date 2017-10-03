#lang typed/racket/base

(require
  "structs-adapted.rkt"
  "benv.rkt"
)
(provide
  (struct-out Closure)
  (struct-out Binding)
  empty-benv
  benv-lookup
  benv-extend
  benv-extend*
  BEnv
  Addr
  Time
)

;; =============================================================================

(define-type BEnv (HashTable (Option Var) (Option Addr)))
(define-type Addr Binding)
(define-type Time (Listof (Option Label)))
