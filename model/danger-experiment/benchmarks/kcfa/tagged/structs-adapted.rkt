#lang typed/racket/base

(require
  "structs.rkt"
)

(provide
  (struct-out Stx)
  (struct-out exp)
  (struct-out Ref)
  (struct-out Lam)
  (struct-out Call)
  Exp
  Label
  Var
)

;; =============================================================================

(define-type Exp (U exp Ref Lam Call))
(define-type Label Symbol)
(define-type Var Symbol)

