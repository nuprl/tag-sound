#lang typed/racket/base

(require
  require-typed-check
)

(require/typed/check "structs.rkt"
  [#:struct Stx ([label : Label])]
  [#:struct (exp Stx) ()]
  [#:struct (Ref exp) ([var : Var])]
  [#:struct (Lam exp) ([formals : (Listof Var)] [call : exp])]
  [#:struct (Call Stx) ([fun : Exp] [args : (Listof Exp)])]
)

(provide
  (struct-out Stx)
  (struct-out exp)
  (struct-out Ref)
  Lam Lam? Lam-formals (rename-out (-Lam-call Lam-call))
  (struct-out Call)
  Exp
  Label
  Var
)

;; =============================================================================

(define-type Exp (U exp Ref Lam Call))
(define-type Label Symbol)
(define-type Var Symbol)

(: -Lam-call (-> Lam Exp))
(define (-Lam-call l)
  (cast (Lam-call l) Exp))
