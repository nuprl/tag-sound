#lang typed/racket/base

(provide
  (struct-out Stx)
  (struct-out exp)
  (struct-out Ref)
  (struct-out Lam)
  (struct-out Call)
)

;; =============================================================================

(struct Stx
 ([label : (Option Symbol)]))

(struct exp Stx ())

(struct Ref exp
 ([var : (Option Symbol)]))

(struct Lam exp
 ([formals : (Option (Listof (Option Symbol)))]
  [call : (Option (U exp Ref Lam Call))]))

(struct Call Stx
 ([fun : (Option (U exp Ref Lam Call))]
  [args : (Option (Listof (Option (U exp Ref Lam Call))))]))

