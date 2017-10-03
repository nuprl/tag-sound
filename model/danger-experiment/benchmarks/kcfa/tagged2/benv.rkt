#lang typed/racket/base

;; Binding environment,
;; helper functions

(require
  "structs-adapted.rkt"
)

(provide
  (struct-out Closure)
  (struct-out Binding)
  empty-benv
  benv-lookup
  benv-extend
  benv-extend*
)

;; =============================================================================

;; -- private

(define-type BEnv (HashTable (Option Var) (Option Addr)))
(define-type Addr Binding)
(define-type Time (Listof (Option Label)))

;; -- structs

(struct Closure
 ([lam : (Option Lam)]
  [benv : (Option BEnv)]))

(struct Binding
 ([var : (Option Var)]
  [time : (Option Time)]))

;; -- public

(: empty-benv BEnv)
(define empty-benv (make-immutable-hasheq '()))

(: benv-lookup (-> (Option BEnv) (Option Var) Addr))
(define (benv-lookup b v)
  (assert (hash-ref (assert b hash?) v) Binding?))

(: benv-extend (-> (Option BEnv) (Option Var) (Option Addr) BEnv))
(define (benv-extend b v a)
  (hash-set (assert b hash?) v a))

(: benv-extend* (-> (Option BEnv) (Option (Listof (Option Var))) (Option (Listof (Option Addr))) BEnv))
(define (benv-extend* benv vars addrs)
  (for/fold ([benv (assert benv hash?)])
    ([v (in-list (assert vars list?))]
     [a (in-list (assert addrs list?))])
    (benv-extend benv v a)))

