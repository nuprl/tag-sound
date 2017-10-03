#lang typed/racket/base

;; Denotable values and stores to hold them.
;; A denotable is a set of values
;; (A value is a closure)

(require
  racket/set
  "structs-adapted.rkt"
  "benv-adapted.rkt"
  "time-adapted.rkt"
)

;; -----------------------------------------------------------------------------

(provide
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

;; -- private
(define-type Denotable (Setof (Option Value)))
(define-type Store (HashTable (Option Addr) (Option Denotable)))

;; -- structs

(struct State
 ([call : (Option Exp)]
  [benv : (Option BEnv)]
  [store : (Option Store)]
  [time : (Option Time)]))

;; -- public

(: d-bot Denotable)
(define d-bot (set))

(: d-join (-> (Option Denotable) (Option Denotable) Denotable))
(define (d-join d0 d1)
  (set-union (assert d0 set?) (assert d1 set?)))

(: empty-store Store)
(define empty-store (make-immutable-hasheq '()))

(: store-lookup (-> (Option Store) (Option Addr) Denotable))
(define (store-lookup s a)
  (assert (hash-ref (assert s hash?) (assert a Binding?) (lambda () d-bot)) set?))

(: store-update (-> (Option Store) (Option Addr) (Option Denotable) Store))
(define (store-update store addr value)
  (: update-lam (-> (Option Denotable) Denotable))
  (define (update-lam d) (d-join d value))
  (hash-update (assert store hash?) (assert addr Binding?) update-lam (lambda () d-bot)))

(: store-update* (-> (Option Store) (Option (Listof (Option Addr))) (Option (Listof (Option Denotable))) Store))
(define (store-update* s as vs)
  (for/fold ([store (assert s hash?)])
    ([a (in-list (assert as list?))]
     [v (in-list (assert vs list?))])
    (store-update store a v)))

(: store-join (-> (Option Store) (Option Store) Store))
(define (store-join s1 s2)
  (for/fold ([new-store (assert s1 hash?)])
    ([(k v) (in-hash (assert s2 hash?))])
    (store-update new-store k v)))

