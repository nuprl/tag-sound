#lang typed/racket/base

;; User Interface to `ai.rkt`

(require
  racket/set
  "structs-adapted.rkt"
  "benv-adapted.rkt"
  "denotable-adapted.rkt"
  "time-adapted.rkt"
  (only-in racket/string string-join)
  "ai.rkt"
)
;; ---

(provide
  summarize
  empty-mono-store
  monovariant-value
  monovariant-store
  analyze
  format-mono-store
)

;; =============================================================================

;; -- ui.rkt
(define-type MonoStore (HashTable Var (Setof Exp)))

(: summarize (-> (Option (Setof (Option State))) Store))
(define (summarize states)
  (for/fold ([store empty-store])
    ([state (in-set (assert states set?))])
    (store-join (State-store (assert state State?)) store)))

(: empty-mono-store MonoStore)
(define empty-mono-store (make-immutable-hasheq '()))

(: monovariant-value (-> (Option Value) Lam))
(define (monovariant-value v)
  (assert (Closure-lam (assert v Closure?)) Lam?))

(: monovariant-store (-> (Option Store) MonoStore))
(define (monovariant-store store)
  (: update-lam (-> (Setof (Option Value)) (-> (Option (Setof Exp)) (Setof Exp))))
  (define ((update-lam vs) b-vs)
    (: v-vs (Setof Lam))
    (define v-vs (list->set (set-map vs monovariant-value)))
    (set-union (assert b-vs set?) v-vs))
  (: default-lam (-> (Setof Exp)))
  (define (default-lam) (set))
  (for/fold ([mono-store empty-mono-store])
    ([(b vs) (in-hash (assert store hash?))])
    (hash-update mono-store
                 (assert (Binding-var (assert b Binding?)) symbol?)
                 (update-lam (assert vs set?))
                 default-lam)))

(: analyze (-> (Option Exp) MonoStore))
(define (analyze exp)
  (define init-state (State exp empty-benv empty-store time-zero))
  (define states (explore (set) (list init-state)))
  (define summary (summarize states))
  (define mono-store (monovariant-store summary))
  mono-store)

(: format-mono-store (-> (Option MonoStore) String))
(define (format-mono-store ms)
  (: res (Listof String))
  (define res
    (for/list ([(i vs) (in-hash (assert ms hash?))])
      (format "~a:\n~a"
              i
              (string-join
                (for/list : (Listof String) ([v (in-set vs)])
                  (format "\t~S" v))
                "\n"))))
  (string-join res "\n"))

