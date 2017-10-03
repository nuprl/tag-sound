#lang typed/racket/base

;; Abstract Interpretation

(require
  "structs-adapted.rkt"
  "benv-adapted.rkt"
  "time-adapted.rkt"
  "denotable-adapted.rkt"
  racket/set
  (only-in racket/match match-define)
)

;; ---

(provide
  atom-eval
  next
  explore
)

;; =============================================================================

(: atom-eval (-> (Option BEnv) (Option Store) (-> (Option Exp) Denotable)))
(define ((atom-eval benv store) id)
  (cond
    [(Ref? id)
     (store-lookup store (benv-lookup benv (Ref-var id)))]
    [(Lam? id)
     (set (Closure id benv))]
    [else
     (error "atom-eval got a plain Exp")]))

(: next (-> (Option State) (Setof (Option State))))
(define (next st)
  (match-define (State c benv store time) (assert st State?))
  (cond
    [(Call? c)
     (define time* (tick c time))
     (match-define (Call _ f args) c)
     (: procs Denotable)
     (define procs ((atom-eval benv store) f))
     (: params (Listof Denotable))
     (define params (map (atom-eval benv store) (assert args list?)))
     (: new-states (Listof State))
     (define new-states
       (for/list ([proc : (Option Value) (in-set procs)])
         (match-define (Closure lam benv*) (assert proc Closure?))
         (match-define (Lam _ formals call*) lam)
         (define bindings (map (alloc time*) (assert formals list?)))
         (define benv** (benv-extend* benv* (assert formals list?) bindings))
         (define store* (store-update* store bindings params))
         (State call* benv** store* time*)))
     (list->set new-states)]
    [else (set)]))

;; -- state space exploration

(: explore (-> (Option (Setof (Option State))) (Option (Listof (Option State))) (Setof (Option State))))
(define (explore seen todo)
  (if (and (list? todo) (set? seen)) (let ()
      (cond
        [(eq? '() todo)
         ;; Nothing left to do
         seen]
        [(set-member? seen (car todo))
         ;; Already seen current todo, move along
         (explore seen (cdr todo))]
        [else
          (define st0 (car todo))
          (: succs (Setof (Option State)))
          (define succs (next st0))
          (explore (set-add seen st0)
                   (append (set->list succs) (cdr todo)))]))
    (error 'dynamic-typecheck)))

