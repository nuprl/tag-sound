#lang mf-apply racket/base

(provide
  set-union*
  env-set
  env-set*
  program-env-ref
  runtime-env-ref
  loc-env-ref
  loc-env-set
  loc-env-update
  substitute*

  current-modname

  stack-push
)

(require
  "lang.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define (set-union* x**)
  (for/fold ([acc '()])
            ([x* (in-list x**)])
    (set-union acc x*)))

(define-metafunction μTR
  env-set : any any -> any
  [(env-set any_env any_val)
   ,(cons (term any_val) (term any_env))])

(define-metafunction μTR
  env-set* : any (any ...) -> any
  [(env-set* any ())
   any]
  [(env-set* any (any_first any_rest ...))
   #{env-set* #{env-set any any_first} (any_rest ...)}])

(define-metafunction μTR
  env-ref : any x any -> any
  [(env-ref any_env x any_fail)
   ,(let loop ([env (term any_env)])
      (cond
       [(null? env)
        (let ((k (term any_fail)))
          (if (procedure? k) (k (term x)) k))]
       [(equal? (car (car env)) (term x))
        (car env)]
       [else
        (loop (cdr env))]))])

(define-metafunction μTR
  env-update : any any any -> any
  [(env-update any_env any_binding any_fail)
   ,(let loop ([env (term any_env)] [acc '()])
      (cond
       [(null? env)
        (let ((k (term any_fail)))
          (if (procedure? k) (k (car (term any_binding))) k))]
       [(equal? (caar env) (car (term any_binding)))
        (term #{env-set* #{env-set ,(cdr env) any_binding} ,acc})]
       [else
        (loop (cdr env) (term #{env-set ,acc ,(car env)}))]))])

(define-metafunction μTR
  program-env-ref : P-ENV x -> MODULE-BINDING
  [(program-env-ref P-ENV x)
   #{env-ref P-ENV x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'program-env-ref "unbound identifier" "id" x "env" (term P-ENV))))])

(define-metafunction μTR
  runtime-env-ref : ρ x any ... -> any
  [(runtime-env-ref ρ x any_fail)
   #{env-ref ρ x any_fail}]
  [(runtime-env-ref ρ x)
   #{env-ref ρ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'runtime-env-ref "unbound identifier" "id" x "env" (term ρ))))])

(define-metafunction μTR
  loc-env-ref : σ x -> any
  [(loc-env-ref σ x)
   #{env-ref σ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'loc-env-ref "unbound identifier" "id" x "store" (term σ))))])

(define-metafunction μTR
  loc-env-set : σ x v -> σ
  [(loc-env-set σ x v)
   #{env-set σ (x v)}
   (where #false #{env-ref σ x #false})]
  [(loc-env-set σ x v)
   ,(raise-arguments-error 'loc-env-set "identifier already bound in store"
      "id" (term x) "store" (term σ) "the value" (term v))])

(define-metafunction μTR
  loc-env-update : σ x v -> σ
  [(loc-env-update σ x v)
   #{env-update σ (x v) any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'loc-env-update "unbound identifier, cannot update" "id" x "store" (term σ))))])

(define-metafunction μTR
  substitute* : any (any ...) -> any
  [(substitute* any_thing ())
   any_thing]
  [(substitute* any_thing (any_first any_rest ...))
   (substitute* (substitute any_thing any_key any_val) (any_rest ...))
   (where (any_key any_val _ ...) any_first)]
  [(substitute* any_thing (any_bad any_rest ...))
   ,(raise-arguments-error 'substitute* "bad environment binding"
      "term" (term any_thing)
      "binding" (term any_bad)
      "other bindings" (term (any_rest ...)))])

(define-metafunction μTR
  current-modname : S -> x
  [(current-modname x_modname)
   x_modname]
  [(current-modname (x_modname _ ...))
   x_modname])

(define-metafunction μTR
  stack-push : S x τ E -> S
  [(stack-push S x τ E)
   (x τ E S)])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "set-union*"
    (check-equal?
      (set-union* '())
      '())
    (check set=?
      (set-union* '((1 2 3) (2 3 4) (3 4 5)))
      '(1 2 3 4 5)))

  (test-case "env-set"
    (check-mf-apply*
     [(env-set () 3)
      (3)]
     [(env-set (2 3) 1)
      (1 2 3)]))

  (test-case "env-ref"
    (check-mf-apply*
     [(env-ref ((a 1) (b 2) (c 3)) a #f)
      (a 1)]
     [(env-ref ((a 1) (b 2)) c #f)
      #f]
     [(env-ref ((a 1) (b 2)) c ,(λ (x) (format "not found ~a" x)))
      "not found c"])

    (check-exn exn:fail:contract?
      (λ () (term (env-ref () x ,(λ (x) (raise-arguments-error 'test "deathcase")))))))

  (test-case "env-update"
    (check-mf-apply*
     [(env-update ((x 2)) (x 3) #false)
      ((x 3))]
     [(env-update ((x 2) (y 3) (z 4)) (y 0) #false)
      ((x 2) (y 0) (z 4))]
     [(env-update ((x 2)) (y 0) #false)
      #false]
     [(env-update ((x 2)) (y 0) ,(λ (z) (format "unbound ~a" z)))
      "unbound y"]))

  (test-case "program-env-ref"
    (check-mf-apply*
     [(program-env-ref ((yo ())) yo)
      (yo ())]
     ;; TODO
  ))

  (test-case "runtime-env-ref"
    (check-mf-apply*
     [(runtime-env-ref ((x 3) (y 4)) x)
      (x 3)]
     [(runtime-env-ref ((x 3) (y 4)) y)
      (y 4)])

    (check-exn exn:fail:contract?
      (λ () (term (runtime-env-ref ((x 3)) y)))))

  (test-case "loc-env-ref"
    (check-mf-apply*
     [(loc-env-ref ((x 3)) x)
      (x 3)]
     [(loc-env-ref ((x 3) (y 4)) y)
      (y 4)])

    (check-exn exn:fail:contract?
      (λ () (term #{loc-env-ref () x}))))

  (test-case "loc-env-set"
    (check-mf-apply*
     [(loc-env-set () x 0)
      ((x 0))]
     [(loc-env-set ((x 1) (y 2)) z 3)
      ((z 3) (x 1) (y 2))])

    (check-exn exn:fail:contract?
      (λ () (term (loc-env-set ((x 0)) x 1)))))

  (test-case "loc-env-update"
    (check-mf-apply*
     [(loc-env-update ((x 0)) x 1)
      ((x 1))])

    (check-exn exn:fail:contract?
      (λ () (term (loc-env-update ((x 0)) y 1)))))

  (test-case "substitute*"
    (check-mf-apply*
     [(substitute* (+ x y) ((x 1) (y 2)))
      (+ 1 2)]
     [(substitute* (+ a a) ())
      (+ a a)]))

)
