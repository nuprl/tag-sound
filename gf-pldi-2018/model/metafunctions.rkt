#lang mf-apply racket/base

(provide
  set-union*
  env-add
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
  env-add : any any -> any
  [(env-add any_env any_val)
   ,(cons (term any_val) (term any_env))])

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
  program-env-ref : P-ENV x -> MODULE-BINDING
  [(program-env-ref P-ENV x)
   #{env-ref P-ENV x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'program-env-ref "unbound identifier" "id" x "env" (term P-ENV))))])

(define-metafunction μTR
  runtime-env-ref : ρ x -> any
  [(runtime-env-ref ρ x)
   #{env-ref ρ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'runtime-env-ref "unbound identifier" "id" x "env" (term ρ))))])

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

  (test-case "env-add"
    (check-mf-apply*
     [(env-add () 3)
      (3)]
     [(env-add (2 3) 1)
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

)
