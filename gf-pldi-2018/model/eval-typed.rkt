#lang mf-apply racket/base

(provide
  eval-program
)

(require
  "lang.rkt"
  "grammar.rkt"
  "metafunctions.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

;; Fold over the modules in a program,
;;  accumulate a program environment.
(define-metafunction μTR
  eval-program : PROGRAM -> [σ P-ENV]
  [(eval-program PROGRAM)
   #{eval-program/env () () PROGRAM}])

(define-metafunction μTR
  eval-program/env : σ P-ENV PROGRAM -> [σ P-ENV]
  [(eval-program/env σ P-ENV ())
   [σ P-ENV]]
  [(eval-program/env σ P-ENV (MODULE_0 MODULE_1 ...))
   #{eval-program/env σ_+ P-ENV_+ (MODULE_1 ...)}
   (where [σ_+ P-ENV_+] (eval-module σ P-ENV MODULE_0))])

;; -----------------------------------------------------------------------------

;; To evaluate a module:
;; - use the requires and program environment to build a local context
;; - evaluate the definitions, extend the context
;; - use the provides to filter the context
(define-metafunction μTR
  eval-module : σ P-ENV MODULE -> [σ P-ENV]
  [(eval-module σ P-ENV MODULE_λ)
   [σ_body P-ENV_final]
   (where (module-λ x_modname REQUIRE-λ ... DEFINE-λ ... PROVIDE) MODULE_λ)
   (where ρλ_init #{eval-untyped-require* P-ENV (REQUIRE-λ ...)})
   (where [σ_body ρλ_body] #{eval-untyped-define* x_modname σ ρλ_init (DEFINE-λ ...)})
   (where ρλ_public #{eval-untyped-provide ρλ_body PROVIDE})
   (where P-ENV_final #{env-set P-ENV (x_modname ρλ_public)})]
   ;; TODO env-set
  [(eval-module σ P-ENV MODULE_τ)
   [σ_body P-ENV_final]
   (where (module-τ x_modname REQUIRE-τ ... DEFINE-τ ... PROVIDE) MODULE_τ)
   (where ρτ_init #{eval-typed-require* P-ENV (REQUIRE-τ ...)})
   (where [σ_body ρτ_body] #{eval-typed-define* x_modname σ ρτ_init (DEFINE-τ ...)})
   (where ρτ_public #{eval-typed-provide ρτ_body PROVIDE})
   (where P-ENV_final #{env-set P-ENV (x_modname ρτ_public)})])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-untyped-require* : P-ENV (REQUIRE-λ ...) -> ρλ
  [(eval-untyped-require* P-ENV ())
   ()]
  [(eval-untyped-require* P-ENV (REQUIRE-λ_first REQUIRE-λ_rest ...))
   #{env-set* ρλ_rest ρλ_first}
   (where ρλ_first #{eval-untyped-require P-ENV REQUIRE-λ_first})
   (where ρλ_rest #{eval-untyped-require* P-ENV (REQUIRE-λ_rest ...)})])

(define-metafunction μTR
  eval-typed-require* : P-ENV (REQUIRE-τ ...) -> ρτ
  [(eval-typed-require* P-ENV ())
   ()]
  [(eval-typed-require* P-ENV (REQUIRE-τ_first REQUIRE-τ_rest ...))
   #{env-set* ρτ_rest ρτ_first}
   (where ρτ_first #{eval-typed-require P-ENV REQUIRE-τ_first})
   (where ρτ_rest #{eval-typed-require* P-ENV (REQUIRE-τ_rest ...)})])

(define-metafunction μTR
  eval-untyped-require : P-ENV REQUIRE-λ -> ρλ
  [(eval-untyped-require P-ENV REQUIRE-λ)
   ρλ
   (where (require x_mod x_require ...) REQUIRE-λ)
   (where (x_mod ρ_mod) (program-env-ref P-ENV x_mod))
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'eval-untyped-require
                        "required identifier not provided by module"
                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
   (where ρ_mixed (#{runtime-env-ref ρ_mod x_require any_fail} ...))
   (where ρλ #{runtime-env->untyped-runtime-env x_mod ρ_mixed})]
  [(eval-untyped-require P-ENV REQUIRE-λ)
   ,(raise-arguments-error 'eval-untyped-require
      "required module does not exist"
      "module" (term x) "env" (term P-ENV))
   (where (require x_mod _ ...) REQUIRE-λ)])

(define-metafunction μTR
  eval-typed-require : P-ENV REQUIRE-τ -> ρτ
  [(eval-typed-require P-ENV REQUIRE-τ)
   ρτ
   (where (require x_mod [x_require τ_require] ...) REQUIRE-τ)
   (where (x_mod ρ_mod) (program-env-ref P-ENV x_mod))
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'eval-typed-require
                        "required identifier not provided by module"
                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
   (where ρ_mixed (#{runtime-env-ref ρ_mod x_require any_fail} ...))
   (where ρτ #{runtime-env->typed-runtime-env x_mod ρ_mixed (τ_require ...)})]
  [(eval-typed-require P-ENV REQUIRE-τ)
   ,(raise-arguments-error 'eval-typed-require
      "required module does not exist"
      "module" (term x) "env" (term P-ENV))
   (where (require x_mod _ ...) REQUIRE-τ)])

(define-metafunction μTR
  runtime-env->untyped-runtime-env : x ρ -> ρλ
  [(runtime-env->untyped-runtime-env x_mod ρλ)
   ρλ]
  [(runtime-env->untyped-runtime-env x_mod ρτ)
   ρλ
   (where ((x v τ) ...) ρτ)
   (where ρλ ((x #{apply-monitor# x_mod v τ}) ...))])

(define-metafunction μTR
  runtime-env->typed-runtime-env : x ρ τ* -> ρτ
  [(runtime-env->typed-runtime-env x_mod ρτ τ*)
   ρτ_sub
   (where ((x v τ_actual) ...) ρτ)
   (where (τ_expected ...) τ*)
   (where ρτ_sub ((x v #{assert-below τ_expected τ_actual}) ...))]
  [(runtime-env->typed-runtime-env x_mod ρλ τ*)
   ρτ
   (where ((x v) ...) ρλ)
   (where (τ ...) τ*)
   (where ρτ ((x #{apply-monitor# x_mod v τ} τ) ...))])

(define-judgment-form μTR
  #:mode (apply-monitor I I I O)
  #:contract (apply-monitor x v τ v)
  [
   (flat-value v)
   (where κ #{type->tag τ})
   (well-tagged-value v κ)
   ---
   (apply-monitor x_mod v τ v)]
  [
   (apply-monitor x_mod v_0 τ v_0+)
   (apply-monitor x_mod v_1 (Listof τ) v_1+)
   (where v_mon (cons v_0+ v_1+))
   ---
   (apply-monitor x_mod (cons v_0 v_1) (Listof τ) v_mon)]
  [
   (fun-value v)
   (well-tagged-value v #{type->tag τ})
   (where v_mon (mon-fun x_mod τ v))
   ---
   (apply-monitor x_mod v τ v_mon)]
  [
   (vector-value v)
   (where v_mon (mon-vector x_mod τ v))
   ---
   (apply-monitor x_mod v τ v_mon)])

(define-metafunction μTR
  apply-monitor# : x v τ -> any
  [(apply-monitor# x v τ)
   v_mon
   (judgment-holds (apply-monitor x v τ v_mon))]
  [(apply-monitor# x v τ)
   ,(raise-arguments-error 'apply-monitor "ill-typed value" "value" (term v) "type" (term τ) "value from" (term x))])

(define-metafunction μTR
  assert-below : τ τ -> τ
  [(assert-below τ_0 τ_1)
   τ_0
   (judgment-holds (<: τ_0 τ_1))]
  [(assert-below τ_0 τ_1)
   ,(raise-arguments-error 'assert-below (format "supertype of ~a" (term τ_0))
      "given" (term τ_1))])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-untyped-define* : x σ ρλ (DEFINE-λ ...) -> [σ ρλ]
  [(eval-untyped-define* x_modname σ ρλ ())
   [σ ρλ]]
  [(eval-untyped-define* x_modname σ ρλ (DEFINE-λ_first DEFINE-λ_rest ...))
   #{eval-untyped-define* x_modname σ_+ ρλ_+ (DEFINE-λ_rest ...)}
   (where (define x e) DEFINE-λ_first)
   (where [σ_+ v] #{eval-value x_modname σ ρλ e})
   (where ρλ_+ #{env-set ρλ (x v)})])

(define-metafunction μTR
  eval-typed-define* : x σ ρτ (DEFINE-τ ...) -> [σ ρτ]
  [(eval-typed-define* x_modname σ ρτ ())
   [σ ρτ]]
  [(eval-typed-define* x σ ρτ (DEFINE-τ_first DEFINE-τ_rest ...))
   #{eval-typed-define* x_modname σ_+ ρτ_+ (DEFINE-τ_rest ...)}
   (where (define x τ e) DEFINE-τ_first)
   (where [σ_+ v] #{eval-value x_modname σ ρτ e})
   (where ρτ_+ #{env-set ρτ (x v τ)})])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-untyped-provide : ρλ PROVIDE -> ρλ
  [(eval-untyped-provide ρλ PROVIDE)
   #{eval-provide ρλ PROVIDE}])

(define-metafunction μTR
  eval-typed-provide : ρτ PROVIDE -> ρτ
  [(eval-typed-provide ρτ PROVIDE)
   #{eval-provide ρτ PROVIDE}])

;; eval-provide
;; Filter a runtime environment, remove all identifiers that are not in the
;;  given list of provides.
;; Error if an identifier is provided, but not defined in the runtime environment
(define-metafunction μTR
  eval-provide : ρ PROVIDE -> ρ
  [(eval-provide ρ (provide x_provide ...))
   (#{runtime-env-ref ρ x_provide any_fail} ...)
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'provide "provided identifier not defined in module"
                       "id" x)))])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-value : x σ ρ e -> [σ v]
  [(eval-value x_modname σ ρ e)
   [σ_final v_final]
   (where Σ_0 #{load-expression x_modname σ ρ e})
   (where A ,(step-expression* (term Σ_0)))
   (where (v_final σ_final x_modname) #{unload-answer A})])

;; NOTE ignores types in ρ
;;  maybe want to use the annotations to make better monitors?
(define-metafunction μTR
  load-expression : x σ ρ e -> Σ
  [(load-expression x_modname σ ρ e)
   (e_ρ σ x_modname)
   (where e_ρ (substitute* e ρ))])

(define-metafunction μTR
  unload-answer : A -> [v σ x]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   (v σ x)
   (where (v σ x) Σ)]
  [(unload-answer Σ)
   ,(raise-arguments-error 'unload-answer
      "evaluation finished with non-empty stack"
      "stack" (term S)
      "value" (term v)
      "store" (term σ))
   (where (v σ S) Σ)])

(define step-expression
  (reduction-relation μTR
   #:domain A
   [-->
     Σ
     BadIndex]
  ))

(define step-expression*
  (make--->* step-expression))

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "apply-monitor"
    (check-mf-apply*
     [(apply-monitor# m 4 Int)
      4]
     [(apply-monitor# m nil (Listof (Vectorof Int)))
      nil]
     [(apply-monitor# m (cons 1 (cons 2 (cons 3 nil))) (Listof Int))
      (cons 1 (cons 2 (cons 3 nil)))]
     [(apply-monitor# m (vector 1) (Vectorof Nat))
      (mon-vector m (Vectorof Nat) (vector 1))]
     [(apply-monitor# m (cons (vector 1) (cons (vector 2) nil)) (Listof (Vectorof Int)))
      (cons (mon-vector m (Vectorof Int) (vector 1)) (cons (mon-vector m (Vectorof Int) (vector 2)) nil))]
     [(apply-monitor# m (fun f (x) (+ x x)) (→ Int Int))
      (mon-fun m (→ Int Int) (fun f (x) (+ x x)))]
    )

   (check-exn exn:fail:contract?
     (λ () (term (apply-monitor# m 4 (Listof Int)))))
  )

  (test-case "runtime-env->untyped-runtime-env"
    (check-mf-apply*
     ((runtime-env->untyped-runtime-env m0 ())
      ())
     ((runtime-env->untyped-runtime-env m0 ((x 0) (y 1) (z (vector 2))))
      ((x 0) (y 1) (z (vector 2))))
     ((runtime-env->untyped-runtime-env m0 ((x 0 Nat) (z (vector 2) (Vectorof Int))))
      ((x 0) (z (mon-vector m0 (Vectorof Int) (vector 2)))))
    )
  )

  (test-case "runtime-env->typed-runtime-env"
    (check-mf-apply*
     ((runtime-env->typed-runtime-env m0 ((x 4) (y 1) (z (vector 2))) (Nat Int (Vectorof Int)))
      ((x 4 Nat) (y 1 Int) (z (mon-vector m0 (Vectorof Int) (vector 2)) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4) (z (vector nil))) (Nat (Vectorof Int)))
      ((x 4 Nat) (z (mon-vector m0 (Vectorof Int) (vector nil)) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4 Int) (z (vector 2) (Vectorof Int))) (Int (Vectorof Int)))
      ((x 4 Int) (z (vector 2) (Vectorof Int))))
    )
  )

  (test-case "eval-untyped-require*"
    (check-true (redex-match? μTR P-ENV (term ((m0 ((n 4)))))))
    (check-true (redex-match? μTR REQUIRE-λ (term (require m0 n))))

    (check-mf-apply*
     ((eval-untyped-require* () ())
      ())
     ((eval-untyped-require* ((m0 ((n 4)))) ((require m0 n)))
      ((n 4)))
     ((eval-untyped-require* ((m0 ((num 4) (y 5)))) ((require m0 num)))
      ((num 4)))
     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 num)))
      ((num 4)))
     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 num) (require m1 f)))
      ((num 4) (f (fun g (x) x))))
     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 num) (require m1 f)))
      ((num 4) (f (mon-fun m1 (→ Int Int) (fun g (x) x)))))
    )

    (check-exn exn:fail:contract?
      (λ () (term (eval-untyped-require* () ((require m x))))))
  )

  (test-case "eval-typed-require*"
    (check-mf-apply*
     ((eval-typed-require* () ())
      ())
     ((eval-typed-require* ((m0 ((num 4 Nat)))) ((require m0 [num Nat])))
      ((num 4 Nat)))
     ((eval-typed-require* ((m0 ((num 4) (y 5)))) ((require m0 [num Nat])))
      ((num 4 Nat)))
     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 [num Nat])))
      ((num 4 Nat)))
     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                           ((require m0 (num Int)) (require m1 (f (→ (Vectorof Int) (Vectorof Int))))))
      ((num 4 Int) (f (mon-fun m1 (→ (Vectorof Int) (Vectorof Int)) (fun g (x) x)) (→ (Vectorof Int) (Vectorof Int)))))
     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 (num Int)) (require m1 (f (→ Int Int)))))
      ((num 4 Int) (f (fun g (x) x) (→ Int Int))))
    )

    (check-exn exn:fail:contract?
      (λ () (term (eval-typed-require* ((m0 ((num 4)))) ((require m0 (num (Vectorof Int))))))))
  )

  (test-case "assert-below"
    (check-mf-apply*
     [(assert-below Int Int)
      Int]
     [(assert-below Nat Int)
      Nat])

    (check-exn exn:fail:contract?
      (λ () (term (assert-below Int Nat))))
  )

  (test-case "eval-untyped-define*"
  )

  (test-case "eval-typed-define*"
  )

  (test-case "eval-untyped-provide"
    (check-mf-apply*
     ((eval-untyped-provide ((x 4) (y (vector 1))) (provide x y))
      ((x 4) (y (vector 1))))
     ((eval-untyped-provide ((x 4) (y (cons 1 nil))) (provide x))
      ((x 4))))
  )

  (test-case "eval-typed-provide"
    (check-mf-apply*
     ((eval-typed-provide ((x 4 Nat) (y (vector 1) (Vectorof Nat))) (provide x y))
      ((x 4 Nat) (y (vector 1) (Vectorof Nat))))
     ((eval-typed-provide ((x 4 Nat) (y (cons 1 nil) (Listof Int))) (provide x))
      ((x 4 Nat))))
  )

  (test-case "eval-provide"
    (check-mf-apply*
      ((eval-provide () (provide))
       ())
      ((eval-provide ((x 4) (y 5)) (provide x y))
        ((x 4) (y 5)))
      ((eval-provide ((x 4) (y 5)) (provide y x))
       ((y 5) (x 4)))
      ((eval-provide ((x 4) (y 5)) (provide y))
       ((y 5)))
      ((eval-provide ((x 4 Nat) (y 5 Int)) (provide x y))
       ((x 4 Nat) (y 5 Int))))

    (check-exn exn:fail:contract?
      (λ () (term (eval-provide ((x 4)) (provide y))))))

  (test-case "eval-value"
  )

  (test-case "load-expression"
  )

  (test-case "unload-answer"
  )

  (test-case "step-expression"
  )

)

