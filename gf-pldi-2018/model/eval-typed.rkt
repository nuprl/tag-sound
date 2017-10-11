#lang mf-apply racket/base

(provide
)

(require
  "lang.rkt"
  "grammar.rkt"
  "metafunctions.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics)

;; -----------------------------------------------------------------------------
;; --- evaluation
;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-program : PROGRAM -> P-ENV
  [(eval-program PROGRAM P-ENV)
   #{eval-program/env () PROGRAM}])

(define-metafunction μTR
  eval-program/env : P-ENV PROGRAM -> P-ENV
  [(eval-program/env P-ENV ())
   P-ENV]
  [(eval-program/env P-ENV (MODULE_0 MODULE_1 ...))
   #{eval-program/env P-ENV_+ (MODULE_1 ...)}
   (where P-ENV_+ (eval-module P-ENV MODULE_0))])

(define-metafunction μTR
  eval-module : P-ENV MODULE -> P-ENV
  [(eval-module P-ENV MODULE_λ)
   P-ENV_final
   (where (module-λ x REQUIRE-λ ... DEFINE-λ ... PROVIDE) MODULE_λ)
   (where ρλ_init #{eval-untyped-require* P-ENV (REQUIRE-λ ...)})
   (where ρλ_body #{eval-untyped-define* ρλ_init (DEFINE-λ ...)})
   (where ρλ_public #{eval-untyped-provide ρλ_body PROVIDE})
   (where P-ENV_final #{env-add P-ENV (x ρλ_public)})]
  [(eval-module P-ENV MODULE_τ)
   P-ENV_final
   (where (module-τ x REQUIRE-τ ... DEFINE-τ ... PROVIDE) MODULE_τ)
   (where ρτ_init #{eval-typed-require* P-ENV (REQUIRE-τ ...)})
   (where ρτ_body #{eval-typed-define* ρτ_init (DEFINE-τ ...)})
   (where ρτ_public #{eval-typed-provide ρτ_body PROVIDE})
   (where P-ENV_final #{env-add P-ENV (x ρτ_public)})])

;; ---

(define-metafunction μTR
  eval-untyped-require* : P-ENV (REQUIRE-λ ...) -> ρλ
  [(eval-untyped-require* P-ENV ())
   ()]
  [(eval-untyped-require* P-ENV (REQUIRE-λ_first REQUIRE-λ_rest ...))
   #{env-add ρλ_rest x:v}
   (where x:v #{eval-untyped-require P-ENV REQUIRE-λ_first})
   (where ρλ_rest #{eval-untyped-require* P-ENV (REQUIRE-λ_rest ...)})])

(define-metafunction μTR
  eval-typed-require* : P-ENV (REQUIRE-τ ...) -> ρτ
  [(eval-typed-require* P-ENV ())
   ()]
  [(eval-typed-require* P-ENV (REQUIRE-τ_first REQUIRE-τ_rest ...))
   #{env-add ρτ_rest x:v:τ}
   (where x:v:τ #{eval-typed-require P-ENV REQUIRE-τ_first})
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
   (where ρ_mixed (#{env-ref ρ_mod x_require any_fail} ...))
   (where ρλ #{runtime-env->untyped-runtime-env ρ_mixed})]
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
   (where ρ_mixed (#{env-ref ρ x_require any_fail} ...))
   (where ρτ #{runtime-env->typed-runtime-env ρ_mixed (τ_require ...)})]
  [(eval-typed-require P-ENV REQUIRE-τ)
   ,(raise-arguments-error 'eval-typed-require
      "required module does not exist"
      "module" (term x) "env" (term P-ENV))
   (where (require x_mod _ ...) REQUIRE-τ)])

(define-metafunction μTR
  runtime-env->untyped-runtime-env : ρ -> ρλ
  [(runtime-env->untyped-runtime-env ρλ)
   ρλ]
  [(runtime-env->untyped-runtime-env ρτ)
   ρλ
   (where ((x v τ) ...) ρτ)
   (where ρλ ((x #{apply-monitor# v τ}) ...))])

(define-metafunction μTR
  runtime-env->typed-runtime-env : ρ τ* -> ρτ
  [(runtime-env->typed-runtime-env ρτ τ*)
   ρτ_sub
   (where ((x v τ_actual) ...) ρτ)
   (where (τ_expected ...) τ*)
   (where ρτ_sub ((x v #{assert-below τ_expected τ_actual}) ...))]
  [(runtime-env->typed-runtime-env ρλ τ*)
   ρτ
   (where ((x v) ...) ρλ)
   (where (τ ...) τ*)
   (where ρτ ((x #{apply-monitor# v τ} τ) ...))])

(define-judgment-form μTR
  #:mode (apply-monitor I I O)
  #:contract (apply-monitor v τ v)
  [
   (flat-value v)
   (where κ #{type->tag τ})
   (well-tagged-value v κ)
   ---
   (apply-monitor v τ v)]
  [
   (apply-monitor v_0 τ v_0+)
   (apply-monitor v_1 (Listof τ) v_1+)
   (where v_mon (cons v_0+ v_1+))
   ---
   (apply-monitor (cons v_0 v_1) (Listof τ) v_mon)]
  [
   (fun-value v)
   (well-tagged-value v #{type->tag τ})
   (where v_mon (mon-fun τ v))
   ---
   (apply-monitor v τ v_mon)]
  [
   (vector-value v)
   (where v_mon (mon-vector τ v))
   ---
   (apply-monitor v τ v_mon)])

(define-metafunction μTR
  apply-monitor# : v τ -> v
  [(apply-monitor# v τ)
   v_mon
   (judgment-holds (apply-monitor v τ v_mon))])

(define-metafunction μTR
  assert-below : τ τ -> τ
  [(assert-below τ_0 τ_1)
   τ_0
   (judgment-holds (<: τ_0 τ_1))]
  [(assert-below τ_0 τ_1)
   ,(raise-argument-error 'assert-below (format "supertype of ~a" (term τ_0))
      "given" (term τ_1))])

(define-metafunction μTR
  eval-untyped-define* : ρλ (DEFINE-λ ...) -> ρλ
  [(eval-untyped-define* ρλ ())
   ρλ]
  [(eval-untyped-define* ρλ (DEFINE-λ_first DEFINE-λ_rest ...))
   #{eval-untyped-define* ρλ_+ (DEFINE-λ_rest ...)}
   (where (define x e) DEFINE-λ_first)
   (where v #{eval-value ρλ e})
   (where ρλ_+ #{env-add ρλ (x v)})])

(define-metafunction μTR
  eval-typed-define* : ρτ (DEFINE-τ ...) -> ρτ
  [(eval-typed-define* ρτ ())
   ρτ]
  [(eval-typed-define* ρτ (DEFINE-τ_first DEFINE-τ_rest ...))
   #{eval-typed-define* ρτ_+ (DEFINE-τ_rest ...)}
   (where (define x τ e) DEFINE-τ_first)
   ;; TODO error, don't know how to thread "vector state" through evaluation
   (where [v ρτ_new] #{eval-value ρτ e})
   (side-condition (error 'not-implemented))
   (where ρτ_+ #{env-add ρτ (x v τ)})])

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
   (#{env-ref ρ x_provide any_fail} ...)
   (where any_fail ,(λ (x)
                      (raise-user-error 'provide "provided identifier not defined in module: ~a" x)))])

(define-metafunction μTR
  eval-value : ρ e -> [v ρ]
  [(eval-value ρ e)
   [v ρ]
   (where Σ_0 #{load-expression ρ e})
   (where A ,(step-expression* (term Σ_0)))
   (where [v ρ] #{unload-answer A})])

(define-metafunction μTR
  load-expression : ρ e -> Σ
  [(load-expression ρ e)
   (e ρ ())])

(define-metafunction μTR
  unload-answer : A -> [v ρ]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   [v ρ]
   (where (v ρ ()) Σ)]
  [(unload-answer Σ)
   ,(raise-arguments-error 'unload-answer "evaluation ended with non-empty continuation" "state" (term Σ))])

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
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

(module+ test
  (test-case "eval-provide"
    (check-mf-apply*
      ((eval-provide () (provide))
       ())
      ((eval-provide ((x 4) (y 5)) (provide x y))
        ((x 4) (y 5)))
      ((eval-provide ((x 4) (y 5)) (provide y x))
       ((y 5) (x 4)))
      ((eval-provide ((x 4) (y 5)) (provide y))
       ((y 5))))

    (check-exn exn:fail:contract?
      (λ () (term (eval-provide ((x 4)) (provide y)))))))

