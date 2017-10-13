#lang mf-apply racket/base

;; Typed Racket semantics,
;;  ....

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
   (where ρλ ((x #{apply-monitor#/fail x_mod v τ}) ...))])

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
   (where ρτ ((x #{apply-monitor#/fail x_mod v τ} τ) ...))])

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
  apply-monitor#/fail : x v τ -> v
  [(apply-monitor#/fail x v τ)
   v_mon
   (judgment-holds (apply-monitor x v τ v_mon))]
  [(apply-monitor#/fail x v τ)
   ,(raise-arguments-error 'apply-monitor "ill-typed value" "value" (term v) "type" (term τ) "value from" (term x))])

(define-metafunction μTR
  apply-monitor# : x v τ -> any
  [(apply-monitor# x v τ)
   v_mon
   (judgment-holds (apply-monitor x v τ v_mon))]
  [(apply-monitor# x v τ)
   #false])

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
   (where [v σ_+] #{eval-value x_modname σ ρλ e})
   (where ρλ_+ #{env-set ρλ (x v)})])

(define-metafunction μTR
  eval-typed-define* : x σ ρτ (DEFINE-τ ...) -> [σ ρτ]
  [(eval-typed-define* x_modname σ ρτ ())
   [σ ρτ]]
  [(eval-typed-define* x_modname σ ρτ (DEFINE-τ_first DEFINE-τ_rest ...))
   #{eval-typed-define* x_modname σ_+ ρτ_+ (DEFINE-τ_rest ...)}
   (where (define x τ e) DEFINE-τ_first)
   (where [v σ_+] #{eval-value x_modname σ ρτ e})
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
  eval-value : x σ ρ e -> [v σ]
  [(eval-value x_modname σ ρ e)
   [v_final σ_final]
   (where Σ_0 #{load-expression x_modname σ ρ e})
   (where A ,(step-expression* (term Σ_0)))
   (where (v_final σ_final x_modname) #{unload-answer A})])

;; NOTE ignores types in ρ
;;  maybe want to use the annotations to make better monitors?
(define-metafunction μTR
  load-expression : x σ ρ e -> Σ
  [(load-expression x_modname σ ρ e)
   (e_ρ σ x_modname ())
   (where e_ρ (substitute* e ρ))])

(define-metafunction μTR
  unload-answer : A -> [v σ x]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   (v σ x)
   (where (v σ x ()) Σ)]
  [(unload-answer Σ)
   ,(raise-arguments-error 'unload-answer
      "evaluation finished with non-empty stack"
      "stack" (term S)
      "value" (term v)
      "store" (term σ)
      "module" (term x))
   (where (v σ x S) Σ)])

(define step-expression
  (reduction-relation μTR
   #:domain A
   [-->
     (v σ x_mod S)
     A_next
     E-Return ;; this rule is special --- no context!
     (side-condition (not (null? (term S))))
     (where A_next #{do-return v σ x_mod S})]
   [-->
     ((in-hole E (v_0 v_1)) σ x_mod S)
     A_next
     E-Call
     (where A_next #{do-call E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (ifz v e_0 e_1)) σ x_mod S)
     ((in-hole E e_next) σ x_mod S)
     E-If
     (where e_next ,(if (zero? (term v)) (term e_0) (term e_1)))]
   [-->
     ((in-hole E (+ v_0 v_1)) σ x_mod S)
     A_next
     E-+
     (where A_next #{primop-arith + E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (- v_0 v_1)) σ x_mod S)
     A_next
     E--
     (where A_next #{primop-arith - E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (* v_0 v_1)) σ x_mod S)
     A_next
     E-*
     (where A_next #{primop-arith * E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (% v_0 v_1)) σ x_mod S)
     A_next
     E-%
     (where A_next #{primop-arith % E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (vector v ...)) σ x_mod S)
     ((in-hole E (vector x_loc)) σ_+ x_mod S)
     E-MakeVector
     (fresh x_loc)
     (where σ_+ #{loc-env-set σ x_loc (v ...)})]
   [-->
     ((in-hole E (vector-ref v_0 v_1)) σ x_mod S)
     A_next
     E-VectorRef
     (where A_next #{primop-ref E v_0 v_1 σ x_mod S})]
   [-->
     ((in-hole E (vector-set! v_0 v_1 v_2)) σ x_mod S)
     A_next
     E-VectorSet
     (where A_next #{primop-set E v_0 v_1 v_2 σ x_mod S})]
   [-->
     ((in-hole E (first v_0)) σ x_mod S)
     A_next
     E-first
     (where A_next #{primop-first E v_0 σ x_mod S})]
   [-->
     ((in-hole E (rest v_0)) σ x_mod S)
     A_next
     E-rest
     (where A_next #{primop-rest E v_0 σ x_mod S})]))

(define step-expression*
  (make--->* step-expression))

(define-metafunction μTR
  do-return : v σ x S -> A
  [(do-return v σ x ())
   ,(raise-arguments-error 'do-return "cannot return, empty stack"
      "value" (term v)
      "module" (term x)
      "store" (term σ))]
  [(do-return v σ x_server ((x_client E_next τ_expected) S_next))
   ,(if (term any_+)
      (term ((in-hole E_next any_+) σ x_client S_next))
      (term (BE x_client τ_expected x_server v)))
   (where any_+ #{apply-monitor# x_server v τ_expected})])

(define-metafunction μTR
  do-call : E v v σ x S -> A
  [(do-call E Λ v_arg σ x S)
   ((in-hole E e_body+) σ x S)
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-call E (mon-fun x_f τ v_f) v_arg σ x_arg S)
   ,(if (term any_v+)
      (term ((v_f any_v+) σ x_f S_+))
      (term (BE x_f τ_dom v_arg τ_cod)))
   (where (→ τ_dom τ_cod) τ)
   (where any_v+ #{apply-monitor# x_arg v_arg τ_dom})
   (where S_+ #{stack-push S (x_arg E τ_cod)})]
  [(do-call E v_0 v_1 σ x S)
   (TE v_0 "procedure?")
   (judgment-holds (not-fun-value v_0))])

(define-metafunction μTR
  primop-arith : any E v v σ x_mod S -> A
  [(primop-arith + E integer_0 integer_1 σ x_mod S)
   ((in-hole E ,(+ (term integer_0) (term integer_1))) σ x_mod S)]
  [(primop-arith - E integer_0 integer_1 σ x_mod S)
   ((in-hole E ,(- (term integer_0) (term integer_1))) σ x_mod S)]
  [(primop-arith * E integer_0 integer_1 σ x_mod S)
   ((in-hole E ,(* (term integer_0) (term integer_1))) σ x_mod S)]
  [(primop-arith % E integer_0 integer_1 σ x_mod S)
   DivisionByZero
   (where 0 integer_1)]
  [(primop-arith % E integer_0 integer_1 σ x_mod S)
   ((in-hole E ,(quotient (term integer_0) (term integer_1))) σ x_mod S)]
  [(primop-arith any_symbol E any integer σ x_mod S)
   (TE any "integer?")]
  [(primop-arith any_symbol E integer any σ x_mod S)
   (TE any "integer?")])

(define-metafunction μTR
  primop-first : E v σ x S -> A
  [(primop-first E nil σ x_mod S)
   EmptyList]
  [(primop-first E (cons v_0 _) σ x_mod S)
   [(in-hole E v_0) σ x_mod S]]
  [(primop-first E v σ x_mod S)
   (TE v "pair?")])

(define-metafunction μTR
  primop-rest : E v σ x S -> A
  [(primop-rest E nil σ x_mod S)
   EmptyList]
  [(primop-rest E (cons _ v_1) σ x_mod S)
   ((in-hole E v_1) σ x_mod S)]
  [(primop-rest E v σ x_mod S)
   (TE v "pair?")])

(define-metafunction μTR
  primop-ref : E v v σ x S -> A
  [(primop-ref E (vector x_loc) integer_index σ x_mod S)
   ,(if (term any_v)
      (term ((in-hole E any_v) σ x_mod S))
      (term BadIndex))
   (where (_ v*) #{loc-env-ref σ x_loc})
   (where any_v #{term-ref v* integer_index})]
  [(primop-ref E (mon-vector x_server (Vectorof τ) v_0) v_1 σ x_client S)
   (e_+ σ x_server S_+)
   (where e_+ (vector-ref v_0 v_1))
   (where S_+ #{stack-push S (x_client E τ)})]
  [(primop-ref E v_0 v_1 σ x_mod S)
   (TE v_0 "vector?")
   (judgment-holds (not-vector-value v_0))])

(define-metafunction μTR
  primop-set : E v v v σ x S -> A
  [(primop-set E (vector x_loc) integer_index v_2 σ x_mod S)
   ,(if (term any_set)
      (term ((in-hole E v_2) #{loc-env-update σ x_loc any_set} x_mod S))
      (term BadIndex))
   (where (_ v*) #{loc-env-ref σ x_loc})
   (where any_set #{term-set v* integer_index v_2})]
  [(primop-set E (mon-vector x_server (Vectorof τ) v_0) v_1 v_2 σ x_client S)
   ;; Technically this is crossing a type boundary (and therefore should do a stack frame)
   ;;  but `apply-monitor` does all the necessary checking.
   ,(if (term any_mon)
      (term ((in-hole E (vector-set! v_0 v_1 any_mon)) σ x_client S))
      (term (BE x_server τ x_client v_2)))
   (where any_mon #{apply-monitor# x_client v_2 τ})]
  [(primop-set E v_0 v_1 v_2 σ x S)
   (TE v_0 "vector?")
   (judgment-holds (not-vector-value v_0))])

(define-metafunction μTR
  term-ref : v* any -> any
  [(term-ref () integer)
   #f]
  [(term-ref (v_first v_rest ...) 0)
   v_first]
  [(term-ref (v_first v_rest ...) natural_k)
   (term-ref (v_rest ...) ,(- (term natural_k) 1))]
  [(term-ref v* _)
   #f])

(define-metafunction μTR
  term-set : v* any any -> any
  [(term-set () natural any)
   #f]
  [(term-set (v_first v_rest ...) 0 any_val)
   (any_val v_rest ...)]
  [(term-set (v_first v_rest ...) natural any_val)
   ,(if (term any_acc)
      (cons (term v_first) (term any_acc))
      (term BadIndex))
   (where any_acc #{term-set (v_rest ...) ,(- (term natural) 1) any_val})]
  [(term-set v* any_index any_val)
   #f])

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
     [(apply-monitor# m (vector x) (Vectorof Nat))
      (mon-vector m (Vectorof Nat) (vector x))]
     [(apply-monitor# m (cons (vector x) (cons (vector y) nil)) (Listof (Vectorof Int)))
      (cons (mon-vector m (Vectorof Int) (vector x)) (cons (mon-vector m (Vectorof Int) (vector y)) nil))]
     [(apply-monitor# m (fun f (x) (+ x x)) (→ Int Int))
      (mon-fun m (→ Int Int) (fun f (x) (+ x x)))]
    )

   (check-exn exn:fail:contract?
     (λ () (term (apply-monitor#/fail m 4 (Listof Int)))))
  )

  (test-case "runtime-env->untyped-runtime-env"
    (check-mf-apply*
     ((runtime-env->untyped-runtime-env m0 ())
      ())
     ((runtime-env->untyped-runtime-env m0 ((x 0) (y 1) (z (vector qq))))
      ((x 0) (y 1) (z (vector qq))))
     ((runtime-env->untyped-runtime-env m0 ((x 0 Nat) (z (vector q) (Vectorof Int))))
      ((x 0) (z (mon-vector m0 (Vectorof Int) (vector q)))))
    )
  )

  (test-case "runtime-env->typed-runtime-env"
    (check-mf-apply*
     ((runtime-env->typed-runtime-env m0 ((x 4) (y 1) (z (vector q))) (Nat Int (Vectorof Int)))
      ((x 4 Nat) (y 1 Int) (z (mon-vector m0 (Vectorof Int) (vector q)) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4) (z (vector q))) (Nat (Vectorof Int)))
      ((x 4 Nat) (z (mon-vector m0 (Vectorof Int) (vector q)) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4 Int) (z (vector q) (Vectorof Int))) (Int (Vectorof Int)))
      ((x 4 Int) (z (vector q) (Vectorof Int))))
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

  (test-case "eval-untyped-provide"
    (check-mf-apply*
     ((eval-untyped-provide ((x 4) (y (vector zzz))) (provide x y))
      ((x 4) (y (vector zzz))))
     ((eval-untyped-provide ((x 4) (y (cons 1 nil))) (provide x))
      ((x 4))))
  )

  (test-case "eval-typed-provide"
    (check-mf-apply*
     ((eval-typed-provide ((x 4 Nat) (y (vector qq) (Vectorof Nat))) (provide x y))
      ((x 4 Nat) (y (vector qq) (Vectorof Nat))))
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

  (test-case "term-ref"
    (check-mf-apply*
     ((term-ref (1) 0)
      1)
     ((term-ref (1 2 3) 0)
      1)
     ((term-ref (1 2 3) 2)
      3)
     ((term-ref (1 2 3) 4)
      #f)
     ((term-ref () 0)
      #f)
     ((term-ref (1) AAA)
      #f)))

  (test-case "term-set"
    (check-mf-apply*
     ((term-set (1) 0 2)
      (2))
     ((term-set (1 2 3) 0 2)
      (2 2 3))
     ((term-set (1 2 3) 2 A)
      (1 2 A))
     ((term-set () 2 2)
      #f)
     ((term-set () q 3)
      #f)))

  (test-case "do-return"
    (check-mf-apply*
     ((do-return 4 () m0 ((m1 hole Int) ()))
      (4 () m1 ()))
    )
  )

  (test-case "do-call"
    (check-mf-apply*
     ((do-call hole (fun f (x) x) 42 () m0 ())
      (42 () m0 ()))
    )
  )

  (test-case "primop-arith"
    (check-mf-apply*
     ((primop-arith + hole 2 2 () m0 ())
      (4 () m0 ()))
     ((primop-arith - hole 3 2 () m0 ())
      (1 () m0 ()))
     ((primop-arith * hole 3 3 () m0 ())
      (9 () m0 ()))
     ((primop-arith % hole 12 4 () m0 ())
      (3 () m0 ()))
     ((primop-arith % hole 5 2 () m0 ())
      (2 () m0 ()))
    )
  )

  (test-case "primop-first"
    (check-mf-apply*
     ((primop-first hole nil () m0 ())
      EmptyList)
     ((primop-first hole (cons 1 nil) () m0 ())
      (1 () m0 ()))
     ((primop-first (+ hole 2) (cons 1 nil) () m0 ())
      ((+ 1 2) () m0 ()))
    )
  )

  (test-case "primop-rest"
    (check-mf-apply*
     ((primop-rest hole nil () m0 ())
      EmptyList)
     ((primop-rest hole (cons 0 nil) () m0 ())
      (nil () m0 ()))
     ((primop-rest (+ hole 2) (cons 0 nil) ((a (2))) m0 ())
      ((+ nil 2) ((a (2))) m0 ()))
    )
  )

  (test-case "primop-ref"
    (check-mf-apply*
     ((primop-ref hole (vector qqq) 0 ((qqq (1 2 3))) m0 ())
      (1 ((qqq (1 2 3))) m0 ()))
     ((primop-ref (+ hole 1) (vector qqq) 0 ((qqq (1 2 3))) m0 ())
      ((+ 1 1) ((qqq (1 2 3))) m0 ()))
     ((primop-ref hole (vector qqq) 8 ((qqq (1 2 3))) m0 ())
      BadIndex)
     ((primop-ref hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 ((qqq (1 2 3))) m1 ())
      ((vector-ref (vector qqq) 0) ((qqq (1 2 3))) m0 ((m1 hole Int) ())))
    )
  )

  (test-case "primop-set"
    (check-mf-apply*
     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ())
      (5 ((qqq (5 2 3))) m0 ()))
     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ((m1 hole Int) ()))
      (5 ((qqq (5 2 3))) m0 ((m1 hole Int) ())))
     ((primop-set hole (vector qqq) 0 5 ((qqq ())) m0 ())
      BadIndex)
     ((primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ())
      ((vector-set! (vector qqq) 0 5) ((qqq (1))) m1 ()))
     ((primop-set (+ hole 1) (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ())
      ((+ (vector-set! (vector qqq) 0 5) 1) ((qqq (1))) m1 ()))
     ((primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 nil ((qqq (1))) m1 ())
      (BE m0 Int m1 nil))
     ((primop-set hole 1 2 3 () m0 ())
      (TE 1 "vector?"))
    )
  )

  (test-case "load-expression"
    (check-mf-apply*
     ((load-expression m0 () () (+ 2 2))
      ((+ 2 2) () m0 ()))
     ((load-expression m1 ((qqq (1))) ((x 3)) (+ 2 2))
      ((+ 2 2) ((qqq (1))) m1 ()))
     ((load-expression m1 ((qqq (1))) ((x 3)) (+ x 2))
      ((+ 3 2) ((qqq (1))) m1 ()))
    )
  )

  (test-case "unload-answer"
    (check-mf-apply*
     ((unload-answer ((vector q) ((q (1))) m0 ()))
      ((vector q) ((q (1))) m0))
    )

    (check-exn exn:fail:contract?
      (λ () (term (unload-answer BadIndex))))

    (check-exn exn:fail:contract?
      (λ () (term (unload-answer (0 () m0 ((m1 hole Int) ())))))))

  (test-case "step-expression"
    (check-equal?
      (apply-reduction-relation step-expression (term ((+ 2 2) () mod ())))
      '((4 () mod ())))
  )

  (test-case "eval-value"
    (check-mf-apply*
     ((eval-value mod0 () () (+ 2 2))
      (4 ()))
     ((eval-value mod0 () () (+ (+ 2 2) (+ 2 2)))
      (8 ()))
     ((eval-value mod0 ((q (1))) ((a 7)) (+ 2 2))
      (4 ((q (1)))))
     ((eval-value mod0 ((q (1))) ((a 7)) (+ a a))
      (14 ((q (1)))))
    )
  )

  (test-case "eval-untyped-define*"
    (check-mf-apply*
     ((eval-untyped-define* m0 () () ((define x 1) (define y 2) (define z 3)))
      (() ((z 3) (y 2) (x 1))))
    )
  )

  (test-case "eval-typed-define*"
    (check-mf-apply*
     ((eval-typed-define* m0 () () ((define x Nat 1) (define y Nat 2) (define z Int 3)))
      (() ((z 3 Int) (y 2 Nat) (x 1 Nat))))
    )
  )

  ;(test-case "redex-match"
  ;  (check-true
  ;    (redex-match? μTR DEFINE-τ (term
  ;    ))
  ;  )
  ;)

  (test-case "eval-program:I"
    (check-mf-apply*
     ((eval-program [(module-λ mu (define x 4) (provide x))])
      (() ((mu ((x 4))))))
     ((eval-program [(module-τ mt (define x Int 4) (provide x))])
      (() ((mt ((x 4 Int))))))
     ((eval-program
       ((module-λ M
         (define x (+ 2 2))
         (provide x))))
      (() ((M ((x 4))))))
     ((eval-program
       ((module-λ M
         (define x 2)
         (define y (+ x x))
         (provide x y))))
      (() ((M ((x 2) (y 4))))))
     ((eval-program
       ((module-λ M
         (define x (fun a (b) (+ b 1)))
         (define y (x 4))
         (provide y))))
      (() ((M ((y 5))))))
     ((eval-program
       ((module-τ M
         (define fact (→ Nat Nat) (fun fact (n) (ifz n 1 (* n (fact (- n 1))))))
         (define f0 Nat (fact 0))
         (define f1 Nat (fact 1))
         (define f2 Nat (fact 2))
         (define f3 Nat (fact 3))
         (define f4 Nat (fact 4))
         (provide f0 f1 f2 f3 f4))))
      (() ((M ((f0 1 Nat) (f1 1 Nat) (f2 2 Nat) (f3 6 Nat) (f4 24 Nat))))))
     ((eval-program
       ((module-τ M
         (define v (Vectorof Int) (vector 1 2 (+ 2 1)))
         (define x Int (vector-ref v 2))
         (define dontcare Int (vector-set! v 0 0))
         (define y Int (vector-ref v 0))
         (provide x y))))
      (((x_loc (0 2 3))) ((M ((x 3 Int) (y 0 Int))))))
     ((eval-program
       ((module-τ M
         (define second (→ (Listof Int) Int) (fun f (xs) (first (rest xs))))
         (define v Int (second (cons 1 (cons 2 nil))))
         (provide v))))
      (() ((M ((v 2 Int))))))
    )
  )

  (test-case "eval-program:TE"
    (check-exn #rx"TE"
      (λ () (term
        (eval-program
         ((module-τ M
           (define x Int (+ 1 nil))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (+ 1 nil))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program
         ((module-τ M
           (define x Int (first 4))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (vector-ref 4 4))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (4 4))
           (provide)))))))
  )

  (test-case "eval-program:RuntimeError"
    (check-exn #rx"DivisionByZero"
      (λ () (term
        (eval-program
         ((module-τ M
           (define x Int (% 1 0))
           (provide)))))))
    (check-exn #rx"DivisionByZero"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (% 1 0))
           (provide)))))))
    (check-exn #rx"EmptyList"
      (λ () (term
        (eval-program
         ((module-τ M
           (define x Int (first nil))
           (provide)))))))
    (check-exn #rx"EmptyList"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (rest nil))
           (provide)))))))
    (check-exn #rx"BadIndex"
      (λ () (term
        (eval-program
         ((module-τ M
           (define x Int (vector-ref (vector 1) 999))
           (provide)))))))
    (check-exn #rx"BadIndex"
      (λ () (term
        (eval-program
         ((module-λ M
           (define x (vector-set! (vector 0) 4 5))
           (provide))))))))

(test-case "rm"
  (check-true (redex-match? μTR σ (term
    ((x_loc (0))))))
  (check-true (redex-match? μTR ρ (term
    ((v (mon-vector M0 (Vectorof Int) (vector x_loc)))))))
  (check-true (redex-match? μTR e (term
    (vector-set! v 0 nil))))
  (check-true (redex-match? μTR e (term
    (mon-vector M0 (Vectorof Int) (vector x_loc))))))

  (test-case "eval-program:BE"
    (check-exn #rx"BE"
      (λ () (term
        (eval-program
         ((module-τ M0
           (define v (Vectorof Int) (vector 0))
           (provide v))
          (module-λ M1
           (require M0 v)
           (define x (vector-set! v 0 nil))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program
         ((module-λ M0
           (define v (vector -1))
           (provide v))
          (module-τ M1
           (require M0 (v (Vectorof Nat)))
           (define x Nat (vector-ref v 0))
           (provide)))))))

    (check-exn #rx"apply-monitor"
      (λ () (term
        (eval-program
         ((module-λ M0
           (define v -1)
           (provide v))
          (module-τ M1
           (require M0 (v Nat))
           (define x Int 42)
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program
         ((module-τ M0
           (define f (→ Nat Nat) (fun f (x) (+ x 2)))
           (provide f))
          (module-λ M1
           (require M0 f)
           (define x (f -1))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program
         ((module-λ M0
           (define f (fun f (x) nil))
           (provide f))
          (module-τ M1
           (require M0 (f (→ Int Int)))
           (define x Int (f 3))
           (provide)))))))
  )

  (test-case "valss"
    (check-true (redex-match? μTR e (term
      (fun f (x) (+ x 2))
    ))))

  (test-case "eval-program:bad-ann"
    (check-exn #rx"BE"
      (λ () (term (eval-program
        ((module-λ M0
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
          (provide f))
         (module-τ M1
          (require M0 (f (→ Int (→ Int Int))))
          (define f2 (→ Int Int) (f 2))
          (define f23 Int (f2 3))
          (provide f23)))))))

    (check-exn #rx"BE"
      (λ () (term (eval-program
        ((module-λ M0
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
          (provide f))
         (module-τ M1
          (require M0 (f (→ Int (→ Int Int))))
          (provide f))
         (module-λ M2
          (require M1 f)
          (define f2 (f 2))
          (define f23 (f2 3))
          (provide)))))))

    (check-exn #rx"TE"
      (λ () (term (eval-program
        ((module-λ M0
          (define f (fun a (x) (vector-ref x 0)))
          (provide f))
         (module-τ M1
          (require M0 (f (→ Nat Nat)))
          (define v Nat (f 4))
          (provide)))))))
  )

  (test-case "no-mon-between-typed"
    ;; If typed code imports a typed function,
    ;;  only do a subtyping check.
    ;; Do not monitor the typed function in typed code.
    ;; (Safe assuming type checker is correct)

    (check-mf-apply* #:is-equal? (λ (P-ENV M+x:v)
                                   (define M (car M+x:v))
                                   (define x:v (cadr M+x:v))
                                   (define x (car x:v))
                                   (define ρ (cadr (term #{program-env-ref ,(cadr P-ENV) ,M})))
                                   (define actual (term #{runtime-env-ref ,ρ ,x}))
                                   (equal? actual x:v))
      ((eval-program
        ((module-τ M0
          (define f (→ Nat Nat) (fun a (b) b))
          (provide f))
         (module-τ M1
          (require M0 (f (→ Nat Nat)))
          (define v Nil (f nil))
          (provide v))))
       (M1 (v nil Nil)))))
)

