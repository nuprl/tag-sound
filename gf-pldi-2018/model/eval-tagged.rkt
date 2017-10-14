#lang mf-apply racket/base

;; Tagged Racket semantics,
;;  ....

;; Diff from eval-untyped
;; - tag-check on require
;; - tag-check where checks appear (assumes rewritten program)

(provide
  eval-program
)

(require
  "eval-common.rkt"
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
   (where ρλ ((x v) ...))])

(define-metafunction μTR
  runtime-env->typed-runtime-env : x ρ τ* -> ρτ
  [(runtime-env->typed-runtime-env x_mod ρτ τ*)
   ρτ_sub
   (where ((x v τ_actual) ...) ρτ)
   (where (τ_expected ...) τ*)
   (where ρτ_sub ((x v #{assert-below τ_expected τ_actual}) ...))]
  [(runtime-env->typed-runtime-env x_mod ρλ τ*)
   ;; TODO abstract this, between here and eval-typed
   ,(let loop ([xv* (term ρλ)]
               [t* (term τ*)]
               [acc '()])
      (cond
       [(and (null? xv*) (null? t*))
        (reverse acc)]
       [(or (null? xv*) (null? t*))
        (raise-arguments-error 'runtime-env->typed-runtime-env
          "unequal number of types and values .. this can't be happening"
          "runtime-env" (term ρλ)
          "types" (term τ*))]
       [else
        (define x (car (car xv*)))
        (define v (cadr (car xv*)))
        (define t (car t*))
        (if (judgment-holds (tag-check ,v ,t))
          (loop (cdr xv*) (cdr t*) (cons (term (,x ,v ,t)) acc))
          (raise-arguments-error 'runtime-env->typed-runtime-env
            "require-error"
            "message" (term (BE x_mod ,t unknown-module ,v))))]))])

;; Check the given value against the tag of the given type,
;;  if the value is higher-order, return a "wrapped" value that remembers the type.
(define-judgment-form μTR
  #:mode (tag-check I I)
  #:contract (tag-check v any)
  [
   (well-tagged-value v κ)
   ---
   (tag-check v κ)]
  [
   (where κ #{type->tag τ})
   (well-tagged-value v κ)
   ---
   (tag-check v τ)])

(define-metafunction μTR
  tag-check# : v any -> any
  [(tag-check# v any)
   #true
   (judgment-holds (tag-check v any))]
  [(tag-check# x v τ)
   #false])

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

;; Notes:
;; - no E-Return rule
;; - yes E-Check rule
;; - no type-checks watsoever, expecting a "completed" program
(define step-expression
  (reduction-relation μTR
   #:domain A
   [-->
     ((in-hole E (!! [x κ e_x] e_body)) σ x_mod S)
     (e_x σ x_mod (FRAME S))
     E-Check
     (fresh x_f)
     (where FRAME (x_mod (in-hole E ((fun x_f (x) e_body) hole)) κ))]
   [-->
     (v σ x_mod S)
     A_next
     E-Return
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
     ((in-hole E (first v_0)) σ x_mod S)
     A_next
     E-first
     (where A_next #{primop-first E v_0 σ x_mod S})]
   [-->
     ((in-hole E (rest v_0)) σ x_mod S)
     A_next
     E-rest
     (where A_next #{primop-rest E v_0 σ x_mod S})]
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
     (where A_next #{primop-set E v_0 v_1 v_2 σ x_mod S})]))

(define step-expression*
  (make--->* step-expression))

(define-metafunction μTR
  do-return : v σ x S -> A
  [(do-return v σ x ())
   ,(raise-arguments-error 'do-return "cannot return, empty stack"
      "value" (term v)
      "module" (term x)
      "store" (term σ))]
  [(do-return v σ x_server ((x_client E_next κ_expected) S_next))
   ((in-hole E_next v) σ x_client S_next)
   (judgment-holds (tag-check v κ_expected))]
  [(do-return v σ x_server ((x_client E_next κ_expected) S_next))
   (BE x_client κ_expected x_server v)])

(define-metafunction μTR
  do-check : E x κ v e σ x S -> A
  [(do-check E x_v κ v e_body σ x_mod S)
   ((in-hole E e_subst) σ x_mod S)
   (judgment-holds (tag-check v κ))
   (where e_subst (substitute e_body x_v v))]
  [(do-check E x_v κ v e_body σ x_mod S)
   (BE x_mod κ context v)])

(define-metafunction μTR
  do-call : E v v σ x S -> A
  [(do-call E Λ v_arg σ x S)
   ((in-hole E e_body+) σ x S)
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
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
  [(primop-set E v_0 v_1 v_2 σ x S)
   (TE v_0 "vector?")
   (judgment-holds (not-vector-value v_0))])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "tag-check"
    (check-judgment-holds*
     (tag-check 4 Int)
     (tag-check nil (Listof (Vectorof Int)))
     (tag-check (cons 1 (cons 2 (cons 3 nil))) (Listof Int))
     (tag-check (vector x) (Vectorof Nat))
     (tag-check (cons (vector x) (cons (vector y) nil)) (Listof (Vectorof Int)))
     (tag-check (fun f (x) (+ x x)) (→ Int Int))
    )

    (check-not-judgment-holds*
     (tag-check 4 (Listof Int))
    )
  )

  (test-case "runtime-env->untyped-runtime-env"
    (check-mf-apply*
     ((runtime-env->untyped-runtime-env m0 ())
      ())
     ((runtime-env->untyped-runtime-env m0 ((x 0) (y 1) (z (vector qq))))
      ((x 0) (y 1) (z (vector qq))))
     ((runtime-env->untyped-runtime-env m0 ((x 0 Nat) (z (vector q) (Vectorof Int))))
      ((x 0) (z (vector q))))
    )
  )

  (test-case "runtime-env->typed-runtime-env"
    (check-mf-apply*
     ((runtime-env->typed-runtime-env m0 ((x 4) (y 1) (z (vector q))) (Nat Int (Vectorof Int)))
      ((x 4 Nat) (y 1 Int) (z (vector q) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4) (z (vector q))) (Nat (Vectorof Int)))
      ((x 4 Nat) (z (vector q) (Vectorof Int))))
     ((runtime-env->typed-runtime-env m0 ((x 4 Int) (z (vector q) (Vectorof Int))) (Int (Vectorof Int)))
      ((x 4 Int) (z (vector q) (Vectorof Int))))
    )
  )

  (test-case "eval-untyped-require*"

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
      ((num 4) (f (fun g (x) x))))
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
      ((num 4 Int) (f (fun g (x) x) (→ (Vectorof Int) (Vectorof Int)))))
     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 (num Int)) (require m1 (f (→ Int Int)))))
      ((num 4 Int) (f (fun g (x) x) (→ Int Int))))
    )

    (check-exn exn:fail:contract?
      (λ () (term (eval-typed-require* ((m0 ((num 4)))) ((require m0 (num (Vectorof Int))))))))
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
      BadIndex))

    (check-exn exn:fail:redex?
      (λ () (term (primop-ref hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 ((qqq (1 2 3))) m1 ()))))
  )

  (test-case "primop-set"
    (check-mf-apply*
     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ())
      (5 ((qqq (5 2 3))) m0 ()))
     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ((m1 hole Int) ()))
      (5 ((qqq (5 2 3))) m0 ((m1 hole Int) ())))
     ((primop-set hole (vector qqq) 0 5 ((qqq ())) m0 ())
      BadIndex)
     ((primop-set hole 1 2 3 () m0 ())
      (TE 1 "vector?"))
    )

    (check-exn exn:fail:redex?
      (λ () (term (primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ()))))

    (check-exn exn:fail:redex?
      (λ () (term (primop-set (+ hole 1) (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ()))))

    (check-exn exn:fail:redex?
      (λ () (term (primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 nil ((qqq (1))) m1 ()))))
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

  (test-case "eval-program:BE"
    (check-mf-apply*
     ((eval-program
       ((module-τ M0
         (define v (Vectorof Int) (vector 0))
         (provide v))
        (module-λ M1
         (require M0 v)
         (define x (vector-set! v 0 nil))
         (provide))))
      (((x_loc (nil))) ((M1 ()) (M0 ((v (vector x_loc) (Vectorof Int)))))))
    )

    (check-exn #rx"BE"
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
         ((module-λ M0
           (define v (vector -1))
           (provide v))
          (module-τ M1
           (require M0 (v (Vectorof Nat)))
           (define x Nat (!! [y Nat (vector-ref v 0)] y))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program
         ((module-τ M0
           (define f (→ Nat Nat) (fun f (x) (!! [x Nat x] (+ x 2))))
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
           (define x Int (!! [a Int (f 3)] a))
           (provide)))))))
  )

  (test-case "eval-program:bad-ann"
    (check-exn #rx"BE"
      (λ () (term (eval-program
        ((module-λ M0
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
          (provide f))
         (module-τ M1
          (require M0 (f (→ Int (→ Int Int))))
          (define f2 (→ Int Int) (f 2))
          (define f23 Int (!! [z Int (f2 3)] z))
          (provide f23)))))))

    (check-not-exn
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

)

