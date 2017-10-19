#lang mf-apply racket/base

;; Typed Racket semantics.
;;
;; This is ONLY the semantics.
;; No types involved, no theorems involved.
;; Just "how things should run".

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

(define-metafunction μTR
  eval-program# : PROGRAM -> [σ VAL-ENV]
  [(eval-program# PROGRAM)
   (σ VAL-ENV)
   (judgment-holds (eval-program PROGRAM σ VAL-ENV))]
  [(eval-program# PROGRAM)
   ,(raise-arguments-error 'eval-program "failed to evaluate" "program" (term PROGRAM))])

(define-judgment-form μTR
  #:mode (eval-program I O O)
  #:contract (eval-program PROGRAM σ VAL-ENV)
  [
   (where (MODULE ...) PROGRAM)
   (eval-module* () () (MODULE ...) σ VAL-ENV)
   ---
   (eval-program PROGRAM σ VAL-ENV)])

(define-judgment-form μTR
  #:mode (eval-module* I I I O O)
  #:contract (eval-module* σ VAL-ENV (MODULE ...) σ VAL-ENV)
  [
   ---
   (eval-module* σ VAL-ENV () σ VAL-ENV)]
  [
   (where (MODULE_0 MODULE_rest ...) PROGRAM)
   (eval-module σ VAL-ENV MODULE_0 σ_1 VAL-ENV_1)
   (eval-module* σ_1 VAL-ENV_1 (MODULE_rest ...) σ_N VAL-ENV_N)
   ---
   (eval-module* σ VAL-ENV PROGRAM σ_N VAL-ENV_N)])

(define-judgment-form μTR
  #:mode (eval-module I I I O O)
  #:contract (eval-module σ VAL-ENV MODULE σ VAL-ENV)
  [
   (where (module M _ REQUIRE ... DEFINE ... PROVIDE) MODULE)
   (where ρ #{require->local-value-env VAL-ENV (REQUIRE ...)})
   (eval-define* σ ρ (DEFINE ...) σ_+ ρ_+)
   (where ρ_provide #{local-value-env->provided ρ_+ PROVIDE})
   (where VAL-ENV_+ #{toplevel-value-env-set VAL-ENV M ρ_provide})
   --- E-Module-Untyped
   (eval-module σ VAL-ENV MODULE σ_+ VAL-ENV_+)])

;; -----------------------------------------------------------------------------
;; --- intermission, metafunctions for eval-module

(define-metafunction μTR
  require->local-value-env : VAL-ENV (REQUIRE ...) -> ρ
  [(require->local-value-env VAL-ENV ())
   ()]
  [(require->local-value-env VAL-ENV (TYPED-REQUIRE_0 TYPED-REQUIRE_rest ...))
   #{local-value-env-append ρ_expected ρ_rest}
   (where (require M Γ_expected) TYPED-REQUIRE_0)
   (where (M ρ_actual) #{toplevel-value-env-ref VAL-ENV M})
   (where ρ_expected #{import/typed Γ_expected ρ_actual})
   (where ρ_rest #{require->local-value-env VAL-ENV (TYPED-REQUIRE_rest ...)})]
  [(require->local-value-env VAL-ENV (UNTYPED-REQUIRE_0 UNTYPED-REQUIRE_rest ...))
   #{local-value-env-append ρ_expected ρ_rest}
   (where (require M x ...) UNTYPED-REQUIRE_0)
   (where (M ρ_actual) #{toplevel-value-env-ref VAL-ENV M})
   (where ρ_expected #{import/untyped (x ...) ρ_actual})
   (where ρ_rest #{require->local-value-env VAL-ENV (UNTYPED-REQUIRE_rest ...)})])

(define-metafunction μTR
  import/typed : Γ ρ -> ρ
  [(import/typed () ρ)
   ()]
  [(import/typed ((x τ) x:τ_rest ...) ρ)
   #{local-value-env-set ρ_rest x v_+}
   (where (_ v) #{local-value-env-ref ρ x})
   (where v_+ #{check-value v τ})
   (where ρ_rest #{import/typed (x:τ_rest ...) ρ})])

;; Usually call `apply-monitor`, but skip the boundary for typed functions and vectors
(define-metafunction μTR
  check-value : v τ -> v
  [(check-value v_fun)
   v_fun
   (where (fun _ τ_fun (_) _) v_fun)
   (side-condition
     (unless (judgment-holds (<: τ_fun τ))
       (raise-arguments-error 'check-value "cannot import typed value at incompatible type"
         "value" (term v_fun)
         "actual type" (term τ_fun)
         "import type" (term τ))))]
  [(check-value v_vec)
   v_vec
   (where (vector τ_vec _) v_vec)
   (side-condition
     (unless (judgment-holds (<: τ_vec τ))
       (raise-arguments-error 'check-value "cannot import typed value at incompatible type"
         "value" (term v_vec)
         "actual type" (term τ_vec)
         "import type" (term τ))))]
  [(check-value v)
   #{apply-monitor#/fail v τ}])

(define-metafunction μTR
  import/untyped : x* ρ -> ρ
  [(import/untyped () ρ)
   ()]
  [(import/untyped (x x_rest ...) ρ)
   #{local-value-env-set ρ_rest x v_+}
   (where (_ v) #{local-value-env-ref ρ x})
   (where v_+ #{protect-value v})
   (where ρ_rest #{import/untyped (x_rest ...) ρ})])

(define-metafunction μTR
  protect-value : v -> v
  [(protect-value v_fun)
   #{apply-monitor#/fail v_fun τ_fun}
   (where (fun _ τ_fun (_) _) v_fun)]
  [(protect-value v_vec)
   #{apply-monitor#/fail v_vec τ_vec}
   (where (vector τ_vec _) v_vec)]
  [(protect-value v)
   v])

(define-metafunction μTR
  local-value-env->provided : ρ PROVIDE -> ρ
  [(local-value-env->provided ρ (provide))
   ()]
  [(local-value-env->provided ρ (provide x_0 x_rest ...))
   (x:τ_0 x:τ_rest ...)
   (where x:τ_0 #{local-value-env-ref ρ x_0})
   (where (x:τ_rest ...) #{local-value-env->provided ρ (provide x_rest ...)})])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (eval-define* I I I O O)
  #:contract (eval-define* σ ρ (DEFINE ...) σ ρ)
  [
   ---
   (eval-define* σ ρ () σ ρ)]
  [
   (eval-define σ ρ DEFINE_0 σ_1 ρ_1)
   (eval-define* σ_1 ρ_1 (DEFINE_rest ...) σ_N ρ_N)
   ---
   (eval-define* σ ρ (DEFINE_0 DEFINE_rest ...) σ_N ρ_N)])

;; Ignore the type annotation, evaluate the expression, save in ρ
(define-judgment-form μTR
  #:mode (eval-define I I I O O)
  #:contract (eval-define σ ρ DEFINE σ ρ)
  [
   (where (define x e) UNTYPED-DEFINE)
   (where L UN)
   (eval-expression σ ρ L e σ_+ v_+)
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (eval-define σ ρ UNTYPED-DEFINE σ_+ ρ_+)]
  [
   (where (define x τ e) TYPED-DEFINE)
   (where L TY)
   (eval-expression σ ρ L e σ_+ v_+)
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (eval-define σ ρ TYPED-DEFINE σ_+ ρ_+)])

(define-judgment-form μTR
  #:mode (eval-expression I I I I O O)
  #:contract (eval-expression σ ρ L e σ v)
  [
   (where Σ_0 #{load-expression L σ ρ e})
   (where A ,(step* (term Σ_0)))
   (where (σ_+ v_+) #{unload-answer A})
   ---
   (eval-expression σ ρ L e σ_+ v_+)])

;; -----------------------------------------------------------------------------

(define single-step
  (reduction-relation μTR
   #:domain A
   [-->
     (L σ (in-hole E (check τ v)))
     A_next
     E-CheckT
     (judgment-holds (typed-context E L))
     (where A_next #{do-check L σ E v τ})]
   [-->
     (L σ (in-hole E (protect τ v)))
     A_next
     E-ProtectU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-protect L σ E v τ})]

   [-->
     (L σ (in-hole E (v_0 v_1)))
     A_next
     E-ApplyT
     (judgment-holds (typed-context E L))
     (where A_next #{do-apply/typed L σ E v_0 v_1})]
   [-->
     (L σ (in-hole E (v_0 v_1)))
     A_next
     E-ApplyU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-apply/untyped L σ E v_0 v_1})]

   [-->
     (L σ (in-hole E (vector v ...)))
     (L σ_+ (in-hole E (vector loc)))
     E-MakeVector
     (fresh loc)
     (where σ_+ #{store-set σ loc (v ...)})]
   [-->
     (L σ (in-hole E (vector-ref v_0 v_1)))
     A_next
     E-VectorRefT
     (judgment-holds (typed-context E L))
     (where A_next #{do-ref/typed L σ E v_0 v_1})]
   [-->
     (L σ (in-hole E (vector-ref v_0 v_1)))
     A_next
     E-VectorRefU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-ref/untyped L σ E v_0 v_1})]

   [-->
     (L σ (in-hole E (vector-set! v_0 v_1 v_2)))
     A_next
     E-VectorSetT
     (judgment-holds (typed-context E L))
     (where A_next #{do-set/typed L σ E v_0 v_1 v_2})]
   [-->
     (L σ (in-hole E (vector-set! v_0 v_1 v_2)))
     A_next
     E-VectorSetU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-set/untyped L σ E v_0 v_1 v_2})]

   [-->
     (L σ (in-hole E (ifz v e_0 e_1)))
     (L σ (in-hole E e_next))
     E-IfzT
     (judgment-holds (typed-context E L))
     (where e_next ,(if (zero? (term v)) (term e_0) (term e_1)))]
   [-->
     (L σ (in-hole E (ifz v e_0 e_1)))
     A_next
     E-IfzU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-ifz/untyped L σ E v e_0 e_1})]

   [-->
     (L σ (in-hole E (BINOP v_0 v_1)))
     A_next
     E-ArithT
     (judgment-holds (typed-context E L))
     (where A_next #{do-arith/typed BINOP L σ E v_0 v_1})]
   [-->
     (L σ (in-hole E (BINOP v_0 v_1)))
     A_next
     E-ArithU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-arith/untyped BINOP L σ E v_0 v_1})]

   [-->
     (L σ (in-hole E (first v)))
     A_next
     E-firstT
     (judgment-holds (typed-context E L))
     (where A_next #{do-first/typed L σ E v})]
   [-->
     (L σ (in-hole E (first v)))
     A_next
     E-firstU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-first/untyped L σ E v})]

   [-->
     (L σ (in-hole E (rest v)))
     A_next
     E-restT
     (judgment-holds (typed-context E L))
     (where A_next #{do-rest/typed L σ E v})]
   [-->
     (L σ (in-hole E (rest v)))
     A_next
     E-restU
     (judgment-holds (untyped-context E L))
     (where A_next #{do-rest/untyped L σ E v})]))

(define step*
  (make--->* single-step))

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  make-answer : L σ E any -> A
  [(make-answer L σ E Error)
   Error]
  [(make-answer L σ E e)
   (L σ (in-hole E e))])

(define-metafunction μTR
  do-check : L σ E v τ -> A
  [(do-check L σ E v τ)
   #{do-return L σ E v τ}])

(define-metafunction μTR
  do-protect : L σ E v τ -> A
  [(do-protect L σ E v τ)
   #{do-return L σ E v τ}])

(define-metafunction μTR
  do-return : L σ E v τ -> A
  [(do-return L σ E v τ)
   #{make-answer L σ E #{apply-monitor# v τ}}])

(define-metafunction μTR
  do-apply/untyped : L σ E v v -> A
  [(do-apply/untyped _ _ _ v _)
   (TE v "procedure?")
   (judgment-holds (not-fun-value v))]
  [(do-apply/untyped L σ E v_0 v_1)
   #{do-apply L σ E v_0 v_1 L_hole}
   (where L_hole UN)])

(define-metafunction μTR
  do-apply/typed : L σ E v v -> A
  [(do-apply/typed L σ E v_0 v_1)
   #{do-apply L σ E v_0 v_1 L_hole}
   (where L_hole TY)])

(define-metafunction μTR
  do-apply : L σ E v v L -> A
  [(do-apply L σ E v_0 v_1 _)
   (L σ (in-hole E e_body+))
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply L σ E (mon-fun x_f τ v_f) v_arg L_hole)
   #{make-answer L σ E_+ #{apply-monitor# v_arg τ_dom}}
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (where E_+
     ,(cond
       [(equal? (term UN) (term L_hole))
        (term (in-hole E (protect τ_cod (v_f hole))))]
       [(equal? (term TY) (term L_hole))
        (term (in-hole E (check τ_cod (v_f hole))))]
       [else
        (raise-arguments-error 'do-apply "bad language" "lang" (term L_hole))]))])

(define-metafunction μTR
  do-ref/typed : L σ E v v -> A
  [(do-ref/typed L σ E v_0 v_1)
   #{do-ref L σ E v_0 v_1 L_hole}
   (where L_hole TY)])

(define-metafunction μTR
  do-ref/untyped : L σ E v v -> A
  [(do-ref/untyped _ _ _ v _)
   (TE v "vector?")
   (judgment-holds (not-vector-value v))]
  [(do-ref/untyped L σ E v_0 v_1)
   #{do-ref L E σ v_0 v_1 L_hole}
   (where L_hole UN)])

(define-metafunction μTR
  do-ref : L σ E v v L -> A
  [(do-ref L σ E (vector loc) integer_index _)
   #{make-answer L E σ #{term-ref v* integer_index}}
   (where (_ v*) #{store-ref σ loc})]
  [(do-ref L σ E (mon-vector τ v_0) v_1 L_hole)
   #{make-answer E_+ σ any_+}
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (where E_+
     ,(cond
       [(equal? (term UN) (term L_hole))
        (term (in-hole E (protect τ_elem (vector-ref v_0 v_1))))]
       [(equal? (term TY) (term L_hole))
        (term (in-hole E (check τ_elem (vector-ref v_0 v_1))))]
       [else
        (raise-arguments-error 'do-ref "bad language" "lang" (term L_hole))]))])

(define-metafunction μTR
  do-set/typed : L σ E v v v -> A
  [(do-set/typed L σ E v_0 v_1 v_2)
   #{do-set L σ E v_0 v_1 v_2 L_hole}
   (where L_hole TY)])

(define-metafunction μTR
  do-set/untyped : L σ E v v v -> A
  [(do-set/untyped _ _ _ v _ _)
   (TE v "vector?")]
  [(do-set/untyped L σ E v_0 v_1 v_2)
   #{do-set L σ E v_0 v_1 v_2 L_hole}
   (where L_hole UN)])

(define-metafunction μTR
  do-set : L σ E v v v L -> A
  [(do-set L σ E (vector loc) v_1 v_2 _)
   ,(if (term any_set)
      (term (L #{store-update σ loc any_set} (in-hole E v_2)))
      (term BadIndex))
   (where (_ v*) #{store-ref σ loc})
   (where any-set #{term-set v* integer_index v_2})]
  [(do-set L σ E (mon-vector τ v_0) v_1 v_2 L_hole)
   #{make-answer L σ E_+ #{apply-monitor# v_2 τ}}
   (where (Vectorof τ_elem) τ)
   (where E_+ (in-hole E (vector-set v_0 v_1 hole)))])

(define-metafunction μTR
  do-ifz/untyped : L σ E v e e -> A
  [(do-ifz/untyped L σ E v e_0 e_1)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-ifz/untyped L σ E 0 e_0 e_1)
   (L σ (in-hole E e_0))]
  [(do-ifz/untyped L σ E integer e_0 e_1)
   (L σ (in-hole E e_1))
   (side-condition (not (zero? (term integer))))])

(define-metafunction μTR
  do-arith/untyped : BINOP L σ E v v -> A
  [(do-arith/untyped _ _ _ _ v _)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped _ _ _ _ _ v)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped BINOP L σ E v v)
   #{do-arith BINOP L σ E v v}])

(define-metafunction μTR
  do-arith/typed : BINOP L σ E v v -> A
  [(do-arith/typed BINOP L σ E v v)
   #{do-arith BINOP L σ E v v}])

(define-metafunction μTR
  do-arith : BINOP L σ E v v -> A
  [(do-arith + E σ integer_0 integer_1)
   (L σ (in-hole E ,(+ (term integer_0) (term integer_1))))]
  [(do-arith - E σ integer_0 integer_1)
   (L σ (in-hole E ,(- (term integer_0) (term integer_1))))]
  [(do-arith * E σ integer_0 integer_1)
   (L σ (in-hole E ,(* (term integer_0) (term integer_1))))]
  [(do-arith % E σ integer_0 integer_1)
   DivisionByZero
   (side-condition (zero? (term integer_1)))]
  [(do-arith % E σ integer_0 integer_1)
   (L σ (in-hole E ,(quotient (term integer_0) (term integer_1))))
   (side-condition (not (zero? (term integer_1))))])

(define-metafunction μTR
  do-first/untyped : L σ E v -> A
  [(do-first/untyped _ _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-first/untyped L σ E v)
   #{do-first L σ E v}])

(define-metafunction μTR
  do-first/typed : L σ E v -> A
  [(do-first/typed L σ E v)
   #{do-first L σ E v}])

(define-metafunction μTR
  do-first : L σ E v -> A
  [(do-first _ _ _ nil)
   EmptyList]
  [(do-first L σ E (cons v_0 _))
   (L σ (in-hole E v_0))])

(define-metafunction μTR
  do-rest/untyped : L σ E v -> A
  [(do-rest/untyped _ _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-rest/untyped L σ E v)
   #{do-rest L σ E v}])

(define-metafunction μTR
  do-rest/typed : L σ E v -> A
  [(do-rest/typed L σ E v)
   #{do-rest L σ E v}])

(define-metafunction μTR
  do-rest : L σ E v -> A
  [(do-rest _ _ _ nil)
   EmptyList]
  [(do-rest L σ E (cons _ v_1))
   (L σ (in-hole E v_1))])

(define-metafunction μTR
  load-expression : L σ E ρ e -> Σ
  [(load-expression L σ E ρ e)
   (L σ (substitute* e ρ))])

(define-metafunction μTR
  unload-answer : A -> [σ v]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   (σ v)
   (where (L σ v) Σ)])

(define-metafunction μTR
  unload-answer/store : A -> e
  [(unload-answer/store A)
   e_sub
   (where (L σ v) #{unload-answer A})
   (where e_sub #{unload-store v σ})])

;; -----------------------------------------------------------------------------
;
;(define-metafunction μTR
;  eval-untyped-require* : VAL-ENV (REQUIRE-λ ...) -> ρλ
;  [(eval-untyped-require* VAL-ENV ())
;   ()]
;  [(eval-untyped-require* VAL-ENV (REQUIRE-λ_first REQUIRE-λ_rest ...))
;   #{env-set* ρλ_rest ρλ_first}
;   (where ρλ_first #{eval-untyped-require VAL-ENV REQUIRE-λ_first})
;   (where ρλ_rest #{eval-untyped-require* VAL-ENV (REQUIRE-λ_rest ...)})])
;
;(define-metafunction μTR
;  eval-typed-require* : VAL-ENV (REQUIRE-τ ...) -> ρτ
;  [(eval-typed-require* VAL-ENV ())
;   ()]
;  [(eval-typed-require* VAL-ENV (REQUIRE-τ_first REQUIRE-τ_rest ...))
;   #{env-set* ρτ_rest ρτ_first}
;   (where ρτ_first #{eval-typed-require VAL-ENV REQUIRE-τ_first})
;   (where ρτ_rest #{eval-typed-require* VAL-ENV (REQUIRE-τ_rest ...)})])
;
;(define-metafunction μTR
;  eval-untyped-require : VAL-ENV REQUIRE-λ -> ρλ
;  [(eval-untyped-require VAL-ENV REQUIRE-λ)
;   ρλ
;   (where (require x_mod x_require ...) REQUIRE-λ)
;   (where (x_mod ρ_mod) (program-env-ref VAL-ENV x_mod))
;   (where any_fail ,(λ (x)
;                      (raise-arguments-error 'eval-untyped-require
;                        "required identifier not provided by module"
;                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
;   (where ρ_mixed (#{runtime-env-ref ρ_mod x_require any_fail} ...))
;   (where ρλ #{runtime-env->untyped-runtime-env x_mod ρ_mixed})]
;  [(eval-untyped-require VAL-ENV REQUIRE-λ)
;   ,(raise-arguments-error 'eval-untyped-require
;      "required module does not exist"
;      "module" (term x) "env" (term VAL-ENV))
;   (where (require x_mod _ ...) REQUIRE-λ)])
;
;(define-metafunction μTR
;  eval-typed-require : VAL-ENV REQUIRE-τ -> ρτ
;  [(eval-typed-require VAL-ENV REQUIRE-τ)
;   ρτ
;   (where (require x_mod [x_require τ_require] ...) REQUIRE-τ)
;   (where (x_mod ρ_mod) (program-env-ref VAL-ENV x_mod))
;   (where any_fail ,(λ (x)
;                      (raise-arguments-error 'eval-typed-require
;                        "required identifier not provided by module"
;                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
;   (where ρ_mixed (#{runtime-env-ref ρ_mod x_require any_fail} ...))
;   (where ρτ #{runtime-env->typed-runtime-env x_mod ρ_mixed (τ_require ...)})]
;  [(eval-typed-require VAL-ENV REQUIRE-τ)
;   ,(raise-arguments-error 'eval-typed-require
;      "required module does not exist"
;      "module" (term x) "env" (term VAL-ENV))
;   (where (require x_mod _ ...) REQUIRE-τ)])
;
;(define-metafunction μTR
;  runtime-env->untyped-runtime-env : x ρ -> ρλ
;  [(runtime-env->untyped-runtime-env x_mod ρλ)
;   ρλ]
;  [(runtime-env->untyped-runtime-env x_mod ρτ)
;   ρλ
;   (where ((x v τ) ...) ρτ)
;   ;; protect typed values in untyped code
;   (where ρλ ((x #{apply-monitor#/fail x_mod v τ}) ...))])
;
;(define-metafunction μTR
;  runtime-env->typed-runtime-env : x ρ τ* -> ρτ
;  [(runtime-env->typed-runtime-env x_mod ρτ τ*)
;   ρτ_sub
;   (where ((x v τ_actual) ...) ρτ)
;   (where (τ_expected ...) τ*)
;   (where ρτ_sub ((x v #{assert-below τ_expected τ_actual}) ...))]
;  [(runtime-env->typed-runtime-env x_mod ρλ τ*)
;   ,(let loop ([xv* (term ρλ)]
;               [t* (term τ*)]
;               [acc '()])
;      (cond
;       [(and (null? xv*) (null? t*))
;        (reverse acc)]
;       [(or (null? xv*) (null? t*))
;        (raise-arguments-error 'runtime-env->typed-runtime-env
;          "unequal number of types and values .. this can't be happening"
;          "runtime-env" (term ρλ)
;          "types" (term τ*))]
;       [else
;        (define x (car (car xv*)))
;        (define v (cadr (car xv*)))
;        (define t (car t*))
;        (define v_mon (term #{apply-monitor# x_mod ,v ,t}))
;        (if v_mon
;          (loop (cdr xv*) (cdr t*) (cons (term (,x ,v_mon ,t)) acc))
;          (raise-arguments-error 'runtime-env->typed-runtime-env
;            "require-error"
;            "message" (term (BE x_mod ,t unknown-module ,v))))]))])

;; -----------------------------------------------------------------------------

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
  apply-monitor#/fail : v τ -> v
  [(apply-monitor#/fail v τ)
   v_mon
   (judgment-holds (apply-monitor v τ v_mon))]
  [(apply-monitor#/fail v τ)
   ,(raise-arguments-error 'apply-monitor "ill-typed value" "value" (term v) "type" (term τ))])

(define-metafunction μTR
  apply-monitor# : v τ -> any
  [(apply-monitor# v τ)
   v_mon
   (judgment-holds (apply-monitor v τ v_mon))]
  [(apply-monitor# v τ)
   #false])

;; =============================================================================

;(module+ test
;  (require rackunit)
;
;  (test-case "apply-monitor"
;    (check-mf-apply*
;     [(apply-monitor# m 4 Int)
;      4]
;     [(apply-monitor# m nil (Listof (Vectorof Int)))
;      nil]
;     [(apply-monitor# m (cons 1 (cons 2 (cons 3 nil))) (Listof Int))
;      (cons 1 (cons 2 (cons 3 nil)))]
;     [(apply-monitor# m (vector x) (Vectorof Nat))
;      (mon-vector m (Vectorof Nat) (vector x))]
;     [(apply-monitor# m (cons (vector x) (cons (vector y) nil)) (Listof (Vectorof Int)))
;      (cons (mon-vector m (Vectorof Int) (vector x)) (cons (mon-vector m (Vectorof Int) (vector y)) nil))]
;     [(apply-monitor# m (fun f (x) (+ x x)) (→ Int Int))
;      (mon-fun m (→ Int Int) (fun f (x) (+ x x)))]
;    )
;
;   (check-exn exn:fail:contract?
;     (λ () (term (apply-monitor#/fail m 4 (Listof Int)))))
;  )
;
;  (test-case "runtime-env->untyped-runtime-env"
;    (check-mf-apply*
;     ((runtime-env->untyped-runtime-env m0 ())
;      ())
;     ((runtime-env->untyped-runtime-env m0 ((x 0) (y 1) (z (vector qq))))
;      ((x 0) (y 1) (z (vector qq))))
;     ((runtime-env->untyped-runtime-env m0 ((x 0 Nat) (z (vector q) (Vectorof Int))))
;      ((x 0) (z (mon-vector m0 (Vectorof Int) (vector q)))))
;    )
;  )
;
;  (test-case "runtime-env->typed-runtime-env"
;    (check-mf-apply*
;     ((runtime-env->typed-runtime-env m0 ((x 4) (y 1) (z (vector q))) (Nat Int (Vectorof Int)))
;      ((x 4 Nat) (y 1 Int) (z (mon-vector m0 (Vectorof Int) (vector q)) (Vectorof Int))))
;     ((runtime-env->typed-runtime-env m0 ((x 4) (z (vector q))) (Nat (Vectorof Int)))
;      ((x 4 Nat) (z (mon-vector m0 (Vectorof Int) (vector q)) (Vectorof Int))))
;     ((runtime-env->typed-runtime-env m0 ((x 4 Int) (z (vector q) (Vectorof Int))) (Int (Vectorof Int)))
;      ((x 4 Int) (z (vector q) (Vectorof Int))))
;    )
;  )
;
;  (test-case "eval-untyped-require*"
;
;    (check-mf-apply*
;     ((eval-untyped-require* () ())
;      ())
;     ((eval-untyped-require* ((m0 ((n 4)))) ((require m0 n)))
;      ((n 4)))
;     ((eval-untyped-require* ((m0 ((num 4) (y 5)))) ((require m0 num)))
;      ((num 4)))
;     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 num)))
;      ((num 4)))
;     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 num) (require m1 f)))
;      ((num 4) (f (fun g (x) x))))
;     ((eval-untyped-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 num) (require m1 f)))
;      ((num 4) (f (mon-fun m1 (→ Int Int) (fun g (x) x)))))
;    )
;
;    (check-exn exn:fail:contract?
;      (λ () (term (eval-untyped-require* () ((require m x))))))
;  )
;
;  (test-case "eval-typed-require*"
;    (check-mf-apply*
;     ((eval-typed-require* () ())
;      ())
;     ((eval-typed-require* ((m0 ((num 4 Nat)))) ((require m0 [num Nat])))
;      ((num 4 Nat)))
;     ((eval-typed-require* ((m0 ((num 4) (y 5)))) ((require m0 [num Nat])))
;      ((num 4 Nat)))
;     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x))))) ((require m0 [num Nat])))
;      ((num 4 Nat)))
;     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
;                           ((require m0 (num Int)) (require m1 (f (→ (Vectorof Int) (Vectorof Int))))))
;      ((num 4 Int) (f (mon-fun m1 (→ (Vectorof Int) (Vectorof Int)) (fun g (x) x)) (→ (Vectorof Int) (Vectorof Int)))))
;     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 (num Int)) (require m1 (f (→ Int Int)))))
;      ((num 4 Int) (f (fun g (x) x) (→ Int Int))))
;    )
;
;    (check-exn exn:fail:contract?
;      (λ () (term (eval-typed-require* ((m0 ((num 4)))) ((require m0 (num (Vectorof Int))))))))
;  )
;
;  (test-case "do-return"
;    (check-mf-apply*
;     ((do-return 4 () m0 ((m1 hole Int) ()))
;      (4 () m1 ()))
;    )
;  )
;
;  (test-case "do-call"
;    (check-mf-apply*
;     ((do-call hole (fun f (x) x) 42 () m0 ())
;      (42 () m0 ()))
;    )
;  )
;
;  (test-case "do-arith/untyped"
;    (check-mf-apply*
;     ((do-arith/untyped + hole 2 2 () m0 ())
;      (4 () m0 ()))
;     ((do-arith/untyped - hole 3 2 () m0 ())
;      (1 () m0 ()))
;     ((do-arith/untyped * hole 3 3 () m0 ())
;      (9 () m0 ()))
;     ((do-arith/untyped % hole 12 4 () m0 ())
;      (3 () m0 ()))
;     ((do-arith/untyped % hole 5 2 () m0 ())
;      (2 () m0 ()))
;    )
;  )
;
;  (test-case "primop-first"
;    (check-mf-apply*
;     ((primop-first hole nil () m0 ())
;      EmptyList)
;     ((primop-first hole (cons 1 nil) () m0 ())
;      (1 () m0 ()))
;     ((primop-first (+ hole 2) (cons 1 nil) () m0 ())
;      ((+ 1 2) () m0 ()))
;    )
;  )
;
;  (test-case "primop-rest"
;    (check-mf-apply*
;     ((primop-rest hole nil () m0 ())
;      EmptyList)
;     ((primop-rest hole (cons 0 nil) () m0 ())
;      (nil () m0 ()))
;     ((primop-rest (+ hole 2) (cons 0 nil) ((a (2))) m0 ())
;      ((+ nil 2) ((a (2))) m0 ()))
;    )
;  )
;
;  (test-case "primop-ref"
;    (check-mf-apply*
;     ((primop-ref hole (vector qqq) 0 ((qqq (1 2 3))) m0 ())
;      (1 ((qqq (1 2 3))) m0 ()))
;     ((primop-ref (+ hole 1) (vector qqq) 0 ((qqq (1 2 3))) m0 ())
;      ((+ 1 1) ((qqq (1 2 3))) m0 ()))
;     ((primop-ref hole (vector qqq) 8 ((qqq (1 2 3))) m0 ())
;      BadIndex)
;     ((primop-ref hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 ((qqq (1 2 3))) m1 ())
;      ((vector-ref (vector qqq) 0) ((qqq (1 2 3))) m0 ((m1 hole Int) ())))
;    )
;  )
;
;  (test-case "primop-set"
;    (check-mf-apply*
;     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ())
;      (5 ((qqq (5 2 3))) m0 ()))
;     ((primop-set hole (vector qqq) 0 5 ((qqq (1 2 3))) m0 ((m1 hole Int) ()))
;      (5 ((qqq (5 2 3))) m0 ((m1 hole Int) ())))
;     ((primop-set hole (vector qqq) 0 5 ((qqq ())) m0 ())
;      BadIndex)
;     ((primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ())
;      ((vector-set! (vector qqq) 0 5) ((qqq (1))) m1 ()))
;     ((primop-set (+ hole 1) (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ())
;      ((+ (vector-set! (vector qqq) 0 5) 1) ((qqq (1))) m1 ()))
;     ((primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 nil ((qqq (1))) m1 ())
;      (BE m0 Int m1 nil))
;     ((primop-set hole 1 2 3 () m0 ())
;      (TE 1 "vector?"))
;    )
;  )
;
;  (test-case "load-expression"
;    (check-mf-apply*
;     ((load-expression m0 () () (+ 2 2))
;      ((+ 2 2) () m0 ()))
;     ((load-expression m1 ((qqq (1))) ((x 3)) (+ 2 2))
;      ((+ 2 2) ((qqq (1))) m1 ()))
;     ((load-expression m1 ((qqq (1))) ((x 3)) (+ x 2))
;      ((+ 3 2) ((qqq (1))) m1 ()))
;    )
;  )
;
;  (test-case "unload-answer"
;    (check-mf-apply*
;     ((unload-answer ((vector q) ((q (1))) m0 ()))
;      ((vector q) ((q (1))) m0))
;    )
;
;    (check-exn exn:fail:contract?
;      (λ () (term (unload-answer BadIndex))))
;
;    (check-exn exn:fail:contract?
;      (λ () (term (unload-answer (0 () m0 ((m1 hole Int) ())))))))
;
;  (test-case "step-expression"
;    (check-equal?
;      (apply-reduction-relation step-expression (term ((+ 2 2) () mod ())))
;      '((4 () mod ())))
;  )
;
;  (test-case "eval-value"
;    (check-mf-apply*
;     ((eval-value mod0 () () (+ 2 2))
;      (4 ()))
;     ((eval-value mod0 () () (+ (+ 2 2) (+ 2 2)))
;      (8 ()))
;     ((eval-value mod0 ((q (1))) ((a 7)) (+ 2 2))
;      (4 ((q (1)))))
;     ((eval-value mod0 ((q (1))) ((a 7)) (+ a a))
;      (14 ((q (1)))))
;    )
;  )
;
;  (test-case "eval-program:I"
;    (check-mf-apply*
;     ((eval-program [(module-λ mu (define x 4) (provide x))])
;      (() ((mu ((x 4))))))
;     ((eval-program [(module-τ mt (define x Int 4) (provide x))])
;      (() ((mt ((x 4 Int))))))
;     ((eval-program
;       ((module-λ M
;         (define x (+ 2 2))
;         (provide x))))
;      (() ((M ((x 4))))))
;     ((eval-program
;       ((module-λ M
;         (define x 2)
;         (define y (+ x x))
;         (provide x y))))
;      (() ((M ((x 2) (y 4))))))
;     ((eval-program
;       ((module-λ M
;         (define x (fun a (b) (+ b 1)))
;         (define y (x 4))
;         (provide y))))
;      (() ((M ((y 5))))))
;     ((eval-program
;       ((module-τ M
;         (define fact (→ Nat Nat) (fun fact (n) (ifz n 1 (* n (fact (- n 1))))))
;         (define f0 Nat (fact 0))
;         (define f1 Nat (fact 1))
;         (define f2 Nat (fact 2))
;         (define f3 Nat (fact 3))
;         (define f4 Nat (fact 4))
;         (provide f0 f1 f2 f3 f4))))
;      (() ((M ((f0 1 Nat) (f1 1 Nat) (f2 2 Nat) (f3 6 Nat) (f4 24 Nat))))))
;     ((eval-program
;       ((module-τ M
;         (define v (Vectorof Int) (vector 1 2 (+ 2 1)))
;         (define x Int (vector-ref v 2))
;         (define dontcare Int (vector-set! v 0 0))
;         (define y Int (vector-ref v 0))
;         (provide x y))))
;      (((x_loc (0 2 3))) ((M ((x 3 Int) (y 0 Int))))))
;     ((eval-program
;       ((module-τ M
;         (define second (→ (Listof Int) Int) (fun f (xs) (first (rest xs))))
;         (define v Int (second (cons 1 (cons 2 nil))))
;         (provide v))))
;      (() ((M ((v 2 Int))))))
;    )
;  )
;
;  (test-case "eval-program:TE"
;    (check-exn #rx"TE"
;      (λ () (term
;        (eval-program
;         ((module-τ M
;           (define x Int (+ 1 nil))
;           (provide)))))))
;    (check-exn #rx"TE"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (+ 1 nil))
;           (provide)))))))
;    (check-exn #rx"TE"
;      (λ () (term
;        (eval-program
;         ((module-τ M
;           (define x Int (first 4))
;           (provide)))))))
;    (check-exn #rx"TE"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (vector-ref 4 4))
;           (provide)))))))
;    (check-exn #rx"TE"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (4 4))
;           (provide)))))))
;  )
;
;  (test-case "eval-program:ValueError"
;    (check-exn #rx"DivisionByZero"
;      (λ () (term
;        (eval-program
;         ((module-τ M
;           (define x Int (% 1 0))
;           (provide)))))))
;    (check-exn #rx"DivisionByZero"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (% 1 0))
;           (provide)))))))
;    (check-exn #rx"EmptyList"
;      (λ () (term
;        (eval-program
;         ((module-τ M
;           (define x Int (first nil))
;           (provide)))))))
;    (check-exn #rx"EmptyList"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (rest nil))
;           (provide)))))))
;    (check-exn #rx"BadIndex"
;      (λ () (term
;        (eval-program
;         ((module-τ M
;           (define x Int (vector-ref (vector 1) 999))
;           (provide)))))))
;    (check-exn #rx"BadIndex"
;      (λ () (term
;        (eval-program
;         ((module-λ M
;           (define x (vector-set! (vector 0) 4 5))
;           (provide))))))))
;
;  (test-case "eval-program:BE"
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-τ M0
;           (define v (Vectorof Int) (vector 0))
;           (provide v))
;          (module-λ M1
;           (require M0 v)
;           (define x (vector-set! v 0 nil))
;           (provide)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-λ M0
;           (define v (vector -1))
;           (provide v))
;          (module-τ M1
;           (require M0 (v (Vectorof Nat)))
;           (define x Nat (vector-ref v 0))
;           (provide)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-λ M0
;           (define v -1)
;           (provide v))
;          (module-τ M1
;           (require M0 (v Nat))
;           (define x Int 42)
;           (provide)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-τ M0
;           (define f (→ Nat Nat) (fun f (x) (+ x 2)))
;           (provide f))
;          (module-λ M1
;           (require M0 f)
;           (define x (f -1))
;           (provide)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-λ M0
;           (define f (fun f (x) nil))
;           (provide f))
;          (module-τ M1
;           (require M0 (f (→ Int Int)))
;           (define x Int (f 3))
;           (provide)))))))
;  )
;
;  (test-case "eval-program:bad-ann"
;    (check-exn #rx"BE"
;      (λ () (term (eval-program
;        ((module-λ M0
;          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
;          (provide f))
;         (module-τ M1
;          (require M0 (f (→ Int (→ Int Int))))
;          (define f2 (→ Int Int) (f 2))
;          (define f23 Int (f2 3))
;          (provide f23)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term (eval-program
;        ((module-λ M0
;          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
;          (provide f))
;         (module-τ M1
;          (require M0 (f (→ Int (→ Int Int))))
;          (provide f))
;         (module-λ M2
;          (require M1 f)
;          (define f2 (f 2))
;          (define f23 (f2 3))
;          (provide)))))))
;
;    (check-exn #rx"TE"
;      (λ () (term (eval-program
;        ((module-λ M0
;          (define f (fun a (x) (vector-ref x 0)))
;          (provide f))
;         (module-τ M1
;          (require M0 (f (→ Nat Nat)))
;          (define v Nat (f 4))
;          (provide)))))))
;  )
;
;  (test-case "no-mon-between-typed"
;    ;; If typed code imports a typed function,
;    ;;  only do a subtyping check.
;    ;; Do not monitor the typed function in typed code.
;    ;; (Safe assuming type checker is correct)
;
;    (check-mf-apply* #:is-equal? (λ (VAL-ENV M+x:v)
;                                   (define M (car M+x:v))
;                                   (define x:v (cadr M+x:v))
;                                   (define x (car x:v))
;                                   (define ρ (cadr (term #{program-env-ref ,(cadr VAL-ENV) ,M})))
;                                   (define actual (term #{runtime-env-ref ,ρ ,x}))
;                                   (equal? actual x:v))
;      ((eval-program
;        ((module-τ M0
;          (define f (→ Nat Nat) (fun a (b) b))
;          (provide f))
;         (module-τ M1
;          (require M0 (f (→ Nat Nat)))
;          (define v Nil (f nil))
;          (provide v))))
;       (M1 (v nil Nil)))))
;
;  (test-case "deep-typecheck"
;    ;; Typed modules "deeply check" untyped imports
;    ;;  ... to keep type soundness
;
;    (check-exn #rx"BE"
;      (λ () (term (eval-program
;        ((module-λ M0
;          (define nats (cons 1 (cons 2 (cons -3 nil))))
;          (provide nats))
;         (module-τ M1
;          (require M0 (nats (Listof Nat)))
;          (provide)))))))
;  )
;
;  (test-case "eval-untyped-define*"
;    (check-mf-apply*
;     ((eval-untyped-define* m0 () () ((define x 1) (define y 2) (define z 3)))
;      (() ((z 3) (y 2) (x 1))))
;    )
;  )
;
;  (test-case "eval-typed-define*"
;    (check-mf-apply*
;     ((eval-typed-define* m0 () () ((define x Nat 1) (define y Nat 2) (define z Int 3)))
;      (() ((z 3 Int) (y 2 Nat) (x 1 Nat))))
;    )
;  )
;
;  (test-case "type-soundness"
;    (check-mf-apply*
;     ((theorem:type-soundness M (M) () () () (+ 2 2) Nat)
;      4)
;     ((theorem:type-soundness M (M) () ((x Nat)) ((x 42)) (+ x 2) Nat)
;      44)
;     ((theorem:type-soundness M (M) () ((fact (→ Int Int))) ((fact (fun f (→ Int Int) (n) (ifz n 1 (* n (f (- n 1))))))) (fact 5) Int)
;      120)
;    )
;
;    (check-exn exn:fail:contract?
;      (λ () (term (theorem:type-soundness M (M) () ((x Nat)) ((x -4)) (+ x 1) Nat))))
;
;    (check-exn exn:fail:contract?
;      (λ () (term (theorem:type-soundness M (M) () () () (- 4 3) Nat))))
;
;    (check-exn exn:fail:contract?
;      (λ () (term (theorem:type-soundness M () () () () (+ 1 1) Int))))
;  )
;
;
;)
;
;#;(
;  (test-case "well-typed-state"
;
;    (check-judgment-holds*
;     (well-typed-state (2 () M ()) Int (M))
;     (well-typed-state ((fun f (x) x) () M ()) (→ Nat Nat) (M))
;     (well-typed-state ((vector x) ((x (1 2 3))) M ()) (Vectorof Nat) (M))
;
;     (well-typed-state
;       ((vector 2) () Mt
;        ((Mu (+ 1 hole) (Vectorof Int)) ((Mt hole Nat) ())))
;       Nat (Mt))
;
;     (well-typed-state
;       ((+ 2 nil) () Mu
;        ((Mt (+ 1 hole) Int) ()))
;       Int (Mt))
;    )
;  )
;
;  (test-case "runtime-env-models"
;    (check-judgment-holds*
;     (runtime-env-models () () ())
;     (runtime-env-models ((x 4)) ((x Nat)) ())
;     (runtime-env-models ((x (cons 1 nil))) ((x (Listof Int))) ())
;     (runtime-env-models ((x 2) (y (fun f (x) (+ x x)))) ((x Int) (y (→ Int Int))) ())
;    )
;
;    (check-not-judgment-holds*
;     (runtime-env-models () ((x Int)) ())
;     (runtime-env-models ((x 2)) () ())
;     (runtime-env-models ((x 2)) ((x (Listof Int))) ())
;     (runtime-env-models ((x (fun f (x) 3))) ((x Nat)) ())
;    )
;  )
;)
