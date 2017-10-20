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
  [(check-value v_fun τ)
   v_fun
   (where (fun _ τ_fun (_) _) v_fun)
   (side-condition
     (unless (judgment-holds (<: τ_fun τ))
       (raise-arguments-error 'check-value "BE: cannot import typed value at incompatible type"
         "value" (term v_fun)
         "actual type" (term τ_fun)
         "import type" (term τ))))]
  [(check-value v_vec τ)
   v_vec
   (where (vector τ_vec _) v_vec)
   (side-condition
     (unless (judgment-holds (<: τ_vec τ))
       (raise-arguments-error 'check-value "BE: cannot import typed value at incompatible type"
         "value" (term v_vec)
         "actual type" (term τ_vec)
         "import type" (term τ))))]
  [(check-value v τ)
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
   (x:v_0 x:v_rest ...)
   (where x:v_0 #{local-value-env-ref ρ x_0})
   (where (x:v_rest ...) #{local-value-env->provided ρ (provide x_rest ...)})])

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

(define-metafunction μTR
  eval-expression# : σ ρ L e -> [σ v]
  [(eval-expression# σ ρ L e)
   (σ_+ v_+)
   (judgment-holds (eval-expression σ ρ L e σ_+ v_+))]
  [(eval-expression# σ ρ L e)
   ,(raise-arguments-error 'eval-expression "undefined for arguments"
     "store" (term σ)
     "local-value-env" (term ρ)
     "context" (term L)
     "expression" (term e))])

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
     E-MakeVectorU
     (fresh loc)
     (where σ_+ #{store-set σ loc (v ...)})]
   [-->
     (L σ (in-hole E (vector τ v ...)))
     (L σ_+ (in-hole E (vector τ loc)))
     E-MakeVectorT
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
  [(do-apply L σ E Λ v_arg _)
   (L σ (in-hole E e_body+))
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply L σ E Λ v_arg _)
   (L σ (in-hole E e_body+))
   (where (fun x_f _ (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply L σ E (mon-fun τ v_f) v_arg L_hole)
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
  [(do-ref/untyped _ _ _ _ v)
   (TE v "integer?")
   (judgment-holds (not-integer-value v))]
  [(do-ref/untyped L σ E v_0 v_1)
   #{do-ref L σ E v_0 v_1 L_hole}
   (where L_hole UN)])

(define-metafunction μTR
  do-ref : L σ E v v L -> A
  [(do-ref L σ E (vector loc) integer_index _)
   #{make-answer L σ E #{term-ref v* integer_index}}
   (where (_ v*) #{store-ref σ loc})]
  [(do-ref L σ E (vector _ loc) integer_index _)
   #{make-answer L σ E #{term-ref v* integer_index}}
   (where (_ v*) #{store-ref σ loc})]
  [(do-ref L σ E (mon-vector τ v_0) v_1 L_hole)
   (L σ e_+)
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (where e_+
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
   #{do-set L σ E v_0 v_1 v_2}])

(define-metafunction μTR
  do-set/untyped : L σ E v v v -> A
  [(do-set/untyped _ _ _ v _ _)
   (TE v "vector?")
   (judgment-holds (not-vector-value v))]
  [(do-set/untyped _ _ _ _ v _)
   (TE v "integer?")
   (judgment-holds (not-integer-value v))]
  [(do-set/untyped L σ E v_0 v_1 v_2)
   #{do-set L σ E v_0 v_1 v_2}])

(define-metafunction μTR
  do-set : L σ E v v v -> A
  [(do-set L σ E (vector loc) v_1 v_2)
   ,(if (redex-match? μTR Error (term any_set))
      (term any_set)
      (term (L #{store-update σ loc any_set} (in-hole E v_2))))
   (where (_ v*) #{store-ref σ loc})
   (where any_set #{term-set v* v_1 v_2})]
  [(do-set L σ E (vector _ loc) v_1 v_2)
   ,(if (redex-match? μTR Error (term any_set))
      (term any_set)
      (term (L #{store-update σ loc any_set} (in-hole E v_2))))
   (where (_ v*) #{store-ref σ loc})
   (where any_set #{term-set v* v_1 v_2})]
  [(do-set L σ E (mon-vector τ v_0) v_1 v_2)
   #{make-answer L σ E_+ #{apply-monitor# v_2 τ_elem}}
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (where E_+ (in-hole E (vector-set! v_0 v_1 hole)))])

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
  [(do-arith/untyped BINOP L σ E v_0 v_1)
   #{do-arith BINOP L σ E v_0 v_1}])

(define-metafunction μTR
  do-arith/typed : BINOP L σ E v v -> A
  [(do-arith/typed BINOP L σ E v_0 v_1)
   #{do-arith BINOP L σ E v_0 v_1}])

(define-metafunction μTR
  do-arith : BINOP L σ E v v -> A
  [(do-arith + L σ E integer_0 integer_1)
   (L σ (in-hole E ,(+ (term integer_0) (term integer_1))))]
  [(do-arith - L σ E integer_0 integer_1)
   (L σ (in-hole E ,(- (term integer_0) (term integer_1))))]
  [(do-arith * L σ E integer_0 integer_1)
   (L σ (in-hole E ,(* (term integer_0) (term integer_1))))]
  [(do-arith % L σ E integer_0 integer_1)
   DivisionByZero
   (side-condition (zero? (term integer_1)))]
  [(do-arith % L σ E integer_0 integer_1)
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
  load-expression : L σ ρ e -> Σ
  [(load-expression L σ ρ e)
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
   (where (σ v) #{unload-answer A})
   (where e_sub #{unload-store v σ})])

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
   ,(raise-arguments-error 'apply-monitor "BE ill-typed value" "value" (term v) "type" (term τ))])

(define-metafunction μTR
  apply-monitor# : v τ -> any
  [(apply-monitor# v τ)
   v_mon
   (judgment-holds (apply-monitor v τ v_mon))]
  [(apply-monitor# v τ)
   (BE τ v)])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "apply-monitor"
    (check-mf-apply*
     [(apply-monitor# 4 Int)
      4]
     [(apply-monitor# nil (Listof (Vectorof Int)))
      nil]
     [(apply-monitor# (cons 1 (cons 2 (cons 3 nil))) (Listof Int))
      (cons 1 (cons 2 (cons 3 nil)))]
     [(apply-monitor# (vector x) (Vectorof Nat))
      (mon-vector (Vectorof Nat) (vector x))]
     [(apply-monitor# (vector (Vectorof Nat) x) (Vectorof Nat))
      (mon-vector (Vectorof Nat) (vector (Vectorof Nat) x))]
     [(apply-monitor# (cons (vector (Vectorof Int) x) (cons (vector y) nil)) (Listof (Vectorof Int)))
      (cons (mon-vector (Vectorof Int) (vector (Vectorof Int) x))
            (cons (mon-vector (Vectorof Int) (vector y)) nil))]
     [(apply-monitor# (fun f (x) (+ x x)) (→ Int Int))
      (mon-fun (→ Int Int) (fun f (x) (+ x x)))]
     [(apply-monitor# (fun f (→ Int Int) (x) (+ x x)) (→ Int Int))
      (mon-fun (→ Int Int) (fun f (→ Int Int) (x) (+ x x)))]
    )

   (check-exn exn:fail:contract?
     (λ () (term (apply-monitor#/fail 4 (Listof Int)))))
  )

  (test-case "local-value-env->provided"
    (check-mf-apply*
     ((local-value-env->provided () (provide))
      ())
     ((local-value-env->provided ((x 66)) (provide x))
      ((x 66)))
     ((local-value-env->provided ((x 1) (y -3)) (provide x y))
      ((x 1) (y -3)))
     ((local-value-env->provided ((x 2) (y -88)) (provide x))
      ((x 2)))
     ((local-value-env->provided ((x 6) (y 5)) (provide y))
      ((y 5))))
  )

  (test-case "protect-value"
    (check-mf-apply*
     ((protect-value 4)
      4)
     ((protect-value (fun f (x) 4))
      (fun f (x) 4))
     ((protect-value (vector asd))
      (vector asd))
     ((protect-value (vector (Vectorof Int) asd))
      (mon-vector (Vectorof Int) (vector (Vectorof Int) asd)))
     ((protect-value (fun f (→ Nat Nat) (x) (+ x 4)))
      (mon-fun (→ Nat Nat) (fun f (→ Nat Nat) (x) (+ x 4))))
    )
  )

  (test-case "check-value"
    (check-mf-apply*
     ((check-value 4 Int)
      4)
     ((check-value (vector q) (Vectorof Int))
      (mon-vector (Vectorof Int) (vector q)))
     ((check-value (fun f (x) x) (→ (Vectorof Int) (Vectorof Int)))
      (mon-fun (→ (Vectorof Int) (Vectorof Int)) (fun f (x) x)))
     ((check-value (fun f (→ (Vectorof Int) (Vectorof Int)) (x) x) (→ (Vectorof Int) (Vectorof Int)))
      (fun f (→ (Vectorof Int) (Vectorof Int)) (x) x))
     ((check-value (vector (Vectorof Int) aaa) (Vectorof Int))
      (vector (Vectorof Int) aaa)))

    (check-exn exn:fail:contract? ;; import at wrong type
      (λ () (term #{check-value (vector (Vectorof Int) asdf) (Vectorof Nat)})))
    (check-exn exn:fail:contract? ;; import at wrong type
      (λ () (term #{check-value (vector (Vectorof Nat) asdf) (Vectorof Int)})))
    (check-exn exn:fail:contract?
      (λ () (term #{check-value 4 (Listof Int)})))
  )

  (test-case "import/untyped"
    (check-mf-apply*
     ((import/untyped (a b c) ((a 1) (b 2) (c 3) (d 4)))
      ((a 1) (b 2) (c 3)))
    )
  )

  (test-case "import/typed"
    (check-mf-apply*
     ((import/typed ((a Int) (b Int) (c Int)) ((a 1) (b 2) (c 3) (d 4)))
      ((a 1) (b 2) (c 3)))
    )
  )

  (test-case "require->local-value-env"
    (check-mf-apply*
     ((require->local-value-env () ())
      ())
     ((require->local-value-env ((M0 ((n 4)))) ((require M0 n)))
      ((n 4)))
     ((require->local-value-env ((m0 ((num 4) (y 5)))) ((require m0 num)))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 num)))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 num) (require m1 f)))
      ((num 4) (f (fun g (x) x))))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 num) (require m1 f)))
      ((num 4) (f (fun g (x) x))))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (→ Int Int) (x) x)))))
                                ((require m0 num) (require m1 f)))
      ((num 4) (f (mon-fun (→ Int Int) (fun g (→ Int Int) (x) x)))))
     ((require->local-value-env ((m0 ((num 4)))) ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4) (y 5)))) ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 ((num Int))) (require m1 ((f (→ (Vectorof Int) (Vectorof Int)))))))
      ((num 4) (f (mon-fun (→ (Vectorof Int) (Vectorof Int)) (fun g (x) x)))))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (→ Int Int) (x) x)))))
                                ((require m0 ((num Int))) (require m1 ((f (→ Int Int))))))
      ((num 4) (f (fun g (→ Int Int) (x) x))))
    )

    (check-exn exn:fail:contract?
      (λ () (term (require->local-value-env () ((require m x))))))

    (check-exn exn:fail:contract?
      (λ () (term (require->local-value-env ((m0 ((num 4)))) ((require m0 ((num (Vectorof Int)))))))))
  )

  (test-case "make-answer"
    (check-mf-apply*
     ((make-answer UN () hole 2)
      (UN () 2))
     ((make-answer TY () hole (TE 2 "pair?"))
      (TE 2 "pair?"))))

  (test-case "do-check"
    (check-mf-apply*
     ((do-check TY () hole 3 Int)
      (TY () 3))
     ((do-check TY () hole 3 (Vectorof Int))
      (BE (Vectorof Int) 3))
     ((do-check TY ((qq (0))) hole (vector qq) (Vectorof Nat))
      (TY ((qq (0))) (mon-vector (Vectorof Nat) (vector qq))))))

  (test-case "do-protect"
    (check-mf-apply*
     ((do-protect TY () hole 3 Int)
      (TY () 3))
     ((do-protect TY () hole 3 (Vectorof Int))
      (BE (Vectorof Int) 3))
     ((do-protect TY ((qq (0))) hole (vector qq) (Vectorof Nat))
      (TY ((qq (0))) (mon-vector (Vectorof Nat) (vector qq))))))

  (test-case "do-return"
    (check-mf-apply*
     ((do-return UN () hole 4 Int)
      (UN () 4))
     ((do-return TY () hole 4 (Vectorof Int))
      (BE (Vectorof Int) 4))
     ((do-return UN () hole (fun f (x) x) (→ Nat Nat))
      (UN () (mon-fun (→ Nat Nat) (fun f (x) x))))))

  (test-case "do-apply/typed"
    (check-mf-apply*
     ((do-apply/untyped UN () hole 4 5)
      (TE 4 "procedure?"))
     ((do-apply/untyped TY () (check Int hole) (fun f (x) (+ x x)) 5)
      (TY () (check Int (+ 5 5))))
    )
  )

  (test-case "do-apply/untyped"
    (check-mf-apply*
     ((do-apply/typed TY ((a (1))) hole (fun f (x) (+ x x)) 5)
      (TY ((a (1))) (+ 5 5)))
     ((do-apply/typed TY () hole (mon-fun (→ Nat Nat) (fun f (x) (+ x x))) 5)
      (TY () (check Nat ((fun f (x) (+ x x)) 5))))
    )
  )

  (test-case "do-apply"
    (check-mf-apply*
     ((do-apply UN () hole (fun f (x) (+ x x)) 5 UN)
      (UN () (+ 5 5)))
    )
  )

  (test-case "do-ref/typed"
    (check-mf-apply*
     ((do-ref/typed TY ((qq (1 2))) hole (vector qq) 0)
      (TY ((qq (1 2))) 1))
     ((do-ref/typed TY ((qq (1 2))) hole (vector (Vectorof Int) qq) 1)
      (TY ((qq (1 2))) 2))
     ((do-ref/typed TY ((qq ())) hole (vector qq) 3)
      BadIndex)
    )
  )

  (test-case "do-ref/untyped"
    (check-mf-apply*
     ((do-ref/untyped UN ((qq (1 2))) hole (vector qq) 0)
      (UN ((qq (1 2))) 1))
     ((do-ref/untyped UN () hole 4 5)
      (TE 4 "vector?"))
    )
  )

  (test-case "do-ref"
    (check-mf-apply*
     ((do-ref TY ((qq (2))) hole (vector qq) 0 UN)
      (TY ((qq (2))) 2))
     ((do-ref TY ((qq (2))) hole (mon-vector (Vectorof Nat) (vector qq)) 0 UN)
      (TY ((qq (2))) (protect Nat (vector-ref (vector qq) 0))))
     ((do-ref TY ((qq (2))) hole (mon-vector (Vectorof Nat) (vector qq)) 0 TY)
      (TY ((qq (2))) (check Nat (vector-ref (vector qq) 0))))
    )
  )

  (test-case "do-set/typed"
    (check-mf-apply*
     ((do-set/typed TY ((qq (1 2))) hole (vector (Vectorof Nat) qq) 0 2)
      (TY ((qq (2 2))) 2))
     ((do-set/typed TY ((qq (1 2))) hole (mon-vector (Vectorof Nat) (vector qq)) 0 2)
      (TY ((qq (1 2))) (vector-set! (vector qq) 0 2)))
     ((do-set/typed TY ((x ()) (qq ((vector z))) (z (1))) hole (mon-vector (Vectorof (Vectorof Nat)) (vector qq)) 0 (vector x))
      (TY ((x ()) (qq ((vector z))) (z (1))) (vector-set! (vector qq) 0 (mon-vector (Vectorof Nat) (vector x)))))
    )
  )

  (test-case "do-set/untyped"
    (check-mf-apply*
     ((do-set/untyped UN () hole 4 5 6)
      (TE 4 "vector?"))
     ((do-set/untyped UN ((qq (0))) hole (vector qq) (vector qq) 6)
      (TE (vector qq) "integer?"))
     ((do-set/untyped UN ((qq (0 0))) hole (vector qq) 0 1)
      (UN ((qq (1 0))) 1))
    )
  )

  (test-case "do-set"
    (check-mf-apply*
     ((do-set UN ((qq (5))) hole (vector qq) 0 1)
      (UN ((qq (1))) 1))
     ((do-set TY ((qq (5))) hole (vector (Vectorof Int) qq) 0 1)
      (TY ((qq (1))) 1))
     ((do-set TY ((qq (5))) hole (mon-vector (Vectorof Int) (vector qq)) 0 (fun f (x) 1))
      (BE Int (fun f (x) 1)))
     ((do-set TY ((qq ((fun f (x) 0)))) hole (mon-vector (Vectorof (→ Nat Nat)) (vector qq)) 0 (fun f (x) 1))
      (TY ((qq ((fun f (x) 0)))) (vector-set! (vector qq) 0 (mon-fun (→ Nat Nat) (fun f (x) 1)))))
    )
  )

  (test-case "do-ifz/untyped"
    (check-mf-apply*
     ((do-ifz/untyped UN () hole 1 2 3)
      (UN () 3))
     ((do-ifz/untyped UN () hole 0 1 2)
      (UN () 1))))

  (test-case "do-arith/untyped"
    (check-mf-apply*
     ((do-arith/untyped + UN () hole nil 0)
      (TE nil "integer?"))
     ((do-arith/untyped + UN () hole 0 nil)
      (TE nil "integer?"))
     ((do-arith/untyped + UN () hole 3 2)
      (UN () 5))
    )
  )

  (test-case "do-arith/typed"
    (check-mf-apply*
     ((do-arith/typed * TY () hole 7 6)
      (TY () 42))))

  (test-case "do-arith"
    (check-mf-apply*
     ((do-arith + UN () hole 3 3)
      (UN () 6))
     ((do-arith - UN () hole 1 3)
      (UN () -2))
     ((do-arith * UN () hole 3 3)
      (UN () 9))
     ((do-arith % UN () hole 6 3)
      (UN () 2))
     ((do-arith % UN () hole 1 3)
      (UN () 0))
     ((do-arith % UN () hole 1 0)
      DivisionByZero)))

  (test-case "do-first/untyped"
    (check-mf-apply*
     ((do-first/untyped UN () hole 3)
      (TE 3 "pair?"))
     ((do-first/untyped UN () hole (cons 3 nil))
      (UN () 3))))

  (test-case "do-first/typed"
    (check-mf-apply*
     ((do-first/typed TY () hole (cons 3 nil))
      (TY () 3))))

  (test-case "do-first"
    (check-mf-apply*
     ((do-first UN () hole nil)
      EmptyList)
     ((do-first UN () hole (cons 2 nil))
      (UN () 2))
     ((do-first UN () hole (cons 2 (cons 3 nil)))
      (UN () 2))))

  (test-case "do-rest/untyped"
    (check-mf-apply*
     ((do-rest/untyped UN () hole 3)
      (TE 3 "pair?"))
     ((do-rest/untyped UN () hole (cons 3 nil))
      (UN () nil))))

  (test-case "do-rest/typed"
    (check-mf-apply*
     ((do-rest/typed TY () hole (cons 3 nil))
      (TY () nil))))

  (test-case "do-rest"
    (check-mf-apply*
     ((do-rest UN () hole nil)
      EmptyList)
     ((do-rest UN () hole (cons 2 nil))
      (UN () nil))
     ((do-rest UN () hole (cons 2 (cons 3 nil)))
      (UN () (cons 3 nil)))))

  (test-case "load-expression"
    (check-mf-apply*
     ((load-expression UN () () (+ 2 2))
      (UN () (+ 2 2)))
     ((load-expression TY ((q (0))) () (+ 2 2))
      (TY ((q (0))) (+ 2 2)))
     ((load-expression UN ((q (0))) ((a 4) (b (vector (Vectorof Integer) q))) (+ a b))
      (UN ((q (0))) (+ 4 (vector (Vectorof Integer) q))))))

  (test-case "unload-answer"
    (check-mf-apply*
     ((unload-answer (UN () 3))
      (() 3)))

    (check-exn exn:fail:contract?
      (λ () (term (unload-answer BadIndex)))))

  (test-case "unload-answer/store"
    (check-mf-apply*
     ((unload-answer/store (UN () 3))
      3)
     ((unload-answer/store (UN ((q (0))) 3))
      3)
     ((unload-answer/store (UN ((q (0))) (vector q)))
      (vector 0))))

  (test-case "eval-value"
    (check-mf-apply*
     ((eval-expression# () () UN (+ 2 2))
      (() 4))
     ((eval-expression# () () TY (+ (+ 2 2) (+ 2 2)))
      (() 8))
     ((eval-expression# ((q (1))) ((a 7)) UN (+ 2 2))
      (((q (1))) 4))
     ((eval-expression# ((q (1))) ((a 7)) UN (+ a a))
      (((q (1))) 14)))

    (check-exn exn:fail:contract?
      (λ () (term (eval-expression# () () UN (+ nil 2)))))

    (check-exn exn:fail:redex?
      (λ () (term (eval-expression# () () TY (+ nil 2)))))
  )

  (test-case "eval-program:I"
    (check-mf-apply*
     ((eval-program# [(module M UN (define x 4) (provide x))])
      (() ((M ((x 4))))))
     ((eval-program# [(module mt TY (define x Int 4) (provide x))])
      (() ((mt ((x 4))))))
     ((eval-program#
       ((module M UN
         (define x (+ 2 2))
         (provide x))))
      (() ((M ((x 4))))))
     ((eval-program#
       ((module M UN
         (define x 2)
         (define y (+ x x))
         (provide x y))))
      (() ((M ((x 2) (y 4))))))
     ((eval-program#
       ((module M UN
         (define x (fun a (b) (+ b 1)))
         (define y (x 4))
         (provide y))))
      (() ((M ((y 5))))))
     ((eval-program#
       ((module M TY
         (define fact (→ Nat Nat) (fun fact (→ Nat Nat) (n) (ifz n 1 (* n (fact (- n 1))))))
         (define f0 Nat (fact 0))
         (define f1 Nat (fact 1))
         (define f2 Nat (fact 2))
         (define f3 Nat (fact 3))
         (define f4 Nat (fact 4))
         (provide f0 f1 f2 f3 f4))))
      (() ((M ((f0 1) (f1 1) (f2 2) (f3 6) (f4 24))))))
     ((eval-program#
       ((module M TY
         (define v (Vectorof Int) (vector (Vectorof Int) 1 2 (+ 2 1)))
         (define x Int (vector-ref v 2))
         (define dontcare Int (vector-set! v 0 0))
         (define y Int (vector-ref v 0))
         (provide x y))))
      (((loc (0 2 3))) ((M ((x 3) (y 0))))))
     ((eval-program#
       ((module M TY
         (define second (→ (Listof Int) Int) (fun f (→ (Listof Int) Int) (xs) (first (rest xs))))
         (define v Int (second (cons 1 (cons 2 nil))))
         (provide v))))
      (() ((M ((v 2))))))
    )
  )

  (test-case "eval-program:TE"
    (check-exn exn:fail:redex?
      (λ () (term
        (eval-program#
         ((module M TY
           (define x Int (+ 1 nil))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (+ 1 nil))
           (provide)))))))
    (check-exn exn:fail:redex?
      (λ () (term
        (eval-program#
         ((module M TY
           (define x Int (first 4))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (vector-ref 4 4))
           (provide)))))))
    (check-exn #rx"TE"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (4 4))
           (provide)))))))
  )

  (test-case "eval-program:ValueError"
    (check-exn #rx"DivisionByZero"
      (λ () (term
        (eval-program#
         ((module M TY
           (define x Int (% 1 0))
           (provide)))))))
    (check-exn #rx"DivisionByZero"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (% 1 0))
           (provide)))))))
    (check-exn #rx"EmptyList"
      (λ () (term
        (eval-program#
         ((module M TY
           (define x Int (first nil))
           (provide)))))))
    (check-exn #rx"EmptyList"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (rest nil))
           (provide)))))))
    (check-exn #rx"BadIndex"
      (λ () (term
        (eval-program#
         ((module M TY
           (define x Int (vector-ref (vector 1) 999))
           (provide)))))))
    (check-exn #rx"BadIndex"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (vector-set! (vector 0) 4 5))
           (provide))))))))

  (test-case "eval-program:BE"
    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 TY
           (define v (Vectorof Int) (vector (Vectorof Int) 0))
           (provide v))
          (module M1 UN
           (require M0 v)
           (define x (vector-set! v 0 nil))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 UN
           (define v (vector -1))
           (provide v))
          (module M1 TY
           (require M0 ((v (Vectorof Nat))))
           (define x Nat (vector-ref v 0))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 UN
           (define v -1)
           (provide v))
          (module M1 TY
           (require M0 ((v Nat)))
           (define x Int 42)
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 TY
           (define f (→ Nat Nat) (fun f (→ Nat Nat) (x) (+ x 2)))
           (provide f))
          (module M1 UN
           (require M0 f)
           (define x (f -1))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 UN
           (define f (fun f (x) nil))
           (provide f))
          (module M1 TY
           (require M0 ((f (→ Int Int))))
           (define x Int (f 3))
           (provide)))))))
  )

  (test-case "eval-program:bad-ann"
    (check-exn #rx"BE"
      (λ () (term (eval-program#
        ((module M0 UN
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
          (provide f))
         (module M1 TY
          (require M0 ((f (→ Int (→ Int Int)))))
          (define f2 (→ Int Int) (f 2))
          (define f23 Int (f2 3))
          (provide f23)))))))

    (check-exn #rx"BE"
      (λ () (term (eval-program#
        ((module M0 UN
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
          (provide f))
         (module M1 TY
          (require M0 ((f (→ Int (→ Int Int)))))
          (provide f))
         (module M2 UN
          (require M1 f)
          (define f2 (f 2))
          (define f23 (f2 3))
          (provide)))))))

    (check-exn #rx"TE"
      (λ () (term (eval-program#
        ((module M0 UN
          (define f (fun a (x) (vector-ref x 0)))
          (provide f))
         (module M1 TY
          (require M0 ((f (→ Nat Nat))))
          (define v Nat (f 4))
          (provide)))))))
  )

  ;(test-case "no-mon-between-typed"
  ;  ;; If typed code imports a typed function,
  ;  ;;  only do a subtyping check.
  ;  ;; Do not monitor the typed function in typed code.
  ;  ;; (Safe assuming type checker is correct)

  ;  (check-mf-apply* #:is-equal? (λ (VAL-ENV M+x:v)
  ;                                 (define M (car M+x:v))
  ;                                 (define x:v (cadr M+x:v))
  ;                                 (define x (car x:v))
  ;                                 (define ρ (cadr (term #{toplevel-value-env-ref ,(cadr VAL-ENV) ,M})))
  ;                                 (define actual (term #{local-value-env-ref ,ρ ,x}))
  ;                                 (equal? actual x:v))
  ;    ((eval-program#
  ;      ((module M0 TY
  ;        (define f (→ Nat Nat) (fun a (→ Nat Nat) (b) b))
  ;        (provide f))
  ;       (module M1 TY
  ;        (require M0 ((f (→ Nat Nat))))
  ;        (define v Nil (f nil))
  ;        (provide v))))
  ;     (M1 (v nil Nil)))))

  (test-case "deep-typecheck"
    ;; Typed modules "deeply check" untyped imports
    ;;  ... to keep type soundness

    (check-exn #rx"BE"
      (λ () (term (eval-program#
        ((module M0 UN
          (define nats (cons 1 (cons 2 (cons -3 nil))))
          (provide nats))
         (module M1 TY
          (require M0 ((nats (Listof Nat))))
          (provide)))))))
  )

)

