#lang mf-apply racket/base

;; Tagged Racket semantics,

;; TODO diff from eval-untyped
;; - tag-check on require
;; - tag-check where checks appear (assumes rewritten program)

(provide
  single-step

  require->local-value-env
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
   (eval-module* () () (MODULE ...) σ VAL-ENV_N)
   (where VAL-ENV ,(reverse (term VAL-ENV_N)))
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
   ---
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
   (where ρ_expected #{import/tagged Γ_expected ρ_actual})
   (where ρ_rest #{require->local-value-env VAL-ENV (TYPED-REQUIRE_rest ...)})]
  [(require->local-value-env VAL-ENV (UNTYPED-REQUIRE_0 UNTYPED-REQUIRE_rest ...))
   #{local-value-env-append ρ_expected ρ_rest}
   (where (require M x ...) UNTYPED-REQUIRE_0)
   (where (M ρ_actual) #{toplevel-value-env-ref VAL-ENV M})
   (where ρ_expected #{import/untyped (x ...) ρ_actual})
   (where ρ_rest #{require->local-value-env VAL-ENV (UNTYPED-REQUIRE_rest ...)})])

(define-metafunction μTR
  import/tagged : Γ ρ -> ρ
  [(import/tagged () ρ)
   ()]
  [(import/tagged ((x τ) x:τ_rest ...) ρ)
   #{local-value-env-set ρ_rest x v}
   (where (_ v) #{local-value-env-ref ρ x})
   (where κ #{type->tag τ})
   (where _ #{check-value/fail v κ})
   (where ρ_rest #{import/tagged (x:τ_rest ...) ρ})])

;; Usually call `apply-monitor`, but skip the boundary for typed functions and vectors
(define-metafunction μTR
  check-value/fail : v κ -> v
  [(check-value/fail v κ)
   v
   (judgment-holds (well-tagged-value v κ))]
  [(check-value/fail v κ)
   ,(raise-argument-error 'check-value "BE ill-tagged value"
     "value" (term v)
     "tag" (term κ))])

(define-metafunction μTR
  check-value : v κ -> any
  [(check-value v κ)
   v
   (judgment-holds (well-tagged-value v κ))]
  [(check-value v κ)
   (BE κ v)])

(define-metafunction μTR
  import/untyped : x* ρ -> ρ
  [(import/untyped () ρ)
   ()]
  [(import/untyped (x x_rest ...) ρ)
   #{local-value-env-set ρ_rest x v}
   (where (_ v) #{local-value-env-ref ρ x})
   ;; No need to protect-value
   (where ρ_rest #{import/untyped (x_rest ...) ρ})])

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
     (L σ (in-hole E (tag? κ v)))
     A_next
     E-Tag
     (where A_next #{do-tag L σ E v κ})]

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
     A_next
     E-IfzT
     (judgment-holds (typed-context E L))
     (where A_next #{do-ifz/typed L σ E v e_0 e_1})]
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
  do-tag : L σ E v κ -> A
  [(do-tag L σ E v κ)
   #{make-answer L σ E #{check-value v κ}}])

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
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))])

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
   (where (_ v*) #{store-ref σ loc})])

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
   (where any_set #{term-set v* v_1 v_2})])

;; =============================================================================
;
;(module+ test
;  (require rackunit)
;
;  (test-case "tag-check"
;    (check-judgment-holds*
;     (tag-check 4 Int)
;     (tag-check nil (Listof (Vectorof Int)))
;     (tag-check (cons 1 (cons 2 (cons 3 nil))) (Listof Int))
;     (tag-check (vector x) (Vectorof Nat))
;     (tag-check (cons (vector x) (cons (vector y) nil)) (Listof (Vectorof Int)))
;     (tag-check (fun f (x) (+ x x)) (→ Int Int))
;    )
;
;    (check-not-judgment-holds*
;     (tag-check 4 (Listof Int))
;    )
;  )
;
;  (test-case "runtime-env->untyped-runtime-env"
;    (check-mf-apply*
;     ((runtime-env->untyped-runtime-env m0 ())
;      ())
;     ((runtime-env->untyped-runtime-env m0 ((x 0) (y 1) (z (vector qq))))
;      ((x 0) (y 1) (z (vector qq))))
;     ((runtime-env->untyped-runtime-env m0 ((x 0 Nat) (z (vector q) (Vectorof Int))))
;      ((x 0) (z (vector q))))
;    )
;  )
;
;  (test-case "runtime-env->typed-runtime-env"
;    (check-mf-apply*
;     ((runtime-env->typed-runtime-env m0 ((x 4) (y 1) (z (vector q))) (Nat Int (Vectorof Int)))
;      ((x 4 Nat) (y 1 Int) (z (vector q) (Vectorof Int))))
;     ((runtime-env->typed-runtime-env m0 ((x 4) (z (vector q))) (Nat (Vectorof Int)))
;      ((x 4 Nat) (z (vector q) (Vectorof Int))))
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
;      ((num 4) (f (fun g (x) x))))
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
;      ((num 4 Int) (f (fun g (x) x) (→ (Vectorof Int) (Vectorof Int)))))
;     ((eval-typed-require* ((m0 ((num 4))) (m1 ((f (fun g (x) x) (→ Int Int))))) ((require m0 (num Int)) (require m1 (f (→ Int Int)))))
;      ((num 4 Int) (f (fun g (x) x) (→ Int Int))))
;    )
;
;    (check-exn exn:fail:contract?
;      (λ () (term (eval-typed-require* ((m0 ((num 4)))) ((require m0 (num (Vectorof Int))))))))
;  )
;
;  (test-case "do-call"
;    (check-mf-apply*
;     ((do-call hole (fun f (x) x) 42 () m0 ())
;      (42 () m0 ()))
;    )
;  )
;
;  (test-case "primop-arith"
;    (check-mf-apply*
;     ((primop-arith + hole 2 2 () m0 ())
;      (4 () m0 ()))
;     ((primop-arith - hole 3 2 () m0 ())
;      (1 () m0 ()))
;     ((primop-arith * hole 3 3 () m0 ())
;      (9 () m0 ()))
;     ((primop-arith % hole 12 4 () m0 ())
;      (3 () m0 ()))
;     ((primop-arith % hole 5 2 () m0 ())
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
;      BadIndex))
;
;    (check-exn exn:fail:redex?
;      (λ () (term (primop-ref hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 ((qqq (1 2 3))) m1 ()))))
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
;     ((primop-set hole 1 2 3 () m0 ())
;      (TE 1 "vector?"))
;    )
;
;    (check-exn exn:fail:redex?
;      (λ () (term (primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ()))))
;
;    (check-exn exn:fail:redex?
;      (λ () (term (primop-set (+ hole 1) (mon-vector m0 (Vectorof Int) (vector qqq)) 0 5 ((qqq (1))) m1 ()))))
;
;    (check-exn exn:fail:redex?
;      (λ () (term (primop-set hole (mon-vector m0 (Vectorof Int) (vector qqq)) 0 nil ((qqq (1))) m1 ()))))
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
;    (check-mf-apply*
;     ((eval-program
;       ((module-τ M0
;         (define v (Vectorof Int) (vector 0))
;         (provide v))
;        (module-λ M1
;         (require M0 v)
;         (define x (vector-set! v 0 nil))
;         (provide))))
;      (((x_loc (nil))) ((M1 ()) (M0 ((v (vector x_loc) (Vectorof Int)))))))
;    )
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
;         ((module-λ M0
;           (define v (vector -1))
;           (provide v))
;          (module-τ M1
;           (require M0 (v (Vectorof Nat)))
;           (define x Nat (!! [y Nat (vector-ref v 0)] y))
;           (provide)))))))
;
;    (check-exn #rx"BE"
;      (λ () (term
;        (eval-program
;         ((module-τ M0
;           (define f (→ Nat Nat) (fun f (x) (!! [x Nat x] (+ x 2))))
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
;           (define x Int (!! [a Int (f 3)] a))
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
;          (define f23 Int (!! [z Int (f2 3)] z))
;          (provide f23)))))))
;
;    (check-not-exn
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
;)
;
