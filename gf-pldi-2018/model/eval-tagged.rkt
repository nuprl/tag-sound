#lang mf-apply racket/base

;; Tagged Racket semantics,

(provide
  eval-program
  untyped-step
  typed-step
  untyped-step#
  typed-step#

  require->local-value-env
  local-value-env->provided
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
;; --- metafunctions for eval-module

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
   (where _ #{tag-check/fail# v κ})
   (where ρ_rest #{import/tagged (x:τ_rest ...) ρ})])

;; Usually call `apply-monitor`, but skip the boundary for typed functions and vectors
(define-metafunction μTR
  tag-check/fail# : v κ -> v
  [(tag-check/fail# v TST)
   v]
  [(tag-check/fail# v κ)
   v
   (judgment-holds (well-tagged-value v κ))]
  [(tag-check/fail# v κ)
   ,(raise-argument-error 'tag-check "BE ill-tagged value"
     "value" (term v)
     "tag" (term κ))])

(define-metafunction μTR
  tag-check# : v κ -> any
  [(tag-check# v TST)
   v]
  [(tag-check# v κ)
   v
   (judgment-holds (well-tagged-value v κ))]
  [(tag-check# v κ)
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
   (eval-untyped-expression σ ρ e σ_+ v_+)
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (eval-define σ ρ UNTYPED-DEFINE σ_+ ρ_+)]
  [
   (where (define x τ e) TYPED-DEFINE)
   (eval-typed-expression σ ρ e σ_+ v_+)
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (eval-define σ ρ TYPED-DEFINE σ_+ ρ_+)])

(define-judgment-form μTR
  #:mode (eval-typed-expression I I I O O)
  #:contract (eval-typed-expression σ ρ e σ v)
  [
   (where Σ_0 #{load-expression σ ρ e})
   (where A ,(typed-step* (term Σ_0)))
   (where (σ_+ v_+) #{unload-answer A})
   ---
   (eval-typed-expression σ ρ e σ_+ v_+)])

(define-judgment-form μTR
  #:mode (eval-untyped-expression I I I O O)
  #:contract (eval-untyped-expression σ ρ e σ v)
  [
   (where Σ_0 #{load-expression σ ρ e})
   (where A ,(untyped-step* (term Σ_0)))
   (where (σ_+ v_+) #{unload-answer A})
   ---
   (eval-untyped-expression σ ρ e σ_+ v_+)])

(define-metafunction μTR
  eval-expression# : σ ρ L e -> [σ v]
  [(eval-expression# σ ρ L e)
   (σ_+ v_+)
   (where L UN)
   (judgment-holds (eval-untyped-expression σ ρ e σ_+ v_+))]
  [(eval-expression# σ ρ L e)
   (σ_+ v_+)
   (where L TY)
   (judgment-holds (eval-typed-expression σ ρ e σ_+ v_+))]
  [(eval-expression# σ ρ L e)
   ,(raise-arguments-error 'eval-expression "undefined for arguments"
     "store" (term σ)
     "local-value-env" (term ρ)
     "context" (term L)
     "expression" (term e))])

;; -----------------------------------------------------------------------------

;; TODO currently no rule for tag?. Need to add one?

(define untyped-step
  (reduction-relation μTR
   #:domain A
   [-->
     (σ (in-hole E (from-typed τ e)))
     A_next
     E-Boundary
     (where A_next #{do-from-typed σ E e τ})]
   [-->
     (σ (in-hole E (v_0 v_1)))
     A_next
     E-Apply
     (where A_next #{do-apply/untyped σ E v_0 v_1})]
   [-->
     (σ (in-hole E (make-vector v ...)))
     (σ_+ (in-hole E (vector loc)))
     E-MakeVector
     (fresh loc)
     (where σ_+ #{store-set σ loc (v ...)})]
   [-->
     (σ (in-hole E (vector-ref v_0 v_1)))
     A_next
     E-Ref
     (where A_next #{do-ref/untyped σ E v_0 v_1})]
   [-->
     (σ (in-hole E (vector-set! v_0 v_1 v_2)))
     A_next
     E-Set
     (where A_next #{do-set/untyped σ E v_0 v_1 v_2})]
   [-->
     (σ (in-hole E (ifz v e_0 e_1)))
     A_next
     E-Ifz
     (where A_next #{do-ifz/untyped σ E v e_0 e_1})]
   [-->
     (σ (in-hole E (BINOP v_0 v_1)))
     A_next
     E-Arith
     (where A_next #{do-arith/untyped BINOP σ E v_0 v_1})]
   [-->
     (σ (in-hole E (first v)))
     A_next
     E-first
     (where A_next #{do-first/untyped σ E v})]
   [-->
     (σ (in-hole E (rest v)))
     A_next
     E-rest
     (where A_next #{do-rest/untyped σ E v})]))

(define typed-step
  (reduction-relation μTR
   #:domain A
   [-->
     (σ (in-hole E (from-untyped τ e)))
     A_next
     E-Boundary
     (where A_next #{do-from-untyped σ E e τ})]
   [-->
     (σ (in-hole E (v_0 v_1)))
     A_next
     E-ApplyT
     (where A_next #{do-apply/typed σ E v_0 v_1})]
   [-->
     (σ (in-hole E (make-vector τ v ...)))
     (σ_+ (in-hole E (vector τ loc)))
     E-MakeVector
     (fresh loc)
     (where σ_+ #{store-set σ loc (v ...)})]
   [-->
     (σ (in-hole E (vector-ref v_0 v_1)))
     A_next
     E-Ref
     (where A_next #{do-ref/typed σ E v_0 v_1})]
   [-->
     (σ (in-hole E (vector-set! v_0 v_1 v_2)))
     A_next
     E-Set
     (where A_next #{do-set/typed σ E v_0 v_1 v_2})]
   [-->
     (σ (in-hole E (ifz v e_0 e_1)))
     A_next
     E-Ifz
     (where A_next #{do-ifz/typed σ E v e_0 e_1})]
   [-->
     (σ (in-hole E (BINOP v_0 v_1)))
     A_next
     E-Arith
     (where A_next #{do-arith/typed BINOP σ E v_0 v_1})]
   [-->
     (σ (in-hole E (first v)))
     A_next
     E-first
     (where A_next #{do-first/typed σ E v})]
   [-->
     (σ (in-hole E (rest v)))
     A_next
     E-rest
     (where A_next #{do-rest/typed σ E v})]))

(define-metafunction μTR
  untyped-step# : Σ -> A
  [(untyped-step# Σ)
   ,(let ([A* (apply-reduction-relation untyped-step (term Σ))])
     (cond
      [(null? A*)
       (term Σ)]
      [(null? (cdr A*))
       (car A*)]
      [else
       (raise-arguments-error 'untyped-step# "non-deterministic reduction"
        "state" (term Σ)
        "answers" A*)]))])

(define-metafunction μTR
  typed-step# : Σ -> A
  [(typed-step# Σ)
   ,(let ([A* (apply-reduction-relation typed-step (term Σ))])
     (cond
      [(null? A*)
       (term Σ)]
      [(null? (cdr A*))
       (car A*)]
      [else
       (raise-arguments-error 'typed-step# "non-deterministic reduction"
        "state" (term Σ)
        "answers" A*)]))])

(define untyped-step*
  (make--->* untyped-step))

(define typed-step*
  (make--->* typed-step))

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  do-from-typed : σ E e τ -> A
  [(do-from-typed σ E v τ)
   #{make-answer σ E #{tag-check/fail# v κ}}
   (where κ #{type->tag τ})]
  [(do-from-typed σ E e τ)
   (σ_+ (in-hole E (from-typed τ e_+)))
   (where (σ_+ e_+) #{typed-step# (σ e)})]
  [(do-from-typed σ E e τ)
   Error
   (where Error #{typed-step# (σ e)})])

(define-metafunction μTR
  do-from-untyped : σ E e τ -> A
  [(do-from-untyped σ E v τ)
   #{make-answer σ E #{tag-check# v κ}}
   (where κ #{type->tag τ})]
  [(do-from-untyped σ E e τ)
   (σ_+ (in-hole E (from-untyped τ e_+)))
   (where (σ_+ e_+) #{untyped-step# (σ e)})]
  [(do-from-untyped σ E e τ)
   Error
   (where Error #{untyped-step# (σ e)})])

(define-metafunction μTR
  do-apply/untyped : σ E v v -> A
  [(do-apply/untyped _ _ v _)
   (TE v "procedure?")
   (judgment-holds (not-fun-value v))]
  [(do-apply/untyped σ E Λ v_arg)
   (σ (in-hole E e_body+))
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply/untyped σ E Λ v_arg)
   (σ (in-hole E (from-typed τ_cod e_body+)))
   (where (fun x_f τ_f (x_arg) e_body) Λ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ_f})
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))])

(define-metafunction μTR
  do-apply/typed : σ E v v -> A
  [(do-apply/typed σ E Λ v_arg)
   (σ (in-hole E (from-untyped TST e_body+)))
   (where (fun x_f (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply/typed σ E Λ v_arg)
   (σ (in-hole E e_body+))
   (where (fun x_f τ_f (x_arg) e_body) Λ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ_f})
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))])

(define-metafunction μTR
  do-ref/typed : σ E v v -> A
  [(do-ref/typed σ E v_0 v_1)
   #{do-ref σ E v_0 v_1}])

(define-metafunction μTR
  do-ref/untyped : σ E v v -> A
  [(do-ref/untyped _ _ v _)
   (TE v "vector?")
   (judgment-holds (not-vector-value v))]
  [(do-ref/untyped _ _ _ v)
   (TE v "integer?")
   (judgment-holds (not-integer-value v))]
  [(do-ref/untyped σ E v_0 v_1)
   #{do-ref σ E v_0 v_1}])

(define-metafunction μTR
  do-set/typed : σ E v v v -> A
  [(do-set/typed σ E v_0 v_1 v_2)
   #{do-set σ E v_0 v_1 v_2}])

(define-metafunction μTR
  do-set/untyped : σ E v v v -> A
  [(do-set/untyped _ _ v _ _)
   (TE v "vector?")
   (judgment-holds (not-vector-value v))]
  [(do-set/untyped _ _ _ v _)
   (TE v "integer?")
   (judgment-holds (not-integer-value v))]
  [(do-set/untyped σ E v_0 v_1 v_2)
   #{do-set σ E v_0 v_1 v_2}])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "tag-check"
    (check-mf-apply*
     ((tag-check# 4 Int)
      4)
     ((tag-check# nil List)
      nil)
     ((tag-check# (cons 1 (cons 2 (cons 3 nil))) List)
      (cons 1 (cons 2 (cons 3 nil))))
     ((tag-check# (vector x) Vector)
      (vector x))
     ((tag-check# (vector Int x) Vector)
      (vector Int x))
     ((tag-check# (cons (vector x) (cons (vector y) nil)) List)
      (cons (vector x) (cons (vector y) nil)))
     ((tag-check# (fun f (x) (+ x x)) →)
      (fun f (x) (+ x x)))
     ((tag-check# (fun f (→ Int Int) (x) (+ x x)) →)
      (fun f (→ Int Int) (x) (+ x x)))
     ((tag-check# 4 Int)
      4)
     ((tag-check# (vector q) Vector)
      (vector q))
     ((tag-check# (fun f (x) x) →)
      (fun f (x) x))
     ((tag-check# (fun f (→ (Vectorof Int) (Vectorof Int)) (x) x) →)
      (fun f (→ (Vectorof Int) (Vectorof Int)) (x) x))
     ((tag-check# (vector (Vectorof Int) aaa) Vector)
      (vector (Vectorof Int) aaa))
     ((tag-check# 4 List)
      (BE List 4))))

  (test-case "import/untyped"
    (check-mf-apply*
     ((import/untyped (a b c) ((a 1) (b 2) (c 3) (d 4)))
      ((a 1) (b 2) (c 3)))
    )
  )

  (test-case "import/tagged"
    (check-mf-apply*
     ((import/tagged ((a Int) (b Int) (c Int)) ((a 1) (b 2) (c 3) (d 4)))
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
      ((num 4) (f (fun g (→ Int Int) (x) x))))
     ((require->local-value-env ((m0 ((num 4)))) ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4) (y 5)))) ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 ([num Nat]))))
      ((num 4)))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (x) x)))))
                                ((require m0 ((num Int))) (require m1 ((f (→ (Vectorof Int) (Vectorof Int)))))))
      ((num 4) (f (fun g (x) x))))
     ((require->local-value-env ((m0 ((num 4))) (m1 ((f (fun g (→ Int Int) (x) x)))))
                                ((require m0 ((num Int))) (require m1 ((f (→ Int Int))))))
      ((num 4) (f (fun g (→ Int Int) (x) x))))
    )

    (check-exn exn:fail:contract?
      (λ () (term (require->local-value-env () ((require m x))))))

    (check-exn exn:fail:contract?
      (λ () (term (require->local-value-env ((m0 ((num 4)))) ((require m0 ((num (Vectorof Int)))))))))
  )

  (test-case "do-from-untyped"
    (check-mf-apply*
     ((do-from-untyped () hole 3 Int)
      (() 3))
     ((do-from-untyped () hole 3 (Vectorof Int))
      (BE Vector 3))
     ((do-from-untyped ((qq (0))) hole (vector qq) (Vectorof Nat))
      (((qq (0))) (vector qq)))
     ((do-from-untyped ((qq (0))) hole (vector qq) (Vectorof (→ Nat Nat)))
      (((qq (0))) (vector qq)))))

  (test-case "do-from-typed"
    (check-mf-apply*
     ((do-from-typed () hole 3 Int)
      (() 3))
     ((do-from-typed ((qq (0))) hole (vector qq) (Vectorof Nat))
      (((qq (0))) (vector qq)))
     ((do-from-typed ((qq (0))) hole (vector qq) (Vectorof (→ Nat Nat)))
      (((qq (0))) (vector qq))))

    (check-exn exn:fail:contract?
      (λ () (term #{do-from-typed () hole 3 (Vectorof Int)}))))


  (test-case "do-apply/untyped"
    (check-mf-apply* #:is-equal? α=?
     ((do-apply/untyped () hole 4 5)
      (TE 4 "procedure?"))
     ((do-apply/untyped () hole (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))) 2)
      (() (fun b (y) (fun c (z) (+ (+ 2 y) z)))))
    )

    (check-exn exn:fail:redex?
      (λ () (term #{do-apply/untyped () (from-untyped Int hole) (fun f (x) (+ x x)) 5})))
  )

  (test-case "do-apply/typed"
    (check-mf-apply*
     ((do-apply/typed ((a (1))) hole (fun f (→ Nat Nat) (x) (+ x x)) 5)
      (((a (1))) (+ 5 5)))
    )
  )

  (test-case "do-ref/typed"
    (check-mf-apply*
     ((do-ref/typed ((qq (1 2))) hole (vector qq) 0)
      (((qq (1 2))) 1))
     ((do-ref/typed ((qq (1 2))) hole (vector (Vectorof Int) qq) 1)
      (((qq (1 2))) 2))
     ((do-ref/typed ((qq ())) hole (vector qq) 3)
      BadIndex)))

  (test-case "do-ref/untyped"
    (check-mf-apply*
     ((do-ref/untyped ((qq (1 2))) hole (vector qq) 0)
      (((qq (1 2))) 1))
     ((do-ref/untyped () hole 4 5)
      (TE 4 "vector?"))))

  (test-case "do-set/typed"
    (check-mf-apply*
     ((do-set/typed ((qq (1 2))) hole (vector (Vectorof Nat) qq) 0 2)
      (((qq (2 2))) 2))
     ((do-set/typed ((qq (1 2))) hole (vector qq) 0 2)
      (((qq (2 2))) 2))))

  (test-case "do-set/untyped"
    (check-mf-apply*
     ((do-set/untyped () hole 4 5 6)
      (TE 4 "vector?"))
     ((do-set/untyped ((qq (0))) hole (vector qq) (vector qq) 6)
      (TE (vector qq) "integer?"))
     ((do-set/untyped ((qq (0 0))) hole (vector qq) 0 1)
      (((qq (1 0))) 1))))

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
         (define v (Vectorof Int) (make-vector (Vectorof Int) 1 2 (+ 2 1)))
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
           (define x Int (vector-ref (make-vector (Vectorof Int) 1) 999))
           (provide)))))))
    (check-exn #rx"BadIndex"
      (λ () (term
        (eval-program#
         ((module M UN
           (define x (vector-set! (make-vector 0) 4 5))
           (provide))))))))

  (test-case "eval-program:BE"
    (check-mf-apply*
     ((eval-program#
       ((module M0 TY
         (define v (Vectorof Int) (make-vector (Vectorof Int) 0))
         (provide v))
        (module M1 UN
         (require M0 v)
         (define x (vector-set! v 0 nil))
         (provide))))
      (((loc (nil))) ((M0 ((v (vector (Vectorof Int) loc)))) (M1 ()))))
     ((eval-program#
       ((module M0 UN
         (define v (make-vector -1))
         (provide v))
        (module M1 TY
         (require M0 ((v (Vectorof Nat))))
         (define x Int (vector-ref v 0))
         (provide))))
      (((loc (-1))) ((M0 ((v (vector loc)))) (M1 ()))))
     ((eval-program#
       ((module M0 TY
         (define f (→ Nat Nat) (fun f (→ Nat Nat) (x) (+ x 2)))
         (provide f))
        (module M1 UN
         (require M0 f)
         (define x (f -1))
         (provide))))
      (() ((M0 ((f (fun f (→ Nat Nat) (x) (+ x 2))))) (M1 ()))))
     ((eval-program#
       ;; WEIRD this is not an error because the semantics doesn't do the completion
       ((module M0 UN
         (define v (make-vector -1))
         (provide v))
        (module M1 TY
         (require M0 ((v (Vectorof Nat))))
         (define x Nat (vector-ref v 0))
         (provide))))
      (((loc (-1))) ((M0 ((v (vector loc)))) (M1 ()))))
    ((eval-program#
      ((module M0 UN
        (define f (fun f (x) nil))
        (provide f))
       (module M1 TY
        (require M0 ((f (→ Int Int))))
        (define x Int (f 3))
        (provide))))
     (() ((M0 ((f (fun f (x) nil)))) (M1 ())))))

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

  )

  (test-case "eval-program:bad-ann"
    (check-mf-apply* #:is-equal? α=?
     ((eval-program#
       ((module M0 UN
         (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))
         (provide f))
        (module M1 TY
         (require M0 ((f (→ Int (→ Int Int)))))
         (define f2 (→ Int Int) (f 2))
         (define f23 Int (f2 3))
         (provide f23))))
      (() ((M0 ((f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))))
           (M1 ((f23 (fun c (z) (+ (+ 2 3) z))))))))
     ((eval-program#
       ((module M0 UN
         (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))
         (provide f))
        (module M1 TY
         (require M0 ((f (→ Int (→ Int Int)))))
         (provide f))
        (module M2 UN
         (require M1 f)
         (define f2 (f 2))
         (define f23 (f2 3))
         (provide))))
      (() ((M0 ((f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))))
           (M1 ((f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))))
           (M2 ()))))
     ((eval-program#
       ((module M0 UN
         (define nats (cons 1 (cons 2 (cons -3 nil))))
         (provide nats))
        (module M1 TY
         (require M0 ((nats (Listof Nat))))
         (provide))))
      (() ((M0 ((nats (cons 1 (cons 2 (cons -3 nil)))))) (M1 ()))))
    )

    (check-exn #rx"TE"
      (lambda () (term
                   (eval-program#
                     ((module M0 UN
                       (define f (fun a (x) (vector-ref x 0)))
                       (provide f))
                      (module M1 TY
                       (require M0 ((f (→ Nat Nat))))
                       (define v Nat (f 4))
                       (provide)))))))
  )
)
