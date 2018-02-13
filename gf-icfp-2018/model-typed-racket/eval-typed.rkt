#lang mf-apply racket/base

;; Typed Racket semantics.
;;
;; This is ONLY the semantics.
;; No types involved, no theorems involved.
;; Just "how things should run".

(provide
  eval-program
  untyped-step
  untyped-step#
  typed-step
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
   (judgment-holds (fun-value v_fun))
   (judgment-holds (infer-expression-type () v_fun τ_fun))]
  [(protect-value v_vec)
   #{apply-monitor#/fail v_vec τ_vec}
   (judgment-holds (vector-value v_vec))
   (judgment-holds (infer-expression-type () v_vec τ_vec))]
  [(protect-value v)
   v])

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

;; Reduction relations should have a more fine-grained domain than A,
;;  but A is the only choice that allows monitors

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
   (σ (in-hole E v_+))
   (where v_+ #{apply-monitor# v τ})]
  [(do-from-typed σ E v τ)
   ,(raise-arguments-error 'do-from-typed "bad value from typed code"
     "expected" (term τ)
     "given" (term v))]
  [(do-from-typed σ E e τ)
   (σ_+ (in-hole E (from-typed τ e_+)))
   (where (σ_+ e_+) #{typed-step# (σ e)})]
  [(do-from-typed σ E e τ)
   Error
   (where Error #{typed-step# (σ e)})])

(define-metafunction μTR
  do-from-untyped : σ E e τ -> A
  [(do-from-untyped σ E v τ)
   #{make-answer σ E #{apply-monitor# v τ}}]
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
  [(do-apply/untyped σ E (mon-fun τ v_f) v_arg)
   (σ (in-hole E (from-typed τ_cod (v_f (from-untyped τ_dom v_arg)))))
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})])

(define-metafunction μTR
  do-apply/typed : σ E v v -> A
  [(do-apply/typed σ E Λ v_arg)
   (σ (in-hole E e_body+))
   (where (fun x_f _ (x_arg) e_body) Λ)
   (where e_body+ (substitute (substitute e_body x_f Λ) x_arg v_arg))]
  [(do-apply/typed σ E (mon-fun τ v_f) v_arg)
   (σ (in-hole E (from-untyped τ_cod (v_f (from-typed τ_dom v_arg)))))
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})])

(define-metafunction μTR
  do-ref/typed : σ E v v -> A
  [(do-ref/typed σ E (mon-vector τ v_0) v_1)
   (σ (in-hole E (from-untyped τ_elem (vector-ref v_0 v_1))))
   (where (Vectorof τ_elem) #{coerce-vector-type τ})]
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
  [(do-ref/untyped σ E (mon-vector τ v_0) v_1)
   (σ (in-hole E (from-typed τ_elem (vector-ref v_0 v_1))))
   (where (Vectorof τ_elem) #{coerce-vector-type τ})]
  [(do-ref/untyped σ E v_0 v_1)
   #{do-ref σ E v_0 v_1}])

(define-metafunction μTR
  do-set/typed : σ E v v v -> A
  [(do-set/typed σ E (mon-vector τ v_0) v_1 v_2)
   (σ (in-hole E (from-untyped τ_elem (vector-set! v_0 v_1 (from-typed τ_elem v_2)))))
   (where (Vectorof τ_elem) #{coerce-vector-type τ})]
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
  [(do-set/untyped σ E (mon-vector τ v_0) v_1 v_2)
   (σ (in-hole E (from-typed τ_elem (vector-set! v_0 v_1 (from-untyped τ_elem v_2)))))
   (where (Vectorof τ_elem) #{coerce-vector-type τ})]
  [(do-set/untyped σ E v_0 v_1 v_2)
   #{do-set σ E v_0 v_1 v_2}])

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
     [(apply-monitor# (vector (Vectorof Int) x) (Vectorof Int))
      (mon-vector (Vectorof Int) (vector (Vectorof Int) x))]
     [(apply-monitor# nil (Listof (Vectorof Int)))
      nil]
     [(apply-monitor# (cons (vector (Vectorof Int) x) nil) (Listof (Vectorof Int)))
      (cons (mon-vector (Vectorof Int) (vector (Vectorof Int) x)) nil)]
     [(apply-monitor# (cons (vector (Vectorof Int) x)
                            (cons (vector (Vectorof Int) y) nil)) (Listof (Vectorof Int)))
      (cons (mon-vector (Vectorof Int) (vector (Vectorof Int) x))
            (cons (mon-vector (Vectorof Int) (vector (Vectorof Int) y)) nil))]
     [(apply-monitor# (fun f (x) (+ x x)) (→ Int Int))
      (mon-fun (→ Int Int) (fun f (x) (+ x x)))]
     [(apply-monitor# (fun f (→ Int Int) (x) (+ x x)) (→ Int Int))
      (mon-fun (→ Int Int) (fun f (→ Int Int) (x) (+ x x)))]
    )

   (check-exn exn:fail:contract?
     (λ () (term (apply-monitor#/fail 4 (Listof Int)))))
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

  (test-case "do-from-untyped"
    (check-mf-apply*
     ((do-from-untyped () hole 3 Int)
      (() 3))
     ((do-from-untyped () hole 3 (Vectorof Int))
      (BE (Vectorof Int) 3))
     ((do-from-untyped ((qq (0))) hole (vector qq) (Vectorof Nat))
      (((qq (0))) (mon-vector (Vectorof Nat) (vector qq))))))

  (test-case "do-from-typed"
    (check-mf-apply*
     ((do-from-typed () hole 3 Int)
      (() 3))
     ((do-from-typed ((qq (0))) hole (vector qq) (Vectorof Nat))
      (((qq (0))) (mon-vector (Vectorof Nat) (vector qq)))))

    (check-exn exn:fail:contract?
      (λ () (term #{do-from-typed () hole 3 (Vectorof Int)}))))

  (test-case "do-apply/untyped"
    (check-mf-apply*
     ((do-apply/untyped () hole 4 5)
      (TE 4 "procedure?"))
     ((do-apply/untyped () hole
       (mon-fun (→ Int (→ Int Int))
         (mon-fun (→ Int (→ Int Int))
           (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))) 2)
      (()
       (from-typed (→ Int Int)
         ((mon-fun (→ Int (→ Int Int)) (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))
           (from-untyped Int 2)))))
    )

    (check-exn exn:fail:redex?
      ;; Not a valid context (not sure if good thing)
      (λ () (term #{do-apply/untyped () (from-untyped Int hole) (fun f (x) (+ x x)) 5})))
  )

  (test-case "do-apply/typed"
    (check-mf-apply*
     ((do-apply/typed ((a (1))) hole (fun f (→ Nat Nat) (x) (+ x x)) 5)
      (((a (1))) (+ 5 5)))
     ((do-apply/typed () hole (mon-fun (→ Nat Nat) (fun f (x) (+ x x))) 5)
      (() (from-untyped Nat ((fun f (x) (+ x x)) (from-typed Nat 5)))))
    )
  )

  (test-case "do-ref/typed"
    (check-mf-apply*
     ((do-ref/typed ((qq (1 2))) hole (vector qq) 0)
      (((qq (1 2))) 1))
     ((do-ref/typed ((qq (1 2))) hole (vector (Vectorof Int) qq) 1)
      (((qq (1 2))) 2))
     ((do-ref/typed ((qq ())) hole (vector qq) 3)
      BadIndex)
     ((do-ref/typed ((qq (2))) hole (mon-vector (Vectorof Nat) (vector qq)) 0)
      (((qq (2))) (from-untyped Nat (vector-ref (vector qq) 0))))
    )
  )

  (test-case "do-ref/untyped"
    (check-mf-apply*
     ((do-ref/untyped ((qq (1 2))) hole (vector qq) 0)
      (((qq (1 2))) 1))
     ((do-ref/untyped () hole 4 5)
      (TE 4 "vector?"))
     ((do-ref/untyped ((qq (2))) hole (mon-vector (Vectorof Nat) (vector (Vectorof Nat) qq)) 0)
      (((qq (2))) (from-typed Nat (vector-ref (vector (Vectorof Nat) qq) 0))))
    )
  )

  (test-case "do-set/typed"
    (check-mf-apply*
     ((do-set/typed ((qq (1 2))) hole (vector (Vectorof Nat) qq) 0 2)
      (((qq (2 2))) 2))
     ((do-set/typed ((qq (1 2))) hole (mon-vector (Vectorof Nat) (vector qq)) 0 2)
      (((qq (1 2))) (from-untyped Nat (vector-set! (vector qq) 0 (from-typed Nat 2)))))
     ((do-set/typed ((x ()) (qq ((vector z))) (z (1)))
                    hole
                    (mon-vector (Vectorof (Vectorof Nat)) (vector qq))
                    0
                    (vector (Vectorof Nat) x))
      (((x ()) (qq ((vector z))) (z (1)))
       (from-untyped (Vectorof Nat)
         (vector-set! (vector qq) 0 (from-typed (Vectorof Nat) (vector (Vectorof Nat) x))))))
    )
  )

  (test-case "do-set/untyped"
    (check-mf-apply*
     ((do-set/untyped () hole 4 5 6)
      (TE 4 "vector?"))
     ((do-set/untyped ((qq (0))) hole (vector qq) (vector qq) 6)
      (TE (vector qq) "integer?"))
     ((do-set/untyped ((qq (0 0))) hole (vector qq) 0 1)
      (((qq (1 0))) 1))
     ((do-set/untyped ((qq (5))) hole (mon-vector (Vectorof Int) (vector (Vectorof Int) qq)) 0 (fun f (x) 1))
      (((qq (5))) (from-typed Int (vector-set! (vector (Vectorof Int) qq) 0 (from-untyped Int (fun f (x) 1))))))
     ((do-set/untyped ((qq ((fun f (x) 0)))) hole (mon-vector (Vectorof (→ Nat Nat)) (vector (→ Nat Nat) qq)) 0 (fun f (x) 1))
      (((qq ((fun f (x) 0))))
       (from-typed (→ Nat Nat) (vector-set! (vector (→ Nat Nat) qq) 0 (from-untyped (→ Nat Nat) (fun f (x) 1))))))
    )
  )

  (test-case "typed-step"
    (check-true (redex-match? μTR e (term
      (vector-set! (vector (Vectorof Int) loc) 0 (from-untyped Int nil)))))
    (check-mf-apply*
     ((typed-step# (() (make-vector (Vectorof Int) 1 2 3)))
      (((loc (1 2 3))) (vector (Vectorof Int) loc)))
     ((typed-step# (((loc (0))) (vector-set! (vector (Vectorof Int) loc) 0 (from-untyped Int nil))))
      (BE Int nil))
    )
  )

  (test-case "untyped-step#"
    (check-mf-apply*
     ((untyped-step# (((loc (0))) (vector-set! (vector loc) 0 nil)))
      (((loc (nil))) nil))
    )
  )

  (test-case "eval-value"
    (check-mf-apply*
     ((eval-expression# () () UN (+ 2 2))
      (() 4))
     ((eval-expression# () () TY (+ (+ 2 2) (+ 2 2)))
      (() 8))
     ((eval-expression# ((q (1))) ((a 7)) UN (+ 2 2))
      (((q (1))) 4))
     ((eval-expression# ((q (1))) ((a 7)) UN (+ a a))
      (((q (1))) 14))
     ((eval-expression# () () TY (make-vector (Vectorof Int) 1 2 3))
      (((loc (1 2 3))) (vector (Vectorof Int) loc)))
    )

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
    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 TY
           (define v (Vectorof Int) (make-vector (Vectorof Int) 0))
           (provide v))
          (module M1 UN
           (require M0 v)
           (define x (vector-set! v 0 nil))
           (provide)))))))

    (check-exn #rx"BE"
      (λ () (term
        (eval-program#
         ((module M0 UN
           (define v (make-vector -1))
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
          (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))
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

  (test-case "no-mon-between-typed"
    ;; If typed code imports a typed function,
    ;;  only do a subtyping check.
    ;; Do not monitor the typed function in typed code.
    ;; (Safe assuming type checker is correct)

    (check-mf-apply*
      ((eval-program#
        ((module M0 TY
          (define f (→ Nat Nat) (fun a (→ Nat Nat) (b) b))
          (provide f))
         (module M1 TY
          (require M0 ((f (→ Nat Nat))))
          (define v Nil (f nil))
          (provide v))))
       (() ((M0 ((f (fun a (→ Nat Nat) (b) b))))
            (M1 ((v nil))))))))

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

