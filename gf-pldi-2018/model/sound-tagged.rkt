#lang mf-apply racket/base

;; Soundness for Tagged Racket semantics
;; i.e. theorems connecting the typechecker to the reduction semantics

;; Theorems:
;;  VERY SIMILAR TO SOUND-TYPED THEOREMS
;;  but expression soundness is weaker
;;  and so, "models" is weaker
;;
;; - expression soundness
;;   * if Γ ⊢ e : τ
;;   * then forall ρ models Γ
;;   * ⊢ ρ(e) : κ
;;   * either:
;;     + reduces to value, ⊢ v : κ
;;     + diverges, raises value error
;;     + raises type error in untyped code
;;     + raises boundary error
;;   * via progress and preservation

;; -----------------------------------------------------------------------------

(require
  "eval-common.rkt"
  "eval-tagged.rkt"
  "lang.rkt"
  "metafunctions.rkt"
  "tagcheck.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

(define-judgment-form μTR
  #:mode (sound-eval-program I)
  #:contract (sound-eval-program PROGRAM)
  [
   (well-typed-program PROGRAM TYPE-ENV)
   (sound-eval-module* () () () PROGRAM TYPE-ENV_rev σ_N VAL-ENV_N)
   (where TYPE-ENV_N ,(reverse (term TYPE-ENV_rev)))
   (side-condition #{toplevel-type-env=? TYPE-ENV TYPE-ENV_N})
   (toplevel-value-env-models σ_N VAL-ENV_N TYPE-ENV_N)
   ---
   (sound-eval-program PROGRAM)])

(define-judgment-form μTR
  #:mode (sound-eval-module* I I I I O O O)
  #:contract (sound-eval-module* TYPE-ENV σ VAL-ENV (MODULE ...) TYPE-ENV σ VAL-ENV)
  [
   ---
   (sound-eval-module* TYPE-ENV σ VAL-ENV () TYPE-ENV σ VAL-ENV)]
  [
   (where (MODULE_0 MODULE_rest ...) PROGRAM)
   (sound-eval-module TYPE-ENV_0 σ_0 VAL-ENV_0 MODULE_0 TYPE-ENV_1 σ_1 VAL-ENV_1)
   (sound-eval-module* TYPE-ENV_1 σ_1 VAL-ENV_1 (MODULE_rest ...) TYPE-ENV_N σ_N VAL-ENV_N)
   ---
   (sound-eval-module* TYPE-ENV_0 σ_0 VAL-ENV_0 PROGRAM TYPE-ENV_N σ_N VAL-ENV_N)])

(define-judgment-form μTR
  #:mode (sound-eval-module I I I I O O O)
  #:contract (sound-eval-module TYPE-ENV σ VAL-ENV MODULE TYPE-ENV σ VAL-ENV)
  [
   (where (module M _ REQUIRE ... DEFINE ... PROVIDE) MODULE)
   (where ρ #{require->local-value-env VAL-ENV (REQUIRE ...)})
   (where Γ #{local-type-env-append #{require->local-type-env TYPE-ENV (REQUIRE ...)}
                                    #{define->local-type-env (DEFINE ...)}})
   (sound-eval-define* Γ σ ρ (DEFINE ...) σ_+ ρ_+)
   (where Γ_provide #{local-type-env->provided Γ PROVIDE})
   (where TYPE-ENV_+ #{toplevel-type-env-set TYPE-ENV M Γ_provide})
   (where ρ_provide #{local-value-env->provided ρ_+ PROVIDE})
   (where VAL-ENV_+ #{toplevel-value-env-set VAL-ENV M ρ_provide})
   ---
   (sound-eval-module TYPE-ENV σ VAL-ENV MODULE TYPE-ENV_+ σ_+ VAL-ENV_+)])

(define-judgment-form μTR
  #:mode (sound-eval-define* I I I I O O)
  #:contract (sound-eval-define* Γ σ ρ (DEFINE ...) σ ρ)
  [
   ---
   (sound-eval-define* Γ σ ρ () σ ρ)]
  [
   (sound-eval-define Γ σ ρ DEFINE_0 σ_1 ρ_1)
   (sound-eval-define* Γ σ_1 ρ_1 (DEFINE_rest ...) σ_N ρ_N)
   ---
   (sound-eval-define* Γ σ ρ (DEFINE_0 DEFINE_rest ...) σ_N ρ_N)])

(define-judgment-form μTR
  #:mode (sound-eval-define I I I I O O)
  #:contract (sound-eval-define Γ σ ρ DEFINE σ ρ)
  [
   (where (define x e) UNTYPED-DEFINE)
   (where A_+ #{sound-eval-untyped-expression# Γ σ ρ e})
   (where (σ_+ v_+) #{unpack-answer A_+})
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (sound-eval-define Γ σ ρ UNTYPED-DEFINE σ_+ ρ_+)]
  [
   (where (define x τ e) TYPED-DEFINE)
   (where A_+ #{sound-eval-typed-expression# Γ σ ρ e τ})
   (where (σ_+ v_+) #{unpack-answer A_+})
   (where ρ_+ #{local-value-env-set ρ x v_+})
   ---
   (sound-eval-define Γ σ ρ TYPED-DEFINE σ_+ ρ_+)])

(define-metafunction μTR
  unpack-answer : A -> [σ v]
  [(unpack-answer Error)
   ,(raise-arguments-error 'sound-eval-expression "not implemented for errors"
     "answer" (term Error))]
  [(unpack-answer [σ v])
   [σ v]])

(define-metafunction μTR
  sound-eval-untyped-expression# : Γ σ ρ e -> A
  [(sound-eval-untyped-expression# Γ σ ρ e)
   A
   (judgment-holds (sound-eval-untyped-expression Γ σ ρ e A))]
  [(sound-eval-untyped-expression# Γ σ ρ e)
   ,(raise-arguments-error 'sound-eval-untyped-expression "failed to eval"
     "type env" (term Γ)
     "store" (term σ)
     "value env" (term ρ)
     "expr" (term e))])

(define-metafunction μTR
  sound-eval-typed-expression# : Γ σ ρ e τ -> A
  [(sound-eval-typed-expression# Γ σ ρ e τ)
   A
   (judgment-holds (sound-eval-typed-expression Γ σ ρ e τ A))]
  [(sound-eval-typed-expression# Γ σ ρ e τ)
   ,(raise-arguments-error 'sound-eval-typed-expression "failed to eval"
     "type env" (term Γ)
     "store" (term σ)
     "value env" (term ρ)
     "expr" (term e)
     "type" (term τ))])

(define-judgment-form μTR
  #:mode (sound-eval-untyped-expression I I I I O)
  #:contract (sound-eval-untyped-expression Γ σ ρ e A)
  [
   (well-dyn-expression Γ e)
   (local-value-env-models σ ρ Γ)
   (where Σ_0 #{load-expression σ ρ e})
   (where (A τ) ,(sound-step* (term [Σ_0 TST])))
   ---
   (sound-eval-untyped-expression Γ σ ρ e A)])

(define-judgment-form μTR
  #:mode (sound-eval-typed-expression I I I I I O)
  #:contract (sound-eval-typed-expression Γ σ ρ e τ A)
  [
   (well-typed-expression Γ e τ)
   (local-value-env-models σ ρ Γ)
   (tag-of τ κ)
   (tagged-completion Γ e κ e_+)
   (well-tagged-expression Γ e_+ τ)
   (where Σ_0 #{load-expression σ ρ e})
   (where (A τ) ,(sound-step* (term [Σ_0 τ])))
   ---
   (sound-eval-typed-expression Γ σ ρ e τ A)])

(define sound-step
  (reduction-relation μTR
    #:domain [A τ]
    [-->
      (Σ τ)
      (A τ)
      T-step
      (judgment-holds (not-TST τ))
      (judgment-holds (well-tagged-state Σ τ))
      (where A #{typed-step# Σ})
      (side-condition (not (equal? (term Σ) (term A))))
      (judgment-holds (well-tagged-answer A τ))]
    [-->
      (Σ TST)
      (A TST)
      U-step
      (judgment-holds (well-tagged-state Σ TST))
      (where A #{untyped-step# Σ})
      (side-condition (not (equal? (term Σ) (term A))))
      (judgment-holds (well-tagged-answer A TST))]))

(define sound-step*
  (make--->* sound-step))

(define-metafunction μTR
  sound-step# : Σ τ -> [A boolean]
  [(sound-step# Σ τ)
   ,(let ((x* (apply-reduction-relation sound-step (term (Σ τ)))))
     (cond
      [(null? x*)
       (term (Σ #false))]
      [(null? (cdr x*))
       (define A (caar x*))
       (list A (not (redex-match? μTR Error A)))]
      [else
       (raise-arguments-error 'sound-step# "non-deterministic"
         "state" (term Σ)
         "type" (term τ)
         "results" x*)]))])

(define-judgment-form μTR
  #:mode (well-tagged-answer I I)
  #:contract (well-tagged-answer A κ)
  [
   ---
   (well-tagged-answer BoundaryError _)]
  [
   ---
   (well-tagged-answer TypeError _)]
  [
   (well-tagged-state Σ_+ κ)
   ---
   (well-tagged-answer Σ_+ κ)])

(define-judgment-form μTR
  #:mode (well-tagged-state I I)
  #:contract (well-tagged-state Σ κ)
  [
   (WK σ () e κ)
   ---
   (well-tagged-state (σ e) κ)])

(define-judgment-form μTR
  #:mode (WK I I I I)
  #:contract (WK σ Γ e κ)
  [
   (or-TST Nat κ)
   --- T-Nat
   (WK σ Γ natural κ)]
  [
   (or-TST Int κ)
   --- T-Int
   (WK σ Γ integer κ)]
  [
   (where (_ τ) #{local-type-env-ref Γ x})
   (or-TST #{type->tag τ} κ)
   --- T-Var
   (WK σ Γ x κ)]
  [
   (or-TST → κ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ_fun})
   (tag-of τ_cod κ_cod)
   (where Γ_fun #{local-type-env-set Γ x_fun τ_fun})
   (where Γ_x #{local-type-env-set Γ_fun x_arg τ_dom})
   (WK σ Γ_x e κ_cod)
   --- T-FunT0
   (WK σ Γ (fun x_fun τ_fun (x_arg) e) κ)]
  [
   (or-TST → κ)
   (where Γ_f #{local-type-env-set Γ x_f (→ TST TST)})
   (where Γ_x #{local-type-env-set Γ_f x_arg TST})
   (WK σ Γ_x e_body TST)
   --- T-FunU0
   (WK σ Γ (fun x_f (x_arg) e_body) κ)]
  [
   (or-TST Vector κ)
   (where (_ (v_elem ...)) #{store-ref σ x})
   (WK σ Γ v_elem TST) ...
   --- T-VecValT
   (WK σ Γ (vector τ x) κ)]
  [
   (or-TST Vector κ)
   (where (_ (v_elem ...)) #{store-ref σ x})
   (WK σ Γ v_elem TST) ...
   --- T-VecValU
   (WK σ Γ (vector x) κ)]
  [
   (or-TST #{type->tag τ_vec} κ)
   (WK σ Γ e TST) ...
   --- T-VecT
   (WK σ Γ (make-vector τ_vec e ...) κ)]
  [
   (or-TST Vector κ)
   (WK σ Γ e TST) ...
   --- T-VecU
   (WK σ Γ (make-vector e ...) κ)]
  [
   (or-TST List κ)
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 TST)
   --- T-Cons
   (WK σ Γ (cons e_0 e_1) κ)]
  [
   (or-TST List κ)
   --- T-Nil
   (WK σ Γ nil κ)]
  [
   (WK σ Γ e_fun TST)
   (WK σ Γ e_arg TST)
   --- T-App
   (WK σ Γ (e_fun e_arg) TST)]
  [
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 κ)
   (WK σ Γ e_2 κ)
   --- T-Ifz
   (WK σ Γ (ifz e_0 e_1 e_2) κ)]
  [
   (WK σ Γ e_0 Int)
   (WK σ Γ e_1 Int)
   --- T-PlusT0
   (WK σ Γ (+ e_0 e_1) Int)]
  [
   (WK σ Γ e_0 Nat)
   (WK σ Γ e_1 Nat)
   --- T-PlusT1
   (WK σ Γ (+ e_0 e_1) Nat)]
  [
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 TST)
   --- T-PlusU
   (WK σ Γ (+ e_0 e_1) TST)]
  [
   (or-TST Int κ)
   (WK σ Γ e_0 Int)
   (WK σ Γ e_1 Int)
   --- T-MinusT
   (WK σ Γ (- e_0 e_1) κ)]
  [
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 TST)
   --- T-MinusU
   (WK σ Γ (- e_0 e_1) TST)]
  [
   (or-TST Int κ)
   (WK σ Γ e_0 Int)
   (WK σ Γ e_1 Int)
   --- T-TimesT0
   (WK σ Γ (* e_0 e_1) κ)]
  [
   (WK σ Γ e_0 Nat)
   (WK σ Γ e_1 Nat)
   --- T-TimesT1
   (WK σ Γ (* e_0 e_1) Nat)]
  [
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 TST)
   --- T-TimesU
   (WK σ Γ (* e_0 e_1) TST)]
  [
   (or-TST Int κ)
   (WK σ Γ e_0 Int)
   (WK σ Γ e_1 Int)
   --- T-DivideT0
   (WK σ Γ (% e_0 e_1) κ)]
  [
   (WK σ Γ e_0 Nat)
   (WK σ Γ e_1 Nat)
   --- T-DivideT1
   (WK σ Γ (% e_0 e_1) Nat)]
  [
   (WK σ Γ e_0 TST)
   (WK σ Γ e_1 TST)
   --- T-DivU
   (WK σ Γ (% e_0 e_1) TST)]
  [
   (WK σ Γ e_vec Vector)
   (WK σ Γ e_i Int)
   --- T-Ref
   (WK σ Γ (vector-ref e_vec e_i) TST)]
  [
   (WK σ Γ e_vec Vector)
   (WK σ Γ e_i Int)
   (WK σ Γ e_val κ)
   --- T-Set
   (WK σ Γ (vector-set! e_vec e_i e_val) κ)]
  [
   (WK σ Γ e TST)
   --- T-First
   (WK σ Γ (first e) TST)]
  [
   (or-TST List κ)
   (WK σ Γ e TST)
   --- T-Rest
   (WK σ Γ (rest e) κ)]
  [
   (WK σ Γ e κ)
   --- T-Union
   (WK σ Γ e (U κ_0 ... κ κ_1 ...))]
  [
   (WK σ Γ e TST)
   --- T-Tag
   (WK σ Γ (check κ e) κ)]
  [
   (tag-of τ κ)
   (WK σ Γ e TST)
   ---
   (WK σ Γ (from-untyped τ e) κ)]
  [
   (tag-of τ κ)
   (WK σ Γ e κ)
   ---
   (WK σ Γ (from-typed τ e) κ)])

(define-judgment-form μTR
  #:mode (toplevel-value-env-models I I I)
  #:contract (toplevel-value-env-models σ VAL-ENV TYPE-ENV)
  [
   (same-domain VAL-ENV TYPE-ENV)
   (toplevel-value-env-models-aux σ VAL-ENV TYPE-ENV)
   ---
   (toplevel-value-env-models σ VAL-ENV TYPE-ENV)])

(define-judgment-form μTR
  #:mode (toplevel-value-env-models-aux I I I)
  #:contract (toplevel-value-env-models-aux σ VAL-ENV TYPE-ENV)
  [
   ---
   (toplevel-value-env-models-aux σ () TYPE-ENV)]
  [
   (where (_ Γ_0) #{toplevel-type-env-ref TYPE-ENV M_0})
   (local-value-env-models σ ρ_0 Γ_0)
   (toplevel-value-env-models-aux σ (M:ρ_rest ...) TYPE-ENV)
   ---
   (toplevel-value-env-models-aux σ ((M_0 ρ_0) M:ρ_rest ...) TYPE-ENV)])

(define-judgment-form μTR
  #:mode (local-value-env-models I I I)
  #:contract (local-value-env-models σ ρ Γ)
  [
   ;;(same-domain ρ Γ)
   (local-value-env-models-aux σ ρ Γ)
   ---
   (local-value-env-models σ ρ Γ)])

(define-judgment-form μTR
  #:mode (local-value-env-models-aux I I I)
  #:contract (local-value-env-models-aux σ ρ Γ)
  [
   ---
   (local-value-env-models-aux σ () Γ)]
  [
   (where (_ τ) #{unsafe-env-ref Γ x_0 #false})
   (tag-of τ κ)
   (WK σ Γ v_0 κ)
   (local-value-env-models-aux σ (x:v_rest ...) Γ)
   ---
   (local-value-env-models-aux σ ((x_0 v_0) x:v_rest ...) Γ)])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "WK"
    (check-judgment-holds*
     (WK () () 4 Nat)
     (WK () () 4 TST)
     (WK () () -4 Int)
     (WK () () -4 TST)
     (WK () ((x Int)) x Int)
     (WK () ((x TST)) x TST)
     (WK () () (fun f (→ Nat Nat) (x) x) →)
     (WK () () (fun f (x) x) TST)
     (WK ((q (1 2))) () (vector (Vectorof Int) q) Vector)
     (WK ((q (1 2))) () (vector q) TST)
     (WK () () (make-vector (Vectorof Int) 1 2) Vector)
     (WK () () (make-vector 1 2) TST)
     (WK () () (cons 1 nil) List)
     (WK () () (cons 1 nil) TST)
     (WK () () nil List)
     (WK () () nil TST)
     (WK () ((f (→ Int Int))) (f -6) TST)
     (WK () ((f (→ Int Int))) (check Int (f -6)) Int)
     (WK () ((f TST)) (f f) TST) ;; TODO how is this allowed but still sound?
     (WK () () (3 3) TST)
     (WK () () (ifz 0 1 2) Nat)
     (WK () () (ifz nil nil nil) TST) ;; TODO soundness
     (WK () () (+ -1 2) Int)
     (WK () () (+ 3 2) Nat)
     (WK () () (+ 4 4) TST)
     (WK () () (+ nil nil) TST)
     (WK () () (- 3 3) Int)
     (WK () () (- 3 3) TST)
     (WK () () (- 3 nil) TST)
     (WK () () (* 3 -3) Int)
     (WK () () (* 3 3) Nat)
     (WK () () (* 3 3) TST)
     (WK () () (* nil 4) TST)
     (WK () () (% -6 2) Int)
     (WK () () (% 6 2) Nat)
     (WK () () (% 6 2) TST)
     (WK () () (% nil nil) TST)
     (WK () () (vector-ref (make-vector (Vectorof Int) 2 3) 0) TST)
     (WK () () (vector-ref (make-vector 3) 0) TST)
     (WK () () (vector-set! (make-vector (Vectorof Int) 2 3) 0 -3) Int)
     (WK () () (vector-set! (make-vector 2) 0 nil) TST)
     (WK () () (first nil) TST)
     (WK () () (first (cons 1 nil)) TST)
     (WK () () (first 3) TST) ;; TODO soundness
     (WK () () (rest nil) List)
     (WK () () (rest (cons 1 nil)) List)
     (WK () () (rest 4) TST) ;; TODO soundness
     (WK () () 4 (U Nat →))
     (WK () () (fun f (∀ (α) (→ α α)) (x) x) →)
     (WK () () (fun f (x) x) →)
     (WK () () (make-vector 1 2) Vector)

     (WK () () (ifz nil 1 2) Nat)
    )

    (check-not-judgment-holds*
     (WK () () -4 Nat)
     (WK () () nil Int)
     (WK () ((f (→ Int Int))) (f -6) Int)
     (WK () () (- 3 0) Nat)
     (WK () () (* -3 -3) Nat)
     (WK () () (vector-ref (make-vector 3) 0) Int)
     (WK () () (vector-ref (make-vector (Vectorof Int) 3) 0) Int)
     (WK () () (vector-set! (make-vector Nat 2 3) 0 -3) Int)
     (WK () () (first (cons 1 nil)) Int)
    )
  )

  (test-case "local-value-env-models"
    (check-judgment-holds*
     (local-value-env-models () () ())
     (local-value-env-models () ((x 4)) ((x Int)))
     (local-value-env-models () ((x 4) (y -1)) ((x Int) (y Int)))
     (local-value-env-models () ((x 4) (y -1)) ((y Int) (x Int)))
     (local-value-env-models () ((x nil)) ((x (Listof Nat))))
     (local-value-env-models () ((x nil)) ((x TST)))
     (local-value-env-models () ((x (fun f (z) z))) ((x TST)))
     (local-value-env-models
       ()
       ((x (fun f (→ Nat Nat) (z) (+ z 3))))
       ((x (→ Nat Nat))))
     (local-value-env-models () () ((x Int)))
     (local-value-env-models () ((x (fun f (z) (+ z 3)))) ((x (→ Nat Nat))))
    )

    (check-not-judgment-holds*
     (local-value-env-models () ((x 4)) ((y Int)))
     (local-value-env-models () ((x 4) (y -1)) ((x Int) (y Nat)))
    )
  )

  (test-case "well-tagged-state"
    (check-judgment-holds*
     (well-tagged-state (() (+ nil 2)) TST)
     (well-tagged-state (() (+ 2 2)) Nat)
     (well-tagged-state (((qq (1 2))) (vector (Vectorof Nat) qq))
                        Vector)
     (well-tagged-state (() (* 4 4)) TST)
    )

    (check-not-judgment-holds*
     (well-tagged-state (() (+ nil 2)) Int)
     (well-tagged-state (((qq (1 -2))) (vector (Vectorof Nat) qq)) Nat)
    )
  )

  (test-case "sound-step"
    (check-mf-apply*
     ((sound-step# (() (+ 4 4)) Int)
      ((() 8) #true))
     ((sound-step# (() (from-untyped Int (+ 2 2))) Int)
      ((() (from-untyped Int 4)) #true))
     ((sound-step# (() (from-untyped Int (+ 2 nil))) Int)
      ((TE nil "integer?") #false))
     ((sound-step# (() (* 4 4)) TST)
      ((() 16) #true))
     ((sound-step# (() 16) TST)
      ((() 16) #false))
    )
  )

  (test-case "well-tagged-answer"
    (check-judgment-holds*
     (well-tagged-answer (BE Int nil) Int)
     (well-tagged-answer DivisionByZero Int)
     (well-tagged-answer EmptyList TST)
     (well-tagged-answer (TE 4 (Listof Int)) TST)
     (well-tagged-answer (TE 4 List) List)
     (well-tagged-answer (() (+ 2 2)) TST)
     (well-tagged-answer (() (+ 2 nil)) TST)
     (well-tagged-answer (() (+ 2 2)) Int)
     (well-tagged-answer (() 16) TST)
     (well-tagged-answer (() (+ 2 2)) Int)
    )
  )

  (test-case "sound-step"
    (check-mf-apply*
     ((sound-step# (() (+ 4 4)) Int)
      ((() 8) #true))
     ((sound-step# (() (check Int (+ 2 2))) Int)
      ((() (check Int 4)) #true))
     ((sound-step# (() (from-untyped Int (+ 2 nil))) Int)
      ((TE nil "integer?") #false))
     ((sound-step# (() (* 4 4)) TST)
      ((() 16) #true))
     ((sound-step# (() 16) TST)
      ((() 16) #false))
    )
  )

  (test-case "sound-eval-expression"
    (check-mf-apply*
     ((sound-eval-typed-expression# () () () (+ 2 2) Int)
      (() 4))
     ((sound-eval-untyped-expression# () () () (* 4 4))
      (() 16))
     ((sound-eval-untyped-expression# () () () (* 4 nil))
      (TE nil "integer?"))
     ((sound-eval-untyped-expression# () () () (4 4))
      (TE 4 "procedure?"))
    )

    ;; `check` is not part of the source language
    (check-exn exn:fail:contract?
      (λ () (term #{sound-eval-typed-expression# () () () (check Int nil) Int})))
  )

  (test-case "sound-eval-program"
    (check-judgment-holds*
     (sound-eval-program
      ((module M0 untyped
        (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int (→ Int Int)))))
        (provide f))
       (module M2 untyped
        (require M1 f)
        (define f2 (f 2))
        (define f23 (f2 3))
        (provide))))
    )
  )

  (test-case "sound-eval-program"
    (check-judgment-holds*
     (sound-eval-program
      ((module M0 untyped
        (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int (→ Int Int)))))
        (provide f))
       (module M2 untyped
        (require M1 f)
        (define f2 (f 2))
        (define f23 (f2 3))
        (provide))))
    )
  )

  (test-case "toplevel-value-env-models"
    (check-judgment-holds*
     (toplevel-value-env-models () () ())
     (toplevel-value-env-models () ((M0 ())) ((M0 ())))
     (toplevel-value-env-models ((q (1 2)) (w (1))) ((M0 ())) ((M0 ())))
     (toplevel-value-env-models () ((M0 ((x 4)))) ((M0 ((x Int)))))
     (toplevel-value-env-models ()
                                ((M0 ((x 4))) (M1 ((y (cons 1 nil)))))
                                ((M0 ((x Int))) (M1 ((y (Listof Nat))))))
     (toplevel-value-env-models ()
                                ((M0 ((x 4))) (M1 ((y (cons nil nil)))))
                                ((M0 ((x Int))) (M1 ((y (Listof Nat))))))
     (toplevel-value-env-models ((qq (0 1 2)))
                                ((M0 ((x (vector qq)))))
                                ((M0 ((x (Vectorof Nat))))))
     (toplevel-value-env-models ((qq (0 -1 -2)))
                                ((M0 ((x (vector qq)))))
                                ((M0 ((x (Vectorof Nat))))))
    )

    (check-not-judgment-holds*
     (toplevel-value-env-models () ((M0 ())) ((M1 ())))
     (toplevel-value-env-models () ((M0 ())) ())
     (toplevel-value-env-models () ()        ((M1 ())))
     (toplevel-value-env-models () ((M0 ((x -4)))) ((M0 ((x Nat)))))
    )
  )
)
