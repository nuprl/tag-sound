#lang mf-apply racket/base

;; Soundness for Typed Racket semantics
;; i.e. theorems connecting the typechecker to the reduction semantics

;; Theorems:
;; - program soundness
;;   * if PROGRAM well-typed at TYPE-ENV
;;   * then reduces to a VAL-ENV (or legal error)
;;   * and VAL-ENV models TYPE-ENV (under store σ)
;; - module-soundness
;;   * if Γ ⊢ MODULE well-typed at Γ+
;;   * then for any ρ that models Γ
;;   * module reduces to a ρ+
;;   * and ρ+ models Γ+
;;   * (ignore the σ ... sort of)
;; - require soundness
;;   * if Γ ⊢ require at Γ+
;;   * then for any ρ that models Γ
;;   * requires reduce to ρ
;;   * and ρ+ models Γ+
;; - define soudness
;;   * if Γ ⊢ define at Γ+
;;   * then for any ρ that models Γ
;;   * defines reduce to ρ+
;;   * and ρ+ models Γ+
;; - provide soundness
;;   * if Γ ⊢ provide at Γ+
;;   * then for any ρ that models Γ
;;   * provides reduce to ρ+
;;   * and ρ+ models Γ+
;; - expression soundness
;;   * if Γ ⊢ e : τ
;;   * then forall ρ models Γ
;;   * ⊢ ρ(e) : τ
;;   * either:
;;     + reduces to value, ⊢ v : τ
;;     + diverges, raises value error
;;     + raises type error in untyped code
;;     + raises boundary error
;;   * via progress and preservation
;; - type error soundness
;;   * E[e] where E is typed context
;;     cannot possibly step to TypeError

;; -----------------------------------------------------------------------------

(require
  "eval-common.rkt"
  "eval-typed.rkt"
  "lang.rkt"
  "metafunctions.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

(define-metafunction μTR
  sound-eval-program# : PROGRAM -> [σ VAL-ENV]
  [(sound-eval-program# PROGRAM)
   [σ VAL-ENV]
   (judgment-holds (sound-eval-program PROGRAM σ VAL-ENV))]
  [(sound-eval-program# PROGRAM)
   ,(raise-argument-error 'sound-eval-program "well-typed program" (term PROGRAM))
   (side-condition (not (judgment-holds (well-typed-program PROGRAM TYPE-ENV))))]
  [(sound-eval-program# PROGRAM)
   ,(raise-arguments-error 'sound-eval-program "undefined for program"
     "program" (term PROGRAM))])

(define-judgment-form μTR
  #:mode (sound-eval-program I O O)
  #:contract (sound-eval-program PROGRAM σ VAL-ENV)
  [
   (well-typed-program PROGRAM TYPE-ENV)
   (sound-eval-module* () () () PROGRAM TYPE-ENV_rev σ_N VAL-ENV_rev)
   (where TYPE-ENV_N ,(reverse (term TYPE-ENV_rev)))
   (where VAL-ENV_N ,(reverse (term VAL-ENV_rev)))
   (side-condition #{toplevel-type-env=? TYPE-ENV TYPE-ENV_N})
   (toplevel-value-env-models σ_N VAL-ENV_N TYPE-ENV_N)
   ---
   (sound-eval-program PROGRAM σ_N VAL-ENV_N)])

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
   (well-typed-module TYPE-ENV MODULE TYPE-ENV_+) ;; double-check
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
   (where A_+ #{sound-eval-untyped-expression# Γ σ ρ e}) ;; gives better error messages
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
   ,(raise-arguments-error 'sound-eval-expression "error during evaluation"
     "message" (term Error))]
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
      (judgment-holds (well-typed-state Σ τ))
      (where A #{typed-step# Σ})
      (side-condition (not (equal? (term Σ) (term A))))
      (judgment-holds (well-typed-answer A τ))]
    [-->
      (Σ TST)
      (A TST)
      U-step
      (judgment-holds (well-typed-state Σ TST))
      (where A #{untyped-step# Σ})
      (side-condition (not (equal? (term Σ) (term A))))
      (judgment-holds (well-typed-answer A TST))]))

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
  #:mode (well-typed-answer I I)
  #:contract (well-typed-answer A τ)
  [
   ---
   (well-typed-answer BoundaryError _)]
  [
   ---
   (well-typed-answer TypeError _)]
  [
   (well-typed-state Σ_+ τ)
   ---
   (well-typed-answer Σ_+ τ)])

(define-judgment-form μTR
  #:mode (well-typed-state I I)
  #:contract (well-typed-state Σ τ)
  [
   (WT σ () e τ)
   ---
   (well-typed-state (σ e) τ)])

;; "well-typed-expression" is the obvious name,
;;  but already using that for the static typing system
(define-judgment-form μTR
  #:mode (WT I I I I)
  #:contract (WT σ Γ e τ)
  [
   --- T-NatT
   (WT σ Γ natural Nat)]
  [
   --- T-NatU
   (WT σ Γ natural TST)]
  [
   --- T-IntT
   (WT σ Γ integer Int)]
  [
   --- T-IntU
   (WT σ Γ integer TST)]
  [
   (where [_ τ_0] #{local-type-env-ref Γ x})
   (<: τ_0 τ)
   --- T-VarT
   (WT σ Γ x τ)]
  [
   (where [_ TST] #{local-type-env-ref Γ x})
   --- T-VarU
   (WT σ Γ x TST)]
  [
   (<: τ τ_fun)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (where Γ_f #{local-type-env-set Γ x_f τ})
   (where Γ_x #{local-type-env-set Γ_f x_arg τ_dom})
   (WT σ Γ_x e_body τ_cod)
   --- T-FunT
   (WT σ Γ (fun x_f τ_fun (x_arg) e_body) τ)]
  [
   (where Γ_f #{local-type-env-set Γ x_f TST})
   (where Γ_x #{local-type-env-set Γ_f x_arg TST})
   (WT σ Γ_x e_body TST)
   --- T-FunU
   (WT σ Γ (fun x_f (x_arg) e_body) TST)]
  [
   (where (_ (v_elem ...)) #{store-ref σ x})
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (WT σ Γ v_elem τ_elem) ...
   --- T-VecT
   (WT σ Γ (vector τ x) τ)]
  [
   (where (_ (v_elem ...)) #{store-ref σ x})
   (WT σ Γ v_elem TST) ...
   --- T-VecU
   (WT σ Γ (vector x) TST)]
  [
   (<: τ_vec τ)
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (WT σ Γ e τ_elem) ...
   --- T-MakeVecT
   (WT σ Γ (make-vector τ_vec e ...) τ)]
  [
   (WT σ Γ e TST) ...
   --- T-MakeVecU
   (WT σ Γ (make-vector e ...) TST)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   (WT σ Γ e_0 τ_elem)
   (WT σ Γ e_1 τ)
   --- T-ConsT
   (WT σ Γ (cons e_0 e_1) τ)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   --- T-ConsU
   (WT σ Γ (cons e_0 e_1) TST)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   --- T-NilT
   (WT σ Γ nil τ)]
  [
   --- T-NilU
   (WT σ Γ nil TST)]
  [
   (infer-expression-type Γ e_fun τ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (WT σ Γ e_fun τ)
   (WT σ Γ e_arg τ_dom)
   --- T-AppT
   (WT σ Γ (e_fun e_arg) τ_cod)]
  [
   (WT σ Γ e_fun TST)
   (WT σ Γ e_arg TST)
   --- T-AppU
   (WT σ Γ (e_fun e_arg) TST)]
  [
   (WT σ Γ e_0 Int)
   (WT σ Γ e_1 τ)
   (WT σ Γ e_2 τ)
   --- T-IfzT
   (WT σ Γ (ifz e_0 e_1 e_2) τ)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   (WT σ Γ e_2 TST)
   --- T-IfzU
   (WT σ Γ (ifz e_0 e_1 e_2) TST)]
  [
   (WT σ Γ e_0 Int)
   (WT σ Γ e_1 Int)
   --- T-PlusT0
   (WT σ Γ (+ e_0 e_1) Int)]
  [
   (WT σ Γ e_0 Nat)
   (WT σ Γ e_1 Nat)
   --- T-PlusT1
   (WT σ Γ (+ e_0 e_1) Nat)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   --- T-PlusU
   (WT σ Γ (+ e_0 e_1) TST)]
  [
   (WT σ Γ e_0 Int)
   (WT σ Γ e_1 Int)
   --- T-MinusT
   (WT σ Γ (- e_0 e_1) Int)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   --- T-MinusU
   (WT σ Γ (- e_0 e_1) TST)]
  [
   (WT σ Γ e_0 Int)
   (WT σ Γ e_1 Int)
   --- T-TimesT0
   (WT σ Γ (* e_0 e_1) Int)]
  [
   (WT σ Γ e_0 Nat)
   (WT σ Γ e_1 Nat)
   --- T-TimesT1
   (WT σ Γ (* e_0 e_1) Nat)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   --- T-TimesU
   (WT σ Γ (* e_0 e_1) TST)]
  [
   (WT σ Γ e_0 Int)
   (WT σ Γ e_1 Int)
   --- T-DivideT0
   (WT σ Γ (% e_0 e_1) Int)]
  [
   (WT σ Γ e_0 Nat)
   (WT σ Γ e_1 Nat)
   --- T-DivideT1
   (WT σ Γ (% e_0 e_1) Nat)]
  [
   (WT σ Γ e_0 TST)
   (WT σ Γ e_1 TST)
   --- T-DivideU
   (WT σ Γ (% e_0 e_1) TST)]
  [
   (WT σ Γ e_vec (Vectorof τ))
   (WT σ Γ e_i Int)
   --- T-RefT
   (WT σ Γ (vector-ref e_vec e_i) τ)]
  [
   (WT σ Γ e_vec TST)
   (WT σ Γ e_i TST)
   --- T-RefU
   (WT σ Γ (vector-ref e_vec e_i) TST)]
  [
   (WT σ Γ e_vec (Vectorof τ))
   (WT σ Γ e_i Int)
   (WT σ Γ e_val τ)
   --- T-SetT
   (WT σ Γ (vector-set! e_vec e_i e_val) τ)]
  [
   (WT σ Γ e_vec TST)
   (WT σ Γ e_i TST)
   (WT σ Γ e_val TST)
   --- T-SetU
   (WT σ Γ (vector-set! e_vec e_i e_val) TST)]
  [
   (WT σ Γ e (Listof τ))
   --- T-FirstT
   (WT σ Γ (first e) τ)]
  [
   (WT σ Γ e TST)
   --- T-FirstU
   (WT σ Γ (first e) TST)]
  [
   (where (Listof τ_elem) τ)
   (WT σ Γ e τ)
   --- T-RestT
   (WT σ Γ (rest e) τ)]
  [
   (WT σ Γ e TST)
   --- T-RestU
   (WT σ Γ (rest e) TST)]
  [
   (WT σ Γ e τ)
   --- T-Union
   (WT σ Γ e (U τ_0 ... τ τ_1 ...))]
  [
   (WT σ Γ e #{mu-fold (μ (α) τ)})
   --- T-Rec
   (WT σ Γ e (μ (α) τ))]
  [
   (WT σ Γ e τ) ;; thank you redex
   --- T-Forall
   (WT σ Γ e (∀ (α) τ))]
  [
   (<: τ_mon τ) ;; (<: _ TST) undefined
   (WT σ Γ v TST)
   --- T-MonFunT
   (WT σ Γ (mon-fun τ_mon v) τ)]
  [
   (WT σ Γ v τ_mon)
   --- T-MonFunU
   (WT σ Γ (mon-fun τ_mon v) TST)]
  [
   (<: τ_mon τ) ;; (<: _ TST) undefined
   (WT σ Γ v TST)
   --- T-MonVectorT
   (WT σ Γ (mon-vector τ_mon v) τ)]
  [
   (WT σ Γ v τ_mon)
   --- T-MonVectorU
   (WT σ Γ (mon-vector τ_mon v) TST)]
  [
   (<: τ_chk τ)
   (WT σ Γ e TST)
   --- T-Boundary0
   (WT σ Γ (from-untyped τ_chk e) τ)]
  [
   (WT σ Γ e τ_pro)
   --- T-Boundary1
   (WT σ Γ (from-typed τ_pro e) TST)])

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
   ;(same-domain ρ Γ) ;; it's OK if Γ is missing some entries
   ;; TODO can't require dom(ρ) = dom(Γ), because Γ has names for mutally-recursive
   ;;      defines but ρ doesn't ... these aren't ready at runtime yet
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
   (where (x_0 τ) #{unsafe-env-ref Γ x_0 #false})
   (WT σ Γ v_0 τ)
   (local-value-env-models-aux σ (x:v_rest ...) Γ)
   ---
   (local-value-env-models-aux σ ((x_0 v_0) x:v_rest ...) Γ)])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "WT"
    (check-judgment-holds*
     (WT () () 4 Nat)
     (WT () () 4 TST)
     (WT () () -4 Int)
     (WT () () -4 TST)
     (WT () ((x Int)) x Int)
     (WT () ((x TST)) x TST)
     (WT () () (fun f (→ Nat Nat) (x) x) (→ Nat Nat))
     (WT () () (fun f (x) x) TST)
     (WT ((qq (1 2))) () (vector (Vectorof Int) qq) (Vectorof Int))
     (WT ((qq (1 2))) () (vector qq) TST)
     (WT () () (make-vector (Vectorof Int) 1 2) (Vectorof Int))
     (WT () () (make-vector 1 2) TST)
     (WT () () (cons 1 nil) (Listof Nat))
     (WT () () (cons 1 nil) TST)
     (WT () () nil (Listof Nat))
     (WT () () nil TST)
     (WT () ((f (→ Int Int))) (f -6) Int)
     (WT () ((f TST)) (f f) TST)
     (WT () () (3 3) TST)
     (WT () () (ifz 0 1 2) Nat)
     (WT () () (ifz nil nil nil) TST)
     (WT () () (+ -1 2) Int)
     (WT () () (+ 3 2) Nat)
     (WT () () (+ 4 4) TST)
     (WT () () (+ nil nil) TST)
     (WT () () (- 3 3) Int)
     (WT () () (- 3 3) TST)
     (WT () () (- 3 nil) TST)
     (WT () () (* 3 -3) Int)
     (WT () () (* 3 3) Nat)
     (WT () () (* 3 3) TST)
     (WT () () (* nil 4) TST)
     (WT () () (% -6 2) Int)
     (WT () () (% 6 2) Nat)
     (WT () () (% 6 2) TST)
     (WT () () (% nil nil) TST)
     (WT () () (vector-ref (make-vector (Vectorof Int) 2 3) 0) Int)
     (WT () () (vector-ref (make-vector 3) 0) TST)
     (WT () () (vector-set! (make-vector (Vectorof Int) 2 3) 0 -3) Int)
     (WT () () (vector-set! (make-vector 2) 0 nil) TST)
     (WT () () (first nil) Nat)
     (WT () () (first (cons 1 nil)) Int)
     (WT () () (first 3) TST)
     (WT () () (rest nil) (Listof Int))
     (WT () () (rest (cons 1 nil)) (Listof Int))
     (WT () () (rest 4) TST)
     (WT () () 4 (U Nat (→ Nat Nat)))
     (WT () () (fun f (∀ (α) (→ α α)) (x) x) (∀ (α) (→ α α)))
     (WT () () (mon-fun (→ Nat Nat) (fun f (x) 3)) (→ Nat Nat))
     (WT () () (mon-fun (→ Nat Nat) (fun f (→ Nat Nat) (x) 3)) TST)
     (WT ((qq (1 2))) () (mon-vector (Vectorof Int) (vector qq)) (Vectorof Int))
     (WT ((qq (2))) () (mon-vector (Vectorof Int) (vector (Vectorof Int) qq)) TST)
     (WT () () (from-untyped Int (+ 3 3)) Int)
     (WT () () (from-typed Int (+ 3 3)) TST)
     (WT () () (mon-fun (→ Int (→ Int Int))
                 (fun a (x)
                   (fun b (y)
                     (fun c (z) (+ (+ x y) z)))))
               (→ Int (→ Int Int)))
    )

    (check-not-judgment-holds*
     (WT () () -4 Nat)
     (WT () () nil Int)
     (WT () ((x Int)) x TST)
     (WT () () (fun f (x) x) (→ Nat Nat)) ;; missing type annotation
     (WT () () (make-vector 1 2) (Vectorof Nat))
     (WT () ((f (→ Int Int))) (f -6) TST)
     (WT () () (ifz nil 1 2) Nat)
     (WT () () (- 3 0) Nat)
     (WT () () (* -3 -3) Nat)
     (WT () () (vector-ref (make-vector 3) 0) Int)
     (WT () () (vector-set! (make-vector Nat 2 3) 0 -3) Int)
     (WT () () (from-untyped Int (+ 3 3)) TST)
     (WT () () (from-typed Int (+ 3 3)) Int)
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
     (local-value-env-models
       ()
       ((x (mon-fun (→ Nat Nat) (fun f (z) (+ z 3)))))
       ((x (→ Nat Nat))))
     (local-value-env-models () () ((x Int)))
    )

    (check-not-judgment-holds*
     (local-value-env-models () ((x 4)) ((y Int)))
     (local-value-env-models () ((x 4) (y -1)) ((x Int) (y Nat)))
     (local-value-env-models () ((x (fun f (z) (+ z 3)))) ((x (→ Nat Nat))))
    )
  )

  (test-case "well-typed-state"
    (check-judgment-holds*
     (well-typed-state (() (+ nil 2)) TST)
     (well-typed-state (() (+ 2 2)) Nat)
     (well-typed-state (((qq (1 2))) (vector (Vectorof Nat) qq))
                        (Vectorof Nat))
     (well-typed-state (() (* 4 4)) TST)
    )

    (check-not-judgment-holds*
     (well-typed-state (() (+ nil 2)) Int)
     (well-typed-state (((qq (1 -2))) (vector (Vectorof Nat) qq)) (Vectorof Nat))
    )
  )

  (test-case "well-typed-answer"
    (check-judgment-holds*
     (well-typed-answer (BE Int nil) Int)
     (well-typed-answer DivisionByZero Int)
     (well-typed-answer EmptyList TST)
     (well-typed-answer (TE 4 (Listof Int)) TST)
     (well-typed-answer (TE 4 (Listof Int)) (Listof Int))
     (well-typed-answer (() (+ 2 2)) TST)
     (well-typed-answer (() (+ 2 nil)) TST)
     (well-typed-answer (() (+ 2 2)) Int)
     (well-typed-answer (() 16) TST)
    )

    (check-not-judgment-holds*
     (well-typed-answer (() (+ nil 2)) Int)
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
     ((sound-eval-typed-expression# ((f (→ Int Nat))) () ((f (mon-fun (→ Int Nat) (fun f (x) x)))) (f 42) Nat)
      (() 42))
     ((sound-eval-typed-expression# ((f (→ Int Nat))) () ((f (mon-fun (→ Int Nat) (fun f (x) (cons 1 nil))))) (f 42) Nat)
      (BE Nat (cons 1 nil)))
     ((sound-eval-typed-expression# ((f (→ Int Nat))) () ((f (mon-fun (→ Int Nat) (fun f (x) (x x))))) (f 42) Nat)
      (TE 42 "procedure?"))
    )

    ;; `check` is not part of the source language
    (check-exn exn:fail:contract?
      (λ () (term #{sound-eval-typed-expression# () () () (from-untyped Int nil) Int})))
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
     (toplevel-value-env-models ((qq (0 1 2)))
                                ((M0 ((x (mon-vector (Vectorof Nat) (vector qq))))))
                                ((M0 ((x (Vectorof Nat))))))
    )

    (check-not-judgment-holds*
     (toplevel-value-env-models () ((M0 ())) ((M1 ())))
     (toplevel-value-env-models () ((M0 ())) ())
     (toplevel-value-env-models () ()        ((M1 ())))
    )
  )

  (test-case "sound-eval-program:I"
    (define-term P
      ((module M0 untyped
        (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ x y) z)))))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int (→ Int Int)))))
        (provide f))
       (module M2 untyped
        (require M1 f)
        (define f2 (f 2))
        (define f23 (f2 3))
        (provide))))
    (check-pred values
      (term #{well-typed-program# P}))
    (check-exn #rx"BE"
     (λ () (term #{sound-eval-program# P})))
  )

  (test-case "sound-eval-program:II"
    (check-mf-apply*
     ((sound-eval-program#
       ((module M0 untyped
         (define nums (cons -1 (cons -2 nil)))
         (provide nums))
        (module M1 typed
         (require M0 ((nums (Listof Int))))
         (define a Int (+ (first nums) (first (rest nums))))
         (provide a))))
      (() ((M0 ((nums (cons -1 (cons -2 nil)))))
           (M1 ((a -3))))))
    )
  )
)
