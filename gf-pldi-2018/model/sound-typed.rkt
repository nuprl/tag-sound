#lang mf-apply racket/base

;; Soundness for Typed Racket semantics
;; i.e. theorems connecting the typechecker to the reduction semantics

;; Theorems:
;; - program soundness
;;   * if PROGRAM well-typed at TYPE-ENV
;;   * then reduces to a VAL-ENV
;;   * and VAL-ENV models TYPE-ENV
;;   * (ignore the σ)
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

;; Just do expressions for now, everything else should follow.

;; -----------------------------------------------------------------------------

(require
  "eval-common.rkt"
  "eval-typed.rkt"
  "lang.rkt"
  "grammar.rkt"
  "metafunctions.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

(define-metafunction μTR
  sound-eval-expression# : Γ σ ρ L e τ -> A
  [(sound-eval-expression# Γ σ ρ L e τ)
   A
   (judgment-holds (sound-eval-expression Γ σ ρ L e τ A))])

(define-judgment-form μTR
  #:mode (sound-eval-expression I I I I I I O)
  #:contract (sound-eval-expression Γ σ ρ L e τ A)
  [
   ;; Check premises
   (well-typed-expression Γ e τ)
   (local-value-env-models σ ρ Γ)
   ;; Do checked evaluation
   (where Σ_0 #{load-expression L σ ρ e})
   (where A #{sound-step* Σ_0 τ})
   ---
   (sound-eval-expression Γ σ ρ L e τ A)])

(define-metafunction μTR
  sound-step* : Σ τ -> A
  [(sound-step* Σ τ)
   ,(if (term boolean_+)
      (term #{sound-step* A_+ τ})
      (term A_+))
   (judgment-holds (sound-step Σ τ A_+ boolean_+))]
  [(sound-step* A τ)
   ,(raise-arguments-error 'sound-step* "undefined for arguments"
      "config" (term A)
      "type" (term τ))])

(define-judgment-form μTR
  #:mode (sound-step I I O O)
  #:contract (sound-step Σ τ A boolean)
  [
   (well-typed-config Σ τ)
   (where (A boolean) ,(do-single-step (term Σ)))
   (well-typed-answer Σ A τ)
   ---
   (sound-step Σ τ A boolean)])

;; Apply reduction relation, make sure get 1 thing out of it
(define (do-single-step Σ)
  (define A* (apply-reduction-relation single-step Σ))
  (cond
   [(null? A*)
    (list Σ #false)]
   [(not (null? (cdr A*)))
    (raise-arguments-error 'do-single-step "non-deterministic step"
      "config" Σ
      "next configs" A*)]
   [else
    (list (car A*) #false)]))

(define-judgment-form μTR
  #:mode (well-typed-answer I I I)
  #:contract (well-typed-answer Σ A τ)
  [
   ---
   (well-typed-answer _ BoundaryError _)]
  [
   ;; TODO for now this is just "okay" ..
   ;;  need a theorem that typed contexts cannot throw type errors
   ---
   (well-typed-answer _ TypeError _)]
  [
   (well-typed-config Σ_+ τ)
   ---
   (well-typed-answer Σ Σ_+ τ)])

(define-judgment-form μTR
  #:mode (well-typed-config I I)
  #:contract (well-typed-config Σ τ)
  [
   (WT () #{unload-store/expression e σ} TST)
   ---
   (well-typed-config (UN σ e) TST)]
  [
   (WT () #{unload-store/expression e σ} τ)
   ---
   (well-typed-config (TY σ e) τ)])

;; "well-typed-expression" is the obvious name,
;;  but already using that for the static typing system
(define-judgment-form μTR
  #:mode (WT I I I)
  #:contract (WT Γ e τ)
  [
   --- T-NatT
   (WT Γ natural Nat)]
  [
   --- T-NatU
   (WT Γ natural TST)]
  [
   --- T-IntT
   (WT Γ integer Int)]
  [
   --- T-IntU
   (WT Γ integer TST)]
  [
   (where [_ τ_0] #{local-type-env-ref Γ x})
   (<: τ_0 τ)
   --- T-VarT
   (WT Γ x τ)]
  [
   (where [_ TST] #{local-type-env-ref Γ x})
   --- T-VarU
   (WT Γ x TST)]
  [
   (<: τ τ_fun)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (where Γ_f #{local-type-env-set Γ x_f τ})
   (where Γ_x #{local-type-env-set Γ_f x_arg τ_dom})
   (WT Γ_x e_body τ_cod)
   --- T-FunT
   (WT Γ (fun x_f τ_fun (x_arg) e_body) τ)]
  [
   (where Γ_f #{local-type-env-set Γ x_f TST})
   (where Γ_x #{local-type-env-set Γ_f x_arg TST})
   (WT Γ_x e_body TST)
   --- T-FunU
   (WT Γ (fun x_f (x_arg) e_body) TST)]
  [
   (<: τ_vec τ)
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (WT Γ e τ_elem) ...
   --- T-VecT
   (WT Γ (vector τ_vec e ...) τ)]
  [
   (WT Γ e TST) ...
   --- T-VecU
   (WT Γ (vector e ...) TST)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   (WT Γ e_0 τ_elem)
   (WT Γ e_1 τ)
   --- T-ConsT
   (WT Γ (cons e_0 e_1) τ)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   --- T-ConsU
   (WT Γ (cons e_0 e_1) TST)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   --- T-NilT
   (WT Γ nil τ)]
  [
   --- T-NilU
   (WT Γ nil TST)]
  [
   (infer-expression-type Γ e_fun τ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (WT Γ e_fun τ)
   (WT Γ e_arg τ_dom)
   --- T-AppT
   (WT Γ (e_fun e_arg) τ_cod)]
  [
   (WT Γ e_fun TST)
   (WT Γ e_arg TST)
   --- T-AppU
   (WT Γ (e_fun e_arg) TST)]
  [
   (WT Γ e_0 Int)
   (WT Γ e_1 τ)
   (WT Γ e_2 τ)
   --- T-IfzT
   (WT Γ (ifz e_0 e_1 e_2) τ)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   (WT Γ e_2 TST)
   --- T-IfzU
   (WT Γ (ifz e_0 e_1 e_2) TST)]
  [
   (WT Γ e_0 Int)
   (WT Γ e_1 Int)
   --- T-PlusT0
   (WT Γ (+ e_0 e_1) Int)]
  [
   (WT Γ e_0 Nat)
   (WT Γ e_1 Nat)
   --- T-PlusT1
   (WT Γ (+ e_0 e_1) Nat)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   --- T-PlusU
   (WT Γ (+ e_0 e_1) TST)]
  [
   (WT Γ e_0 Int)
   (WT Γ e_1 Int)
   --- T-MinusT
   (WT Γ (- e_0 e_1) Int)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   --- T-MinusU
   (WT Γ (- e_0 e_1) TST)]
  [
   (WT Γ e_0 Int)
   (WT Γ e_1 Int)
   --- T-TimesT0
   (WT Γ (* e_0 e_1) Int)]
  [
   (WT Γ e_0 Nat)
   (WT Γ e_1 Nat)
   --- T-TimesT1
   (WT Γ (* e_0 e_1) Nat)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   --- T-TimesU
   (WT Γ (* e_0 e_1) TST)]
  [
   (WT Γ e_0 Int)
   (WT Γ e_1 Int)
   --- T-DivideT0
   (WT Γ (% e_0 e_1) Int)]
  [
   (WT Γ e_0 Nat)
   (WT Γ e_1 Nat)
   --- T-DivideT1
   (WT Γ (% e_0 e_1) Nat)]
  [
   (WT Γ e_0 TST)
   (WT Γ e_1 TST)
   --- T-DivideU
   (WT Γ (% e_0 e_1) TST)]
  [
   (WT Γ e_vec (Vectorof τ))
   (WT Γ e_i Int)
   --- T-RefT
   (WT Γ (vector-ref e_vec e_i) τ)]
  [
   (WT Γ e_vec TST)
   (WT Γ e_i TST)
   --- T-RefU
   (WT Γ (vector-ref e_vec e_i) TST)]
  [
   (WT Γ e_vec (Vectorof τ))
   (WT Γ e_i Int)
   (WT Γ e_val τ)
   --- T-SetT
   (WT Γ (vector-set! e_vec e_i e_val) τ)]
  [
   (WT Γ e_vec TST)
   (WT Γ e_i TST)
   (WT Γ e_val TST)
   --- T-SetU
   (WT Γ (vector-set! e_vec e_i e_val) TST)]
  [
   (WT Γ e (Listof τ))
   --- T-FirstT
   (WT Γ (first e) τ)]
  [
   (WT Γ e TST)
   --- T-FirstU
   (WT Γ (first e) TST)]
  [
   (where (Listof τ_elem) τ)
   (WT Γ e τ)
   --- T-RestT
   (WT Γ (rest e) τ)]
  [
   (WT Γ e TST)
   --- T-RestU
   (WT Γ (rest e) TST)]
  [
   (WT Γ e τ)
   --- T-Union
   (WT Γ e (U τ_0 ... τ τ_1 ...))]
  [
   (WT Γ e #{mu-fold (μ (α) τ)})
   --- T-Rec
   (WT Γ e (μ (α) τ))]
  [
   (WT Γ e τ) ;; thank you redex
   --- T-Forall
   (WT Γ e (∀ (α) τ))]
  [
   (side-condition ,(raise-user-error 'T-MonFunT "got monitor in typed code ~a" (term (mon-fun τ_mon v))))
   --- T-MonFunT
   (WT Γ (mon-fun τ_mon v) τ)]
  [
   (WT Γ v τ_mon)
   --- T-MonFunU
   (WT Γ (mon-fun τ_mon v) TST)]
  [
   (side-condition ,(raise-user-error 'T-MonVectorT "got monitor in typed code ~a" (term (mon-vector τ_mon v))))
   --- T-MonVectorT
   (WT Γ (mon-vector τ_mon v) τ)]
  [
   (WT Γ v τ_mon)
   --- T-MonVectorU
   (WT Γ (mon-vector τ_mon v) TST)]
  [
   (<: τ_chk τ)
   (WT Γ e TST)
   --- T-Check
   (WT Γ (check τ_chk e) τ)]
  [
   (WT Γ e τ_pro)
   --- T-Protect
   (WT Γ (protect τ_pro e) TST)])

(define-judgment-form μTR
  #:mode (local-value-env-models I I I)
  #:contract (local-value-env-models σ ρ Γ)
  [
   (same-domain ρ Γ) ;; it's OK if Γ is missing some entries
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
   (where (x_0 τ) #{local-type-env-ref Γ x_0})
   (WT Γ v_0 τ)
   (local-value-env-models-aux σ (x:v_rest ...) Γ)
   ---
   (local-value-env-models-aux σ ((x_0 v_0) x:v_rest ...) Γ)])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "WT"
  )

  (test-case "local-value-env-models"
  )

  (test-case "well-typed-config"
  )

  (test-case "well-typed-answer"
  )

  (test-case "sound-step"
  )

  (test-case "sound-eval-expression"
  )

)
