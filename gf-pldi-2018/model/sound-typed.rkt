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
   (WT σ () e TST)
   ---
   (well-typed-config (UN σ e) TST)]
  [
   (WT σ () e τ)
   ---
   (well-typed-config (TY σ e) τ)])

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
   (where (vector τ x) v)
   (WT σ Γ #{unload-store/expression v σ} τ)
   --- T-VecValT
   (WT σ Γ v τ)]
  [
   (where (vector x) v)
   (WT σ Γ #{unload-store/expression v σ} TST)
   --- T-VecValU
   (WT σ Γ v TST)]
  [
   (not-VV σ (vector τ_vec e ...)) ;; TODO
   (<: τ_vec τ)
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (WT σ Γ e τ_elem) ...
   --- T-VecT
   (WT σ Γ (vector τ_vec e ...) τ)]
  [
   (not-VV σ (vector e ...)) ;; TODO
   (WT σ Γ e TST) ...
   --- T-VecU
   (WT σ Γ (vector e ...) TST)]
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
   (side-condition ,(not (equal? (term TST) (term τ))))
   (side-condition ,(raise-user-error 'T-MonFunT "got monitor in typed code ~a" (term (mon-fun τ_mon v))))
   --- T-MonFunT
   (WT σ Γ (mon-fun τ_mon v) τ)]
  [
   (WT σ Γ v τ_mon)
   --- T-MonFunU
   (WT σ Γ (mon-fun τ_mon v) TST)]
  [
   (side-condition ,(not (equal? (term TST) (term τ))))
   (side-condition ,(raise-user-error 'T-MonVectorT "got monitor in typed code ~a" (term (mon-vector τ_mon v))))
   --- T-MonVectorT
   (WT σ Γ (mon-vector τ_mon v) τ)]
  [
   (WT σ Γ v τ_mon)
   --- T-MonVectorU
   (WT σ Γ (mon-vector τ_mon v) TST)]
  [
   (<: τ_chk τ)
   (WT σ Γ e TST)
   --- T-Check
   (WT σ Γ (check τ_chk e) τ)]
  [
   (WT σ Γ e τ_pro)
   --- T-Protect
   (WT σ Γ (protect τ_pro e) TST)])

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
   (WT σ Γ v_0 τ)
   (local-value-env-models-aux σ (x:v_rest ...) Γ)
   ---
   (local-value-env-models-aux σ ((x_0 v_0) x:v_rest ...) Γ)])

(define-judgment-form μTR
  #:mode (not-VV I I)
  #:contract (not-VV σ e)
  [
   (side-condition ,(not (judgment-holds (VV σ e))))
   ---
   (not-VV σ e)])

(define-judgment-form μTR
  #:mode (VV I I)
  #:contract (VV σ e)
  [
   (where (x _) #{unsafe-env-ref σ x #false})
   ---
   (VV σ (vector x))]
  [
   (where (x _) #{unsafe-env-ref σ x #false})
   ---
   (VV σ (vector τ x))])

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "not-VV"
    (check-judgment-holds*
     (not-VV () (vector (Vectorof Int) 1 2))
    ))

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
     (WT () () (vector (Vectorof Int) 1 2) (Vectorof Int))
     (WT () () (vector 1 2) TST)
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
     (WT () () (vector-ref (vector (Vectorof Int) 2 3) 0) Int)
     (WT () () (vector-ref (vector 3) 0) TST)
     (WT () () (vector-set! (vector (Vectorof Int) 2 3) 0 -3) Int)
     (WT () () (vector-set! (vector 2) 0 nil) TST)
     (WT () () (first nil) Nat)
     (WT () () (first (cons 1 nil)) Int)
     (WT () () (first 3) TST)
     (WT () () (rest nil) (Listof Int))
     (WT () () (rest (cons 1 nil)) (Listof Int))
     (WT () () (rest 4) TST)
     (WT () () 4 (U Nat (→ Nat Nat)))
     (WT () () (fun f (∀ (α) (→ α α)) (x) x) (∀ (α) (→ α α)))
;;     (WT () () (mon-fun (→ Nat Nat) (fun f (x) 3)) (→ Nat Nat)) ;; TODO is this legal???
     (WT () () (mon-fun (→ Nat Nat) (fun f (→ Nat Nat) (x) 3)) TST)
;;     (WT ((qq (1 2))) () (mon-vector (Vectorof Int) (vector qq)) (Vectorof Int)) ;; TODO
     (WT ((qq (2))) () (mon-vector (Vectorof Int) (vector (Vectorof Int) qq)) TST)
     (WT () () (check Int (+ 3 3)) Int)
     (WT () () (protect Int (+ 3 3)) TST)
    )

    (check-not-judgment-holds*
     (WT () () -4 Nat)
     (WT () () nil Int)
     (WT () ((x Int)) x TST)
     (WT () () (fun f (x) x) (→ Nat Nat)) ;; missing type annotation
     (WT () () (vector 1 2) (Vectorof Nat))
     (WT () ((f (→ Int Int))) (f -6) TST)
     (WT () () (ifz nil 1 2) Nat)
     (WT () () (- 3 0) Nat)
     (WT () () (* -3 -3) Nat)
     (WT () () (vector-ref (vector 3) 0) Int)
     (WT () () (vector-set! (vector Nat 2 3) 0 -3) Int)
     (WT () () (check Int (+ 3 3)) TST)
     (WT () () (protect Int (+ 3 3)) Int)
    )
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
