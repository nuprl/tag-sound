#lang mf-apply racket/base

;; Workspace for a type sound RST, based on simply-typed λ calculus

;; TODO
;; - substitution lemma (anything hard here?)
;; - mon, need to remember more things????
;; - mon, why/how not nested???
;; - lemma `∀L . ⊢L mon(t,e,L+) : t`

;; - (check-type (T e) τ)
;;   implies (check-type (S e) τ)
;;   implies (check-type (R e) τ)
;; - 

;; =============================================================================

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse))
)

;; =============================================================================

;; Simple [Racket Shallow Typed] language
(define-language RST
  (e ::= v (e e) x (let (x τ P) e) (+ e e) (= e e) (if e e e) (and e e) (mon L τ P) (pre-mon L τ P))
  (v ::= integer boolean (λ (x τ) e) (mon L τ (L v)))
  (P ::= (L e))
  (τ ::= Int Bool (Pair τ τ) (→ τ τ) TST)
  (L ::= R S T)
  (L\R ::= S T)
  (Γ ::= ((x τ) ...))
  (E ::= hole
         (E e) (v E)
         (+ E e) (+ v E)
         (= E e) (= v E)
         (if E e e)
         (and E e))
  (x ::= (variable-not-otherwise-mentioned))
#:binding-forms
  (λ (x τ) e #:refers-to x))

;; -----------------------------------------------------------------------------
;; --- check-type

(define-judgment-form RST
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (S e) #{tag-only τ})
   ---
   (check-type Γ (S e) τ)]
  [
   (infer-type Γ (T e) τ)
   ---
   (check-type Γ (T e) τ)])

(define-judgment-form RST
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P TST)
  [
   ---
   (infer-type Γ (R integer) TST)]
  [
   ---
   (infer-type Γ (L\R integer) Int)]
  [
   ---
   (infer-type Γ (R boolean) TST)]
  [
   ---
   (infer-type Γ (L\R boolean) TST)]
;  [
;   (where Γ_x #{type-env-set Γ (x τ)})
;   (infer-type-R Γ_x e TST)
;   ---
;   (infer-type-R Γ (λ (x τ) e) TST)]
;  [
;   (infer-type-R Γ e_0 TST)
;   (infer-type-R Γ e_1 TST)
;   ---
;   (infer-type-R Γ (e_0 e_1) TST)]
;  [
;   (where τ #{type-env-ref Γ x})
;   ---
;   (infer-type-R Γ x TST)]
;  [
;   (check-type Γ P τ)
;   (where Γ_x #{type-env-set Γ (x τ)})
;   (infer-type-R Γ_x e TST)
;   ---
;   (infer-type-R Γ (let (x τ P) e) TST)]
;  [
;   (infer-type-R Γ e_0 TST)
;   (infer-type-R Γ e_1 TST)
;   ---
;   (infer-type-R Γ (+ e_0 e_1) TST)]
;  [
;   (infer-type-R Γ e_0 TST)
;   (infer-type-R Γ e_1 TST)
;   ---
;   (infer-type-R Γ (= e_0 e_1) TST)]
;  [
;   (infer-type-R Γ e_0 TST)
;   (infer-type-R Γ e_1 TST)
;   (infer-type-R Γ e_2 TST)
;   ---
;   (infer-type-R Γ (if e_0 e_1 e_2) TST)]
;  [
;   (infer-type-R Γ e_0 TST)
;   (infer-type-R Γ e_1 TST)
;   ---
;   (infer-type-R Γ (and e_0 e_1) TST)]
;  [
;   (check-type P τ) ;; maybe too strict
;   ---
;   (infer-type-R Γ (mon R τ P) TST)]
;  [
;   (check-type P τ)
;   ---
;   (infer-type-R Γ (pre-mon R τ P) TST)]
)

;;(define-judgment-form RST
;;  #:mode (infer-type-S I I I)
;;  #:contract (infer-type-S Γ e τ)
;;  [
;;   ---
;;   (infer-type-S Γ integer Int)]
;;  [
;;   ---
;;   (infer-type-S Γ boolean Bool)]
;;  [
;;   (where Γ_x #{type-env-set Γ (x τ_dom)})
;;   (infer-type-S Γ_x e τ_cod)
;;   ---
;;   (infer-type-S Γ (λ (x τ_dom) e) (→ τ_dom τ_cod))]
;;  [
;;   (infer-type-S Γ e_0 (→ τ_dom τ_cod))
;;   (infer-type-S Γ e_1 τ_1)
;;   (type= τ_dom τ_1)
;;   ---
;;   (infer-type-S Γ (e_0 e_1) τ_cod)]
;;  [
;;   (where τ #{type-env-ref Γ x})
;;   ---
;;   (infer-type-S Γ x τ)]
;;  [
;;   (check-type P τ)
;;   (where Γ_x #{type-env-set Γ (x τ)})
;;   (infer-type-S Γ_x e τ_e)
;;   ---
;;   (infer-type-S Γ (let (x τ P) e) τ_e)]
;;  [
;;   (infer-type-S Γ e_0 Int)
;;   (infer-type-S Γ e_1 Int)
;;   ---
;;   (infer-type-S Γ (+ e_0 e_1) Int)]
;;  [
;;   (infer-type-S Γ e_0 Int)
;;   (infer-type-S Γ e_1 Int)
;;   ---
;;   (infer-type-S Γ (= e_0 e_1) Bool)]
;;  [
;;   (infer-type-S Γ e_0 τ_0)
;;   (infer-type-S Γ e_1 τ_1)
;;   (infer-type-S Γ e_2 τ_2)
;;   (type= τ_1 τ_2)
;;   ---
;;   (infer-type-S Γ (if e_0 e_1 e_2) τ_2)]
;;  [
;;   (infer-type-S Γ e_0 Bool)
;;   (infer-type-S Γ e_1 Bool)
;;   ---
;;   (infer-type-S Γ (and e_0 e_1) Bool)]
;;  [
;;   (check-type P τ) ;; maybe too strict
;;   ---
;;   (infer-type-S Γ (mon S τ P) τ)]
;;  [
;;   (check-type P τ)
;;   ---
;;   (infer-type-S Γ (pre-mon S τ P) τ)]
;;)
;;
;;(define-judgment-form RST
;;  #:mode (check-type-T I I I)
;;  #:contract (check-type-T Γ e τ)
;;)

;; -----------------------------------------------------------------------------
;; --- infer-type

;; -----------------------------------------------------------------------------
;; --- type helpers

(define-metafunction RST
  tag-only : τ -> τ
  [(tag-only Int)
   Int]
  [(tag-only Bool)
   Bool]
  [(tag-only (Pair τ_0 τ_1))
   (Pair TST TST)]
  [(tag-only (→ τ_dom τ_cod))
   (→ TST TST)]
  [(tag-only TST)
   TST])

(define-metafunction RST
  coerce-→ : τ -> τ
  [(coerce-→ TST)
   (→ TST TST)]
  [(coerce-→ (→ τ_dom τ_cod))
   (→ τ_dom τ_cod)]
  [(coerce-→ τ)
   ,(raise-argument-error 'coerce-→ "cannot coerce ~a" (term τ))])

(define-judgment-form RST
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   --- Refl
   (type= τ τ)])

(module+ test
  (test-case "tag-only"
    (check-mf-apply*
     ((tag-only Int)
      Int)
     ((tag-only (→ Int Bool))
      (→ TST TST))
     ((tag-only (Pair (→ Int Int) Bool))
      (Pair TST TST))))

  (test-case "coerce-→"
    (check-mf-apply*
     ((coerce-→ (→ Int Bool))
      (→ Int Bool))
     ((coerce-→ TST)
      (→ TST TST))))
)

;; -----------------------------------------------------------------------------
;; --- environment helpers

(define-metafunction RST
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction RST
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

;; -----------------------------------------------------------------------------
;; --- evalution

;; simple rule for application
;; - if e0 not value then step
;; - if e1 not value then step
;; - if L_ctx = R and v0 not λ then die
;; - if L_ctx finer-than L_λ then mon(t_cod (e[x ↦ mon(t_dom v1 L_ctx)]) L_λ)
;; - if L_ctx coarser-than L_λ then e[x ↦ mon(t_dom v1 L_ctx)]
;; - else e[x ↦ v1]

;; lang(mon _ _ L) = L
;; lang(_) = L_ctx

;; typeof(mon τ _ _) = τ
;; typeof(_) = τ0 or (TST → TST)

;; -----------------------------------------------------------------------------
;; --- examples

;; Assume type-checked,
;; ((λR f . f) (λS x . (+ x 1))) :: String->String
;; --> (mon [String->String] R ((λ f . f) (mon [Int->Int] (λS x . (+ x 1)))))
;; --> (mon [String->String] R (mon [Int->Int] (λS x . (+ x 1))))
;; --> (mon [String->String] R (λS x . (+ x 1)))
;; ??? why does/should this work ??!
