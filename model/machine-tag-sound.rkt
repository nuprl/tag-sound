#lang mf-apply racket/base

;; Machine-tag-sound typed language.
;; Two theorems:
;; 1. SOUNDNESS === if Γ ⊢ e ⇓ c : τ then either:
;;   - c -->* v  and  τ ⊨ v
;;   - c diverges
;;   - c raises DivisionByZero
;;   - c raises CheckError(κ v)
;; 2. OPTIMIZATION === if e_0 ⊑ e_1 and e_1 -->* v then:
;;   - e_0 -->* v
;;   - e_0 <~ e_1
;;
;; Interpretation:
;; (1) is tag soundness, if you predict a type thats what you get
;;     though the program might end in a nondescript check error
;; (2) is "guaranteed optimization", if you add types the program will
;;     use fewer tag checks (the <~ relation is a kind of stepping simulation)

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs
  redex-abbrevs/unstable
  (only-in racket/string string-split))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; =============================================================================

(define-language++ TAG #:alpha-equivalent? α=?
  ;; --- e = source language
  (e ::= ve x (e e) (if e e e) (let (x τ φ e) e)
         (δ e ...))
  (ve ::= integer boolean (fun f τ τ (x) e))
  ;; eτ = intermediate language
  ;;;; (eτ ::= vτ (x : τφ) ((eτ eτ) : τφ) ((if eτ eτ eτ) : τφ)
  ;;;;         ((let (x τ eτ) eτ) : τφ)
  ;;;;         ((binop eτ eτ) : τφ) ((unop eτ) : τφ))
  ;;;; (vτ ::= (integer : τφ) (boolean : τφ) ((fun f (x : τφ) eτ) : τφ))
  ;; --- c = target language
  (c ::= ;; completions
         v x (c c) (if c c c) (let (x c) c)
         (δ c ...) (check κ c))
  (v ::= integer boolean (fun f (x) c))
  (δ ::= δ- δ+)
  (δ- ::= + / and or unbox set-box! int? bool? proc?)
  (δ+ ::= make-box)
  (binop ::= + / and or set-box!)
  ;; ---
  (τ ::= (U τ0 ...) τ0)
  (τ0 ::= Natural Integer Boolean (Box τ) (→ τ τ))
  (τφ ::= (U φ τφ0 ...) τφ0)
  (τφ0 ::= (Natural φ) (Integer φ) (Boolean φ) (Box φ τφ) (→ φ τφ τφ))
  (φ ::= ++ --)
  (κ ::= int bool proc box)
  (Γ ::= ((x τφ) ...))
  (RuntimeError ::= DivisonByZero)
  (CheckError ::= (CheckError v κ))
  (A ::= e RuntimeError CheckError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (fun f τ_dom τ_cod (x) e #:refers-to (shadow f x))
  (let (x τ φ e_x) e #:refers-to x)
  (fun f (x) c #:refers-to (shadow f x))
  (let (x c_x) c #:refers-to x)
)

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (check-type I I I O)
  #:contract (check-type Γ e τ c)
  [
   (infer-type Γ e c τφ_c)
   (flag++ τφ_c)
   (erase-φ τφ_c τ_c)
   (type=? τ τ_c)
   ---
   (check-type Γ e τ c)]
  [
   (infer-type Γ e c τφ_c)
   (flag-- τφ_c)
   (erase-φ τφ_c τ_c)
   (type=? τ τ_c) ;; IDK
   (tag-of τ_c κ)
   (where c_+ (check κ c))
   ---
   (check-type Γ e τ c_+)])

(define-judgment-form TAG
  #:mode (infer-type I I O O)
  #:contract (infer-type Γ e c τφ)
  [
   ---
   (infer-type Γ integer integer (Integer ++))]
  [
   ---
   (infer-type Γ boolean boolean (Boolean ++))]
  [
   (add-φ τ_dom -- τφ_dom)
   (where Γ_x #{type-env-add Γ x τφ_dom})
   ;; TODO need to add `f` to `Γ` ... but need to decide if τ_cod is present or absent
   (infer-type Γ_x e c τφ_cod)
   ---
   (infer-type Γ (fun f τ_dom τ_cod (x) e) (fun f (x) c) (→ ++ τφ_dom τφ_cod))]
  [
   (infer-type Γ e_0 c_0 (→ φ τφ_dom τφ_cod))
   (infer-type Γ e_1 c_1 τφ_1)
   (type=? τφ_dom τφ_1)
   (where c_0+ ,(if (judgment-holds (flag++ (→ φ τφ_dom τφ_cod)))
                  (term c_0)
                  (term (check proc c_0))))
   ---
   (infer-type Γ (e_0 e_1) (c_0+ c_1) τφ_dom)]
  [
   (infer-type Γ e_0 c_0 τφ_0)
   (infer-type Γ e_1 c_1 τφ_1)
   (infer-type Γ e_2 c_2 τφ_2)
   ---
   (infer-type Γ (if e_0 e_1 e_2) (if c_0 c_1 c_2) (U τφ_1 τφ_2))]
  ;[
  ; ;; TODO
  ; ---
  ; (infer-type Γ (let (x τ ++ e_x) e) (let (x c_x) c) τφ)]
)

(define-judgment-form TAG
  #:mode (tag-of I O)
  #:contract (tag-of τ0 κ)
  [
   ---
   (tag-of Natural int)]
  [
   ---
   (tag-of Integer int)]
  [
   ---
   (tag-of Boolean bool)]
  [
   ---
   (tag-of (Box τ) box)]
  [
   ---
   (tag-of (→ τ_0 τ_1) proc)])

(define -->TAG
  (reduction-relation TAG
    #:domain A
    [-->
      e
      42]))

(define -->*
  (make--->* -->TAG))

;; "term precision" ⊑
(define-judgment-form TAG
  #:mode (type-ann<=? I I)
  #:contract (type-ann<=? e e)
  [
   ---
   (type-ann<=? e_0 e_1)]
)

;; "more checks"
;; This is TOO SIMPLE ... really need a simulation & compare traces
(define-judgment-form TAG
  #:mode (checks<=? I I)
  #:contract (checks<=? c c)
  [
   ---
   (checks<=? c_0 c_1)]
)

;; -----------------------------------------------------------------------------

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (flag++ I)
  #:contract (flag++ τφ)
  [
   ---
   (flag++ (_ ++ τφ ...))])

(define-judgment-form TAG
  #:mode (flag-- I)
  #:contract (flag-- τφ)
  [
   ---
   (flag-- (_ -- τφ ...))])

(module+ test
  (test-case "flag++"
    (check-judgment-holds*
     (flag++ (Integer ++))
     (flag++ (Boolean ++))
     (flag++ (→ ++ (Integer ++) (Boolean --)))
     (flag++ (Box ++ (Integer --)))
    )
    (check-not-judgment-holds*
     (flag++ (Integer --))
     (flag++ (→ -- (Integer --) (Integer --)))
    )
  )

  (test-case "flag--"
    (check-judgment-holds*
     (flag-- (Integer --))
     (flag-- (→ -- (Integer --) (Integer --)))
    )
    (check-not-judgment-holds*
     (flag-- (Integer ++))
    )
  )
)

(define-judgment-form TAG
  #:mode (erase-φ I O)
  #:contract (erase-φ τφ τ)
  [
   ---
   (erase-φ (any φ) any)]
  [
   (erase-φ τφ_0 τ_0)
   (erase-φ τφ_1 τ_1) ...
   ---
   (erase-φ (any φ τφ_0 τφ_1 ...) (any τ_0 τ_1 ...))])

(define-judgment-form TAG
  #:mode (add-φ I I O)
  #:contract (add-φ τ φ τφ)
  [
   ---
   (add-φ Natural φ (Natural φ))]
  [
   ---
   (add-φ Integer φ (Integer φ))]
  [
   ---
   (add-φ Boolean φ (Boolean φ))]
  [
   (add-φ τ φ τφ)
   ---
   (add-φ (Box τ) φ (Box φ τφ))]
  [
   (add-φ τ_dom φ τφ_dom)
   (add-φ τ_cod φ τφ_cod)
   ---
   (add-φ (→ τ_dom τ_cod) φ (→ φ τφ_dom τφ_cod))])

(define-judgment-form TAG
  #:mode (type=? I I)
  #:contract (type=? any any)
  [
   (erase-φ τφ_0 τ_0)
   (erase-φ τφ_1 τ_1)
   (type=? τ_0 τ_1)
   ---
   (type=? τφ_0 τφ_1)]
  [
   ---
   (type=? τ τ)])

(module+ test
  (test-case "erase-φ"
    (check-judgment-holds*
     (erase-φ (Integer ++) Integer)
     (erase-φ (→ ++ (Integer ++) (Box -- (Integer --))) (→ Integer (Box Integer)))
    )
  )
)

(define-metafunction TAG
  type-env-add : Γ x τφ -> Γ
  [(type-env-add Γ x τφ)
   ,(cons (term (x τφ)) (term Γ))])

