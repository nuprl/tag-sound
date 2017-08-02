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
  (ve ::= integer boolean (fun f (x : τ) e))
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
  (φ ::= ++ -- x)
  (κ ::= int bool proc box)
  (Γ ::= ((x τφ) ...))
  (RuntimeError ::= DivisonByZero)
  (CheckError ::= (CheckError v κ))
  (A ::= e RuntimeError CheckError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (fun f (x : τ) e #:refers-to (shadow f x))
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
   (type=? τ τ_c)
   (tag-of τ_c κ)
   (where c_+ (check κ c))
   ---
   (check-type Γ e τ c_+)])

(define-judgment-form TAG
  #:mode (infer-type I I O O)
  #:contract (infer-type Γ e c τφ)
  [
   ---
   (infer-type Γ e 0 (Integer ++))]
)

(define-judgment-form TAG
  #:mode (tag-of I O)
  #:contract (tag-of τ κ)
  [
   ---
   (tag-of τ int)]
)

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
   (flag++ τφ)]
)

(define-judgment-form TAG
  #:mode (flag-- I)
  #:contract (flag-- τφ)
  [
   ---
   (flag-- τφ)]
)

(define-judgment-form TAG
  #:mode (erase-φ I O)
  #:contract (erase-φ τφ τ)
  [
   ---
   (erase-φ τφ Integer)]
)

(define-judgment-form TAG
  #:mode (type=? I I)
  #:contract (type=? τ τ)
  [
   ---
   (type=? τ τ)])

