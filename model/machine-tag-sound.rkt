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

;; YOU KNOW WHAT, STOP IT. Forget the IR for now.

(define-language++ TAG #:alpha-equivalent? α=?
  ;; --- e = source language
  (e ::= ve x (e e) (if e e e) (let (x ?τ e) e)
         (δ e ...))
  (ve ::= integer boolean (fun f (x : ?τ) e))
  ;; eτ = intermediate language
  ;;;; (eτ ::= vτ (x : ?τφ) ((eτ eτ) : ?τφ) ((if eτ eτ eτ) : ?τφ)
  ;;;;         ((let (x ?τ eτ) eτ) : ?τφ)
  ;;;;         ((binop eτ eτ) : ?τφ) ((unop eτ) : ?τφ))
  ;;;; (vτ ::= (integer : ?τφ) (boolean : ?τφ) ((fun f (x : ?τφ) eτ) : ?τφ))
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
  (?τ ::= Dyn τ)
  ;;;; (?τφ ::= Dyn ....)
  (τ ::= (U τ0 ...) τ0)
  (τ0 ::= (Natural φ) (Integer φ) (Boolean φ) (→ φ τ0 τ0))
  (φ ::= + - x)
  (κ ::= int bool proc)
  (Γ ::= ((x τ) ...))
  (RuntimeError ::= DivisonByZero)
  (CheckError ::= (CheckError v κ))
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (fun f (x : ?τ) e #:refers-to (shadow f x))
  (let (x ?τ e_x) e #:refers-to x)
  (fun f (x) c #:refers-to (shadow f x))
  (let (x c_x) c #:refers-to x)
)
