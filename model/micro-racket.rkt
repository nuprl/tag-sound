#lang mf-apply racket/base

;; Model of Typed Racket,
;;  showing difference between type soundness and tag soundness semantics.

;; Outline:
;; - one source language, looks like Typed Racket
;; - three semantics,
;;   * type sound
;;   * tag sound
;;   * unsound
;; proofs of type and tag soundness

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs
  (only-in racket/string string-split))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; -----------------------------------------------------------------------------

(define-language++ μTR #:alpha-equivalent? α=?
  (τ ::= Int Nat (→ τ τ) (Vectorof τ) (Listof τ)
         (U τ ...) (∀ (α) τ) (μ (α) τ))
  ;; Types,
  ;; - simple types with non-trivial subtyping
  ;; - parameterized types with covariant, contravariant, and invariant positions
  ;; - unions, universals, and recursives because they have non-obvious tags

  (κ ::= Int Nat → Vector List (U κ ...))
  ;; Tags,
  ;; - one for each base type
  ;; - one for each value constructor
  ;; Purpose: so partial functions can check their inputs.
  ;;  the reduction relation uses tag-checks to make partial functions total

  (P ::= (M ...))
  (M ::= (module-λ x Rλ ... Dλ ... P ...)
         (module-τ x Rτ ... Dτ ... P ...))
  (Rλ ::= (require x x ...))
  (Rτ ::= (require/typed x [x τ] ...))
  (Dλ ::= (define x eλ))
  (Dτ ::= (define x eτ))
  (P ::= (provide x ...))
  ;; Programs

  (eλ ::= integer (fun x (x) eλ) (vector eλ ...) (cons eλ eλ)
          (ifz eλ eλ eλ)
          (+ eλ eλ) (- eλ eλ) (* eλ eλ) (% eλ eλ) (vector-ref eλ eλ) (vector-set! eλ eλ eλ) (first eλ) (rest eλ))
  (eτ ::= integer (fun x τ (x) eτ) (vector eτ ...) (cons eτ eτ)
          (ifz eτ eτ eτ)
          (+ eτ eτ) (- eτ eτ) (* eτ eτ) (% eτ eτ) (vector-ref eτ eτ) (vector-set! eτ eτ eτ) (first eτ) (rest eτ))
)

;  (τ ::= (U τk ...) τk TST)
;  (τk ::= Int Bool (Pair τ τ) (→ τ τ) (Box τ))
;  (L ::= R T)
;  (Γ ::= ((x τ) ...))
;  (ρ ::= (RB ...))
;  (RB ::= (x (BOX v)) (x UNDEF) (x (LETREC v)))
;  (primop ::= car cdr binop =)
;  (binop ::= + * -)
;  (tag ::= tagk (U tagk ...))
;  (tagk ::= Int Bool Pair → Box)
;  (E ::= hole
;         (E e) (v E) (if E e e) (and E e) (let (x E) e) (letrec (x E) e)
;         (cons E e) (cons v E)
;         (car E) (cdr E)
;         (binop E e) (binop v E)
;         (= E e) (= v E)
;         (make-box E) (set-box! E e) (set-box! v E) (unbox E)
;         (dyn-check tag E srcloc)
;         (pre-mon L τ (L E) srcloc))
;  (RuntimeError ::= (DynError tag v srcloc) (BoundaryError L τ P srcloc) (UndefError x))
;  (srcloc ::= (path-elem srcloc) (unbox τ) (set-box! τ) (primop τ) (x τ))
;  (path-elem ::= dom cod car cdr unbox set-box! (proj natural))
;  (A ::= [ρ e] RuntimeError)
;  (x ::= variable-not-otherwise-mentioned)
;#:binding-forms
;  (let (x τ P) e #:refers-to x)
;  (letrec (x τ e_L #:refers-to x) e #:refers-to x)
;  (letrec (x τ (L e_L #:refers-to x)) e #:refers-to x)
;  ;; the 3rd letrec is NOT a binding form, needs to cooperate with enclosing environment
;  (λ (x) e #:refers-to x)
;  (λ (x τ) e #:refers-to x))
;
;;; -----------------------------------------------------------------------------
