#lang mf-apply racket/base

;; The point of this model is to study contract insertion & boundaries.
;; I think the cross-boundary soudnenss is going to work fine,
;;  with R < S < T
;;  and interesting types
;; but the model is here to find out, before diving into the weeds of:
;; - TR contract generation
;; - TR type-driven rewriting
;; - actual boundaries
;; (keep a TODO list of Racket things!)

;; ---

;; - evaluate with context-aware CEK machine
;; - prove "soundness" for closed programs
;; - prove absence of certain errors in certain contexts

;; After CEK machine is good,
;;  note that its not practical do implement this way,
;;  you really have a "colorbind" CEK machine
;;  that you compile the other languages to.
;; No problemo, define translations and show machine equivalence.
;; Should be easy right ha ha ha.

;; PROPERTIES
;; - type soundness for closed T programs
;; - tag soundness for closed S programs
;; - safety for closed R programs
;; - bounds on where certain errors can occur
;;   T can error for bad R or bad S (eventually find witness of bad input)
;;   S can error for bad R or bad S (ditto, but based on tag checks so maybe different? yes different)
;;   R can error anywhere, might just be wrong like `(+ 1 "two")`
;; - simulation between interpreted code and colorbind-compiled code

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit-abbrevs rackunit
           (for-syntax racket/base racket/syntax syntax/parse)))

;; =============================================================================

(define-language RST
  (e ::= x integer (λ (x) e) (unbox e) (set-box! e e) (+ e e) (e e) (box e) (if e e e) (let ((L x e)) e) (letrec ((L x e)) e) (:: e σ))
  (v ::= integer (λ (x) e) (box v))
  (c ::= (CLOSURE e γ))
  (σ ::= (∀ (α) σ) τ)
  (τ ::= (U k τ) (μ (α) τ) α k)
  (k ::= Integer (→ τ τ) (Box τ))
  (P ::= (L e))
  (L ::= R S T)
  (γ ::= ((L x v) ...))
  (Γ ::= ((L x τ) ...))
  (x* ::= (x ...))
  (α* ::= (α ...))
  (x α ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (∀ (α) σ #:refers-to α)
  (μ (α) τ #:refers-to α)
  (λ (x) e #:refers-to x)
  (let ((x e_0)) e #:refers-to x)
  (letrec ((x e_0 #:refers-to x)) e #:refers-to x)
)

(module+ test
  (define-syntax (define-predicate* stx)
    (syntax-parse stx
     [(_ [x*:id ...])
      #:with (x?* ...) (for/list ([x (in-list (syntax-e #'(x* ...)))]) (format-id stx "~a?" (syntax-e x)))
      (syntax/loc stx (begin (define x?* (redex-match? RST x*)) ...))]))

  (define-predicate* [e v c σ τ k L γ Γ])

  (test-case "e"
    (check-pred e? (term x))
    (check-pred e? (term 4))
    (check-pred e? (term (:: 4 Integer)))
    (check-pred e? (term (:: 4 (Box Integer))))
    (check-pred e? (term (let ((R x 4)) (+ x 1)))))

  (test-case "τ"
    (check-pred τ? (term Integer)))
)

;; -----------------------------------------------------------------------------
;; --- grammar
;; TODO
;; - type have discriminative unions
;; - check σ in the right places?
;; - well-formed type variables
;; - closed

(define-judgment-form RST
  #:mode (well-formed I I)
  #:contract (well-formed L e)
  [
   (closed e)
   ---
   (well-formed R e)]
  [
   (closed e)
   (well-formed-T e)
   ---
   (well-formed S e)]
  [
   (closed e)
   (well-formed-T e)
   ---
   (well-formed T e)])

(define-judgment-form RST
  #:mode (well-formed-T I)
  #:contract (well-formed-T e)
  [
   --- Var
   (well-formed-T x)]
  [
   --- Integer
   (well-formed-T integer)]
  [
   (well-formed-T e)
   (well-formed-type τ)
   --- Lambda
   (well-formed-T (:: (λ (x) e) τ))]
  [
   (well-formed-T e)
   --- Unbox
   (well-formed-T (unbox e))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- Set
   (well-formed-T (set-box! e_0 e_1))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- +
   (well-formed-T (+ e_0 e_1))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- App
   (well-formed-T (e_0 e_1))]
  [
   (well-formed-T e)
   (well-formed-type τ)
   --- Box
   (well-formed-T (:: (box e) τ))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   (well-formed-T e_2)
   --- If
   (well-formed-T (if e_0 e_1 e_2))]
  [
   (well-formed L e_0)
   (well-formed-T e_1)
   --- Let
   (well-formed-T (let ((L x e_0)) e_1))]
  [
   (well-formed L e_0)
   (well-formed-T e_1)
   --- Letrec
   (well-formed-T (letrec ((L x e_0)) e_1))])

(define-judgment-form RST
  #:mode (well-formed-type I)
  #:contract (well-formed-type σ)
  [
   ;; TODO
   ;; - no f
   ---
   (well-formed-type σ)])

(define-judgment-form RST
  #:mode (closed I)
  #:contract (closed any)
  [
   (free-variables any ())
   ---
   (closed any)])

(define-judgment-form RST
  #:mode (free-variables I O)
  #:contract (free-variables any x*)
  [
   ;; TODO
   ---
   (free-variables any ())])

;; -----------------------------------------------------------------------------
;; --- utils


;; -----------------------------------------------------------------------------
;; --- type checking

(define-judgment-form RST
  #:mode (well-typed I O)
  #:contract (well-typed P τ)
  [
   (R-typed () e τ)
   ---
   (well-typed (R e) τ)]
  [
   (T-typed () e τ)
   ---
   (well-typed (S e) τ)]
  [
   (T-typed () e τ)
   ---
   (well-typed (T e) τ)])

(define-judgment-form RST
  #:mode (R-typed I I O)
  #:contract (R-typed Γ e τ)
  [
   --- TODO
   (R-typed Γ e Integer)]
)

(define-judgment-form RST
  #:mode (T-typed I I O)
  #:contract (T-typed Γ e τ)
  [
   --- TODO
   (T-typed Γ e Integer)]
)



;; uhm what abouy environemnts?
(define-metafunction RST
  typecheck : P -> τ
  [(typecheck P)
   τ
   (judgment-holds (well-typed P τ))])

;; -----------------------------------------------------------------------------
;; --- evaluation


;; -----------------------------------------------------------------------------
;; --- (colorblind) compiler
;; - translate R S T terms all to R
;; - but the S T terms have proper checks,
;; - via contracts and type-directed defense

