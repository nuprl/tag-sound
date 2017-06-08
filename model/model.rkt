#lang mf-apply racket/base

;; - 3 languages
;; - 3/3 terms
;; - 2/3 types
;; - type context remembers source language
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

;; TODO what about type annotations?

(define-language RST
  (e ::= x v (λ (x) e) (unbox e) (set-box! e e) (+ e e) (e e) (box e) (if e e e) (let ((L x e)) e) (letrec ((L x e)) e) (:: e τ))
  (v ::= c integer (box v))
  (c ::= (CLOSURE e γ))
  (σ ::= (∀ (α) σ) τ)
  (τ ::= (U k τ) (μ (α) τ) α k)
  (k ::= Integer (→ τ τ) (Box τ))
  (L ::= R S T)
  (γ ::= ((L x v) ...))
  (Γ ::= ((L x τ) ...))
  (x α ::= variable-not-otherwise-mentioned)
  #:binding-forms
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

;; -----------------------------------------------------------------------------


;; -----------------------------------------------------------------------------

;; -----------------------------------------------------------------------------


;; -----------------------------------------------------------------------------

;; The colored interpreter needs to keep types at runtime. For what?
;; - ???
