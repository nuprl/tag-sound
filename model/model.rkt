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
  (require rackunit-abbrevs rackunit))

;; =============================================================================

;; TODO what about type annotations?

(define-language RST
  (e ::= x (λ (x) e) (unbox e) (set-box! e e) (+ e e) (e e) (box e) (if e e e) (let ((x e)) e) (letrec ((x e)) e))
  (v ::= c integer (box v))
  (c ::= (CLOSURE (λ (x) e) γ))
  (τ ::= (U k τ) (μ (α) τ) α)
  (k ::= Integer (→ τ τ) (Box τ))
  (L ::= R S T)
  (P ::= (R e))
  (γ ::= ((L x v) ...))
  (Γ ::= ((L x τ) ...))
  (x α ::= variable-not-otherwise-mentioned)
  ;#:binding-forms ???
)

;; The colored interpreter needs to keep types at runtime. For what?
;; - ???
