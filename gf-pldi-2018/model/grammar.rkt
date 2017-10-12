#lang mf-apply racket/base

(provide
  well-formed-type
  well-formed-program
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  (only-in racket/list
    check-duplicates)
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define-judgment-form μTR
  #:mode (well-formed-type I)
  #:contract (well-formed-type τ)
  [
   (all-unions-discriminative τ)
   (all-recursive-types-contractive τ)
   (all-abstractions-guarded τ)
   (closed-type τ)
   ---
   (well-formed-type τ)])

(define-judgment-form μTR
  #:mode (all-unions-discriminative I)
  #:contract (all-unions-discriminative τ)
  [
   ---
   (all-unions-discriminative Int)]
  [
   ---
   (all-unions-discriminative Nat)]
  [
   (all-unions-discriminative τ_dom)
   (all-unions-discriminative τ_cod)
   ---
   (all-unions-discriminative (→ τ_dom τ_cod))]
  [
   (all-unions-discriminative τ)
   ---
   (all-unions-discriminative (Vectorof τ))]
  [
   (all-unions-discriminative τ)
   ---
   (all-unions-discriminative (Listof τ))]
  [
   (discriminative-union (U τ ...))
   (all-unions-discriminative τ) ...
   ---
   (all-unions-discriminative (U τ ...))]
  [
   (all-unions-discriminative τ)
   ---
   (all-unions-discriminative (∀ (α) τ))]
  [
   (all-unions-discriminative τ)
   ---
   (all-unions-discriminative (μ (α) τ))]
  [
   ---
   (all-unions-discriminative α)])

(define-judgment-form μTR
  #:mode (discriminative-union I)
  #:contract (discriminative-union (U τ ...))
  [
   (where (κ ...) (#{type->tag τ} ...))
   (side-condition ,(check-duplicates (term (κ ...))))
   ---
   (discriminative-union (U τ ...))])

(define-judgment-form μTR
  #:mode (all-recursive-types-contractive I)
  #:contract (all-recursive-types-contractive τ)
  [
   ---
   (all-recursive-types-contractive Int)]
  [
   ---
   (all-recursive-types-contractive Nat)]
  [
   (all-recursive-types-contractive τ_dom)
   (all-recursive-types-contractive τ_cod)
   ---
   (all-recursive-types-contractive (→ τ_dom τ_cod))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (Vectorof τ))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (Listof τ))]
  [
   (all-recursive-types-contractive τ) ...
   ---
   (all-recursive-types-contractive (U τ ...))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (∀ (α) τ))]
  [
   (formally-contractive (α) τ)
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (μ (α) τ))]
  [
   ---
   (all-recursive-types-contractive α)])

;; formally-contractive = does not have the form `(μ (α_i ...) α_i)`
(define-judgment-form μTR
  #:mode (formally-contractive I I)
  #:contract (formally-contractive α* τ)
  [
   ---
   (formally-contractive α* Int)]
  [
   ---
   (formally-contractive α* Nat)]
  [
   ---
   (formally-contractive α* (→ _ _))]
  [
   ---
   (formally-contractive α* (Vectorof _))]
  [
   ---
   (formally-contractive α* (Listof _))]
  [
   (formally-contractive α* τ_i) ...
   ---
   (formally-contractive α* (U τ_i ...))]
  [
   (where α*_+ ,(set-remove (term α*) (term α)))
   (formally-contractive α*_+ τ)
   ---
   (formally-contractive α* (∀ (α) τ))]
  [
   (where α*_+ ,(set-add (term α*) (term α)))
   (formally-contractive α*_+ τ)
   ---
   (formally-contractive α* (μ (α) τ))]
  [
   (side-condition ,(not (set-member? (term α*) (term α))))
   ---
   (formally-contractive α* α)])

(define-judgment-form μTR
  #:mode (all-abstractions-guarded I)
  #:contract (all-abstractions-guarded τ)
  [
   ;; TODO
   ---
   (all-abstractions-guarded τ)])

(define-judgment-form μTR
  #:mode (closed-type I)
  #:contract (closed-type τ)
  [
   (free-type-variables τ ())
   ---
   (closed-type τ)])

(define-judgment-form μTR
  #:mode (free-type-variables I O)
  #:contract (free-type-variables I O)
  [
   ---
   (free-type-variables Int ())]
  [
   ---
   (free-type-variables Nat ())]
  [
   (free-type-variables τ_dom α*_dom)
   (free-type-variables τ_cod α*_cod)
   (where α* ,(set-union (term α*_dom) (term α*_cod)))
   ---
   (free-type-variables (→ τ_dom τ_cod) α*)]
  [
   (free-type-variables τ α*)
   ---
   (free-type-variables (Vectorof τ) α*)]
  [
   (free-type-variables τ α*)
   ---
   (free-type-variables (Listof τ) α*)]
  [
   (free-type-variables τ_i α*_i) ...
   (where α* ,(set-union* (term (α*_i ...))))
   ---
   (free-type-variables (U τ_i ...) α*)]
  [
   (free-type-variables τ_body α*_body)
   (where α* ,(set-remove (term α*_body) (term α)))
   ---
   (free-type-variables (∀ (α) τ_body) α*)]
  [
   (free-type-variables τ_body α*_body)
   (where α* ,(set-remove (term α*_body) (term α)))
   ---
   (free-type-variables (μ (α) τ_body) α*)]
  [
   ---
   (free-type-variables α (α))])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-formed-program I)
  #:contract (well-formed-program P)
  [
   (where (MODULE ...) P)
   (well-formed-module MODULE) ...
   ;; TODO only require provided
   ---
   (well-formed-program P)])

(define-judgment-form μTR
  #:mode (well-formed-module I)
  #:contract (well-formed-module MODULE)
  [
   ;; TODO only provide defined
   ---
   (well-formed-module MODULE)])


(define-judgment-form μTR
  #:mode (well-formed-expression I)
  #:contract (well-formed-expression e)
  [
   ;; closed
   ;; no checks
   ;; no monitors?!
   ---
   (well-formed-expression e)])

