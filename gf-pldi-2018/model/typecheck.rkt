#lang mf-apply racket/base

(provide
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  racket/set
  redex/reduction-semantics)

;; -----------------------------------------------------------------------------
;; --- typing
;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (<: I I)
  #:contract (<: τ τ)
  [
   --- Sub-Refl
   (<: τ τ)])

(define-metafunction μTR
  subtype? : τ τ -> boolean
  [(subtype? τ_0 τ_1)
   (judgment-holds (<: τ_0 τ_1))])

(define-judgment-form μTR
  #:mode (well-tagged-value I I)
  #:contract (well-tagged-value v κ)
  [
   ---
   (well-tagged-value integer Int)]
  [
   ---
   (well-tagged-value natural Nat)]
  [
   (fun-value v)
   ---
   (well-tagged-value v →)]
  [
   (vector-value v)
   ---
   (well-tagged-value v Vector)]
  [
   ---
   (well-tagged-value nil List)]
  [
   ---
   (well-tagged-value (cons v_0 v_1) List)]
  [
   ;; TODO edit if performance is an issue
   (where (κ_pre ... κ_mid κ_post ...) (κ ...))
   (well-tagged-value v κ_mid)
   ---
   (well-tagged-value v (U κ ...))])

(define-judgment-form μTR
  #:mode (not-well-tagged-value I I)
  #:contract (not-well-tagged-value v κ)
  [
   (side-condition ,(not (judgment-holds (well-tagged-value v κ))))
   ---
   (not-well-tagged-value v κ)])

(define-judgment-form μTR
  #:mode (flat-value I)
  #:contract (flat-value v)
  [
   ---
   (flat-value integer)]
  [
   ---
   (flat-value nil)])

(define-judgment-form μTR
  #:mode (vector-value I)
  #:contract (vector-value v)
  [
   ---
   (vector-value (vector v ...))]
  [
   ---
   (vector-value (mon-vector τ v))])

(define-judgment-form μTR
  #:mode (fun-value I)
  #:contract (fun-value v)
  [
   ---
   (fun-value Λ)]
  [
   ---
   (fun-value (mon-fun τ v))])

(define-judgment-form μTR
  #:mode (tag-of I I)
  #:contract (tag-of τ κ)
  [
   ---
   (tag-of κ κ)]
  [
   ---
   (tag-of (→ τ_0 τ_1) →)]
  [
   ---
   (tag-of (Vectorof τ) Vector)]
  [
   ---
   (tag-of (Listof τ) List)]
  [
   (tag-of τ κ) ...
   ---
   (tag-of (U τ ...) (U κ ...))]
  [
   (tag-of τ κ)
   ---
   (tag-of (∀ (α) τ) κ)]
  [
   (tag-of τ κ)
   ---
   (tag-of (μ (α) τ) κ)])

(define-metafunction μTR
  type->tag : τ -> κ
  [(type->tag τ)
   κ
   (judgment-holds (tag-of τ κ))])

