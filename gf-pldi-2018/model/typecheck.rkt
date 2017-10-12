#lang mf-apply racket/base

(provide
  <:
  subtype?
  not-well-tagged-value
  well-tagged-value
  flat-value
  vector-value
  fun-value
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define-judgment-form μTR
  #:mode (<: I I)
  #:contract (<: τ τ)
  [
   ---
   (<: Nat Int)]
  [
   --- Sub-Refl
   (<: τ τ)])

(define-metafunction μTR
  subtype? : τ τ -> boolean
  [(subtype? τ_0 τ_1)
   ,(judgment-holds (<: τ_0 τ_1))])

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
   (vector-value (mon-vector x τ v))])

(define-judgment-form μTR
  #:mode (fun-value I)
  #:contract (fun-value v)
  [
   ---
   (fun-value Λ)]
  [
   ---
   (fun-value (mon-fun x τ v))])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "subtype?"
    (check-mf-apply*
     [(subtype? Int Int)
      #true])
  )

  (test-case "well-tagged"
    (check-judgment-holds*
     (well-tagged-value 1 Nat)
     (well-tagged-value 1 Int)
     (well-tagged-value 1 (U Int Vector))
     (well-tagged-value (vector 1 2 3) Vector)
     (well-tagged-value (fun f (x) x) →)
     (well-tagged-value (cons 1 (cons 3 nil)) List))

    (check-not-judgment-holds*
     (well-tagged-value 1 Vector)
     (well-tagged-value (fun f (x) x) List)
     (well-tagged-value (vector 8 8) List))

    (check-judgment-holds*
     (not-well-tagged-value 1 Vector))

    (check-not-judgment-holds*
     (not-well-tagged-value (fun f (x) x) →))
  )

  (test-case "flat-value"
    (check-judgment-holds*
     (flat-value 3)
     (flat-value -2)
     (flat-value nil))

    (check-not-judgment-holds*
     (flat-value (cons 3 nil))
     (flat-value (fun f (x) x))
     (flat-value (vector 3))))

  (test-case "vector-value"
    (check-judgment-holds*
     (vector-value (vector 0 0))
     (vector-value (vector))
     (vector-value (mon-vector lbl (Vectorof Int) (vector)))
     (vector-value (mon-vector lbl (Vectorof Nat) (vector nil))))

    (check-not-judgment-holds*
     (vector-value (fun f (x) 3))
     (vector-value 4)
     (vector-value (cons 3 nil))))

  (test-case "fun-value"
    (check-judgment-holds*
     (fun-value (fun f (x) x))
     (fun-value (mon-fun lbl (→ Int Int) (fun f (x) (cons 0 nil)))))

    (check-not-judgment-holds*
     (fun-value -2)
     (fun-value 2)
     (fun-value (vector 0 0))))
)
