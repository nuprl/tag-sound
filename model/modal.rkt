#lang mf-apply racket/base

;; Goal:
;; - types with modalities
;; - generalize TR Retic TypeScript
;; - normal evaluation semantics
;; - erasure semantics

;; Need
;; - soundness
;;   if ⊢ e : τ^μ then either
;;   - e diverges
;;   - e -->* runtime-error
;;   - e -->* boundary-error
;;   - e -->* v and v ⊨ τ^μ
;; - corollary : soundness for TR retic TS SS
;; - complete monitor
;;
;; - union types, recursive types, forall types

;; NOTATION
;; □ = "A" (currently necessary)
;; ∎ = "W" (always necessary)
;; ◇ = "V" (possible)

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

;; -----------------------------------------------------------------------------

(define-language++ MMT #:alpha-equivalent? α=?
  (e ::= v x (e e) (if e e e) (and e e)
         (let (x τ P) e)
         (cons e e) (car e) (cdr e)
         (binop e e) (= e e)
         (box e) (make-box e) (unbox e) (set-box! e e))
  (c ::= ;; core language
         e
         (mon τ e)
         (check τ e))
  (v ::= (box x) integer boolean Λ (cons v v) (mon τ v))
  (Λ ::= (fun f τ x e))
  (τ ::= (k μ τ ...))
  (k ::= Int Bool Pair → Box)
  (μ ::= □ ∎ ◊)
  (Γ ::= ((x τ) ...))
  (σ ::= ((x v) ...))
  (primop ::= car cdr binop =)
  (binop ::= + * -)
  (E ::= hole
         (E e) (v E) (if E e e) (let (x τ E) e)
         (cons E e) (cons v E)
         (car E) (cdr E)
         (binop E e) (binop v E)
         (= E e) (= v E)
         (make-box E) (set-box! E e) (set-box! v E) (unbox E)
         (check τ E)
         (mon τ E))
  (RuntimeError ::= (PrimopError string) (BoundaryError τ v))
  (A ::= [σ e] RuntimeError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (let (x τ P) e #:refers-to x)
  (fun f τ x e #:refers-to (shadow f x)))

;; -----------------------------------------------------------------------------
;; --- static type checking

;; -----------------------------------------------------------------------------
;; --- evaluation

;; -----------------------------------------------------------------------------
;; --- models

;; Well-typed if:
;; A. higher-order and ∎ and monitored
;; B. well-tagged under the given modality, and subterms well-typed
;; C. not well-tagged, and ◊ modality
(define-judgment-form MMT
  #:mode (well-typed-value I I)
  #:contract (well-typed-value v τ)
  [
   (not-well-tagged-value v k)
   ---
   (well-typed-value v (k ◊ τ_k ...))]
  [
   (well-typed-value v (k □ τ_k ...))
   ---
   (well-typed-value v (k ◊ τ_k ...))]
  [
   (well-tagged-value v k)
   (where (v_k ...) #{sub-values v})
   (well-typed-value* (v_k ...) (τ_k ...))
   ---
   (well-typed-value v (k □ τ_k ...))]
  [
   ---
   (well-typed-value integer (Int ∎))]
  [
   ---
   (well-typed-value boolean (Bool ∎))]
  [
   (well-typed-value v_0 τ_0)
   (well-typed-value v_1 τ_1)
   ---
   (well-typed-value (cons v_0 v_1) (Pair ∎ τ_0 τ_1))]
  [
   (where (mon (→ ∎ τ_0 τ_1) v_arr) v)
   ---
   (well-typed-value v (→ ∎ τ_0 τ_1))]
  [
   (where (mon τ v_box) v)
   ---
   (well-typed-value v (Box ∎ τ))])

(define-judgment-form MMT
  #:mode (well-typed-value* I I)
  #:contract (well-typed-value* (v ...) (τ ...))
  [
   --- Null
   (well-typed-value* () (τ ...))]
  [
   (well-typed-value v_0 τ_0)
   (well-typed-value* (v_1 ...) (τ_1 ...))
   ---
   (well-typed-value* (v_0 v_1 ...) (τ_0 τ_1 ...))])

(define-judgment-form MMT
  #:mode (well-tagged-value I I)
  #:contract (well-tagged-value v k)
  [
   ---
   (well-tagged-value integer Int)]
  [
   ---
   (well-tagged-value boolean Bool)]
  [
   ---
   (well-tagged-value (cons v_0 v_1) Pair)]
  [
   ---
   (well-tagged-value (fun f τ e) →)]
  [
   ---
   (well-tagged-value (box _) Box)]
  [
   (well-tagged-value v k)
   ---
   (well-tagged-value (mon τ v) k)])

(define-judgment-form MMT
  #:mode (not-well-tagged-value I I)
  #:contract (not-well-tagged-value v k)
  [
   (side-condition ,(not (judgment-holds (well-tagged-value v k))))
   ---
   (not-well-tagged-value v k)])

(module+ test
  ;; TODO
)

;; -----------------------------------------------------------------------------
;; --- well-formedness

(define-judgment-form MMT
  #:mode (well-formed-type I)
  #:contract (well-formed-type τ)
  [
   (type-arity-ok τ)
   ---
   (well-formed-type τ)])

(define-judgment-form MMT
  #:mode (type-arity-ok I)
  #:contract (type-arity-ok τ)
  [
   (where natural_k #{type-constructor-arity k})
   (where natural_τ ,(length (term (τ ...))))
   (side-condition ,(= (term natural_k) (term natural_τ)))
   (type-arity-ok τ) ...
   ---
   (type-arity-ok (k _ τ ...))])

(define-metafunction MMT
  type-constructor-arity : k -> natural
  [(type-constructor-arity Int)
   0]
  [(type-constructor-arity Bool)
   0]
  [(type-constructor-arity Pair)
   2]
  [(type-constructor-arity →)
   2]
  [(type-constructor-arity Box)
   1]
  [(type-constructor-arity k)
   ,(raise-user-error 'type-constructor-arity "not implemented for ~a" (term k))])

(module+ test
  (test-case "well-formed-type"
    (check-judgment-holds*
     (well-formed-type (Int □))
     (well-formed-type (Int ∎))
     (well-formed-type (Bool ◊))
     (well-formed-type (→ □ (→ □ (Int ◊) (Int ∎))
                            (Pair □ (Box ∎ (Int ∎))
                                    (Int ∎))))))

  (test-case "well-formed-type:bad-arity"
    (check-not-judgment-holds*
     (well-formed-type (Int ◊ (Int ◊)))
     (well-formed-type (→ □))
     (well-formed-type (→ □ (Box □) (Int □)))))
)

;; -----------------------------------------------------------------------------
;; --- utils

(define-judgment-form MMT
  #:mode (μ<=? I I)
  #:contract (μ<=? μ μ)
  [
   --- Refl
   (μ<=? μ μ)])

(define-metafunction MMT
  sub-values : v -> (v ...)
  [(sub-values integer)
   ()]
  [(sub-values boolean)
   ()]
  [(sub-values (cons v_0 v_1))
   (v_0 v_1)]
  [(sub-values Λ)
   ()]
  [(sub-values (box v_0))
   (v_0)])

(module+ test
  ;; TODO
)

