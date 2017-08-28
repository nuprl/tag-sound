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
;; - ◊ (□ ∎) are logical duals in FRP (says Tony),
;;   are they logical duals here?
;;  (if not, maybe ◊ should be "next" as in "after 1 check" Ο)
;; - union types, recursive types, forall types

;; NOTATION
;; □ = "A" (currently necessary)
;; ∎ = "W" (always necessary)
;; ◊ = "V" (possible)

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

;; Language MTT, key points:
;; - recursive functions
;; - mutable data (box)
;; - immutable data (cons)
;; - conditional
;; - base types / values
;; - modal types

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
  (Λ ::= (fun x τ (x) e))
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
  (fun x_f τ (x) e #:refers-to (shadow x_f x)))

;; -----------------------------------------------------------------------------
;; --- static type checking

;; -----------------------------------------------------------------------------
;; --- evaluation

;; -----------------------------------------------------------------------------
;; --- models

;; v ⊨ τ
;; Well-typed if:
;; A. higher-order and ∎ and monitored
;; B. well-tagged under the given modality, and subterms well-typed
;; C. not well-tagged, and ◊ modality
;; (This is basically 3 judgments in one,
;;  first recur on the mode,
;;  second recur on the value/type)
(define-judgment-form MMT
  #:mode (well-typed-value I I I)
  #:contract (well-typed-value σ v τ)
  [
   (not-well-tagged-value v k)
   ---
   (well-typed-value σ v (k ◊ τ_k ...))]
  [
   (well-typed-value σ v (k □ τ_k ...))
   ---
   (well-typed-value σ v (k ◊ τ_k ...))]
  [
   (well-tagged-value v k)
   (where (v_k ...) #{sub-values σ v}) ;; maybe fewer sub-values than τ
   (well-typed-value* σ (v_k ...) (τ_k ...))
   ---
   (well-typed-value σ v (k □ τ_k ...))]
  [
   ---
   (well-typed-value σ integer (Int ∎))]
  [
   ---
   (well-typed-value σ boolean (Bool ∎))]
  [
   (well-typed-value σ v_0 τ_0)
   (well-typed-value σ v_1 τ_1)
   ---
   (well-typed-value σ (cons v_0 v_1) (Pair ∎ τ_0 τ_1))]
  [
   (where (mon (→ ∎ τ_0 τ_1) v_arr) v)
   ---
   (well-typed-value σ v (→ ∎ τ_0 τ_1))]
  [
   (where (mon (Box ∎ τ_box) (box x_box)) v)
   (where v_box #{runtime-env-ref σ x_box})
   (well-typed-value σ v_box τ_box)
   ---
   (well-typed-value σ v (Box ∎ τ_box))])

(define-judgment-form MMT
  #:mode (well-typed-value* I I I)
  #:contract (well-typed-value* σ (v ...) (τ ...))
  [
   --- Null
   (well-typed-value* σ () (τ ...))]
  [
   (well-typed-value σ v_0 τ_0)
   (well-typed-value* σ (v_1 ...) (τ_1 ...))
   ---
   (well-typed-value* σ (v_0 v_1 ...) (τ_0 τ_1 ...))])

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
   (well-tagged-value (fun _ _ _ _) →)]
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
  (define Int->Int (term (→ □ (Int □) (Int □))))

  (test-case "well-tagged"
    ;; box tests are a little weird,
    ;;  because the boxes contain unbound variables,
    ;;  because (box v) is not a value --- only (box x) is

    (check-judgment-holds*
     (well-tagged-value 3 Int)
     (well-tagged-value #true Bool)
     (well-tagged-value (cons 1 #false) Pair)
     (well-tagged-value (fun f ,Int->Int (x) x) →)
     (well-tagged-value (mon ,Int->Int (fun g ,Int->Int (x) 3))
                        →)
     (well-tagged-value (box x) Box)
     (well-tagged-value (mon (Box □ (Int □)) (box z)) Box)
    )
    (check-not-judgment-holds*
     (well-tagged-value 3 Bool)
     (well-tagged-value #false →)
     (well-tagged-value (mon (Box □ (Int □)) 4) Box)
    )
  )

  (test-case "not-well-tagged"
    (check-judgment-holds*
     (not-well-tagged-value 3 Bool)
     (not-well-tagged-value #false →)
     (not-well-tagged-value (mon (Box □ (Int □)) 4) Box)
    )
    (check-not-judgment-holds*
     (not-well-tagged-value 3 Int)
     (not-well-tagged-value #true Bool)
     (not-well-tagged-value (box a) Box)
     (not-well-tagged-value (mon (Box □ (Int □)) (box b)) Box)
    )
  )

  (test-case "well-typed-value"
    (check-judgment-holds*
     (well-typed-value () 4 (Int □))
     (well-typed-value () #true (Bool ∎))
     (well-typed-value () #true (Bool ◊))
     (well-typed-value () #true (Int ◊))

     (well-typed-value () (cons 1 1) (Pair □ (Int □) (Int □)))
     (well-typed-value () (cons 1 1) (Pair ∎ (Int ∎) (Int ∎)))
     (well-typed-value () (cons 1 1) (Pair ◊ (Int ◊) (Int ◊)))
     (well-typed-value () (cons #true #true) (Pair ◊ (Int ◊) (Int ◊)))
     (well-typed-value () 8888 (Pair ◊ (Int ◊) (Int ◊)))
     (well-typed-value () (cons 1 #false) (Pair ◊ (Int □) (Int ◊)))
     (well-typed-value () (cons 1 #false) (Pair □ (Int □) (→ ◊ (Int □) (Int □))))

     (well-typed-value ((x 3)) (box x) (Box □ (Int □)))
     (well-typed-value ((x #true)) (box x) (Box □ (Bool ◊)))
     (well-typed-value ((x (fun f ,Int->Int (x) (+ x x)))) (box x) (Box □ ,Int->Int))
     (well-typed-value ((z (fun f ,Int->Int (x) (+ x x)))) (box z) (Box □ (Int ◊)))
     (well-typed-value ((z (fun f ,Int->Int (x) (+ x x)))) (box z) (Bool ◊))
     (well-typed-value ((z 4)) (mon (Box ∎ (Int ∎)) (box z)) (Box ∎ (Int ∎)))

     (well-typed-value () (fun f ,Int->Int (x) 4) (→ □ (Int □) (Int □)))
     (well-typed-value () (fun f ,Int->Int (x) 4) (→ □ (Bool □) (Bool □)))
     (well-typed-value () (fun f ,Int->Int (x) 4) (→ ◊ (Bool □) (Int ∎)))
     (well-typed-value () (mon (→ ∎ (Int □) (Int ◊)) (fun f ,Int->Int (x) 4))
                       (→ ∎ (Int □) (Int ◊)))
    )

    (check-not-judgment-holds*
     ;; TODO simple tests

     (well-typed-value ((z 4)) (box z) (Box ∎ (Int □)))
     (well-typed-value ((z 4)) (box z) (Box ∎ (Int ◊)))
     (well-typed-value ((z (fun f ,Int->Int (x) (+ x x)))) (box z) (Box ∎ ,Int->Int))
     (well-typed-value ((z #true)) (mon (Box ∎ (Int ∎)) (box z)) (Box ∎ (Int ∎)))
     (well-typed-value ((z 32)) (mon (Box ∎ (Int ∎)) (box z)) (Box ∎ (Bool ∎)))
    )
  )
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
  sub-values : σ v -> (v ...)
  [(sub-values σ integer)
   ()]
  [(sub-values σ boolean)
   ()]
  [(sub-values σ (cons v_0 v_1))
   (v_0 v_1)]
  [(sub-values σ Λ)
   ()]
  [(sub-values σ (box x_0))
   (#{runtime-env-ref σ x_0})])

(define-metafunction MMT
  runtime-env-ref : σ x -> v
  [(runtime-env-ref σ x)
   ,(or (for/first ([xv (in-list (term σ))]
                    #:when (equal? (car xv) (term x)))
          (cadr xv))
        (raise-arguments-error 'runtime-env-ref "unbound variable" "var" (term x) "env" (term σ)))])

(module+ test
  ;; TODO

  (test-case "runtime-env-ref"
    (check-equal?
      (term #{runtime-env-ref ((x 0) (y 1)) x})
      0)
    (check-equal?
      (term #{runtime-env-ref ((x 0) (y 1)) y})
      1)
    (check-exn exn:fail:contract?
      (λ () (term #{runtime-env-ref ((x 0) (y 1)) z})))
  )
)

