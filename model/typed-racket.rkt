#lang mf-apply racket/base

;; Simple model of Typed Racket.

;; Soundness (from SNAPL 2017):
;;   If `⊢ e : τ` then either
;;   - `e` reduces to `v` and `⊢ v : τ`
;;   - `e` diverges
;;   - `e` raises a runtime error (bad value given to partial primitive)
;;   - `e` raises a boundary error `b` that points to a _specific location_
;;     where an untyped value entered typed code.

;; Lemmas
;;   - `∀ e . ⊢T e : τ => τ != TST`

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; -----------------------------------------------------------------------------

(define-language++ μTR #:alpha-equivalent? α=?
  (e ::= v (e e) x (let (x τ P) e) (cons e e) (+ e e) (= e e) (if e e e) (and e e) (pre-mon L τ P))
  (v ::= integer boolean Λ (cons v v) (mon L τ (L v)))
  (Λ ::= (λ (x τ) e))
  (P ::= (L e))
  (τ ::= (U τk ...) τk TST)
  (τk ::= Int Bool (Pair τ τ) (→ τ τ))
  (L ::= R T)
  (Γ ::= ((x τ) ...))
  (E ::= hole
         (E e) (v E)
         (cons E e) (cons v E)
         (+ E e) (+ v E)
         (= E e) (= v E)
         (if E e e)
         (and E e) (and v E))
  (RuntimeError ::= (DynError P) (BoundaryError L τ P))
  (A ::= P RuntimeError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (let (x τ P) e #:refers-to x)
  (λ (x τ) e #:refers-to x))

(module+ test
  (*term-equal?* α=?)

  (test-case "define-language"
    (check-pred e? (term 2))
    (check-pred e? (term (+ 1 1)))
    (check-pred e? (term (= x 1)))
    (check-pred e? (term (if (= x 1) 1 #false)))
    (check-pred e? (term (if #true 2 3)))
    (check-pred τ? (term (→ Int Int)))
    (check-pred τ? (term TST))
    (check-pred P? (term (R (if (= x 1) 1 #false))))
    (check-pred P? (term (R (λ (x TST) (if (= x 1) 1 #false)))))
    (check-pred P? (term (R (if 1 2 3))))
    (check-pred P? (term (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1)))))
    (check-pred e? (term (if 1 2 3)))
  )
)

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-typed I)
  #:contract (well-typed P)
  [
   (infer-type () P τ)
   ---
   (well-typed P)])

(define-judgment-form μTR
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (T e) τ_actual)
   (subtype τ_actual τ)
   ---
   (check-type Γ (T e) τ)])

(define-judgment-form μTR
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P τ)
  [
   ---
   (infer-type Γ (R integer) TST)]
  [
   ---
   (infer-type Γ (T integer) Int)]
  [
   ---
   (infer-type Γ (R boolean) TST)]
  [
   ---
   (infer-type Γ (T boolean) Bool)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (R e) τ_cod)
   ---
   (infer-type Γ (R (λ (x τ_dom) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (T e) τ_cod)
   ---
   (infer-type Γ (T (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   ---
   (infer-type Γ (T (e_0 e_1)) τ_cod)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (R x) TST)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (T x) τ)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (R e_body) τ_body)
   ---
   (infer-type Γ (R (let (x τ P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (T e_body) τ_body)
   ---
   (infer-type Γ (T (let (x τ P) e_body)) τ_body)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (+ e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (+ e_0 e_1)) Int)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (= e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (= e_0 e_1)) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   (infer-type Γ (R e_2) τ_2)
   ---
   (infer-type Γ (R (if e_0 e_1 e_2)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (type= τ_0 Bool)
   (infer-type Γ (T e_1) τ_1)
   (infer-type Γ (T e_2) τ_2)
   (type= τ_1 τ_2)
   ---
   (infer-type Γ (T (if e_0 e_1 e_2)) τ_2)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (and e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Bool)
   (type= τ_1 Bool)
   ---
   (infer-type Γ (T (and e_0 e_1)) Bool)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (mon R τ P)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (mon T τ P)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (pre-mon R τ P)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (pre-mon T τ P)) τ)]
)

(define-metafunction μTR
  check-type# : P τ -> boolean
  [(check-type# P τ)
   #true
   (judgment-holds (check-type () P τ))]
  [(check-type# P τ)
   #false])

(define-metafunction μTR
  infer-type# : P -> τ
  [(infer-type# P)
   τ
   (judgment-holds (infer-type () P τ))]
  [(infer-type# P)
   ,(raise-user-error 'infer-type# "failed to infer type for term ~a" (term P))])

(module+ test

  (test-case "check-type#"
    (check-true (term #{check-type# (R (if 1 2 3)) TST})))

  (test-case "infer-type#"
    (check-mf-apply*
     ((infer-type# (T (if (and #true #true) (+ 1 1) (+ 2 2))))
      Int)
     ((infer-type# (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (T (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)))

  (test-case "well-typed"
    (check-judgment-holds*
     (well-typed (T (λ (x Int) 2)))
     (infer-type () (T (λ (x Int) 3)) (→ Int Int))
     (check-type () (T (λ (x Int) 3)) (→ Int Int))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2))) 7)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (check-type () (T 1) Int)
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
    )

    (check-false (judgment-holds (well-typed (T (if (λ (x Int) x) 1 0)))))
  )
)

;; -----------------------------------------------------------------------------
;; --- type helpers

;; TODO need this?
(define-metafunction μTR
  coerce-→ : τ -> τ
  [(coerce-→ TST)
   (→ TST TST)]
  [(coerce-→ (→ τ_dom τ_cod))
   (→ τ_dom τ_cod)]
  [(coerce-→ τ)
   ,(raise-argument-error 'coerce-→ "cannot coerce ~a" (term τ))])

(define-judgment-form μTR
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   (side-condition ,(α=? (term #{type-normalize τ_0}) (term #{type-normalize τ_1})))
   --- Refl
   (type= τ_0 τ_1)])

(define-metafunction μTR
  type-normalize : τ -> τ
  [(type-normalize τk)
   τk]
  [(type-normalize TST)
   TST]
  [(type-normalize (U τk ...))
   ,(let ((kk (sort/deduplicate (term (τk ...)) symbol<? #:key simple-type->constructor)))
      (cond
       [(null? kk)
        (term (U))]
       [(null? (cdr kk))
        (car kk)]
       [else
        (cons (term U) kk)]))])

(define (simple-type->constructor t)
  (unless (τk? t)
    (raise-argument-error 'simple-type->constructor "simple type" t))
  (cond
   [(symbol? t)
    t]
   [(pair? t)
    (car t)]
   [else
    (raise-user-error 'simple-type->constructor "undefined for type ~a" t)]))

(define (sort/deduplicate t* <? #:key get-key)
  (let loop ([t* (sort t* <? #:key get-key)])
    (cond
     [(or (null? t*) (null? (cdr t*)))
      t*]
     [(equal? (car t*) (cadr t*))
      ;; TODO not great (but also not horrible)
      (loop (cdr t*))]
     [else
      (cons (car t*) (loop (cdr t*)))])))

(define-judgment-form μTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [
   --- Refl
   (subtype τ τ)]
  [
   (subtype τ_dom1 τ_dom0)
   (subtype τ_cod0 τ_cod1)
   --- Arrow
   (subtype (→ τ_dom0 τ_cod0) (→ τ_dom1 τ_cod1))]
  [
   (subtype τ_lhs τ_rhs)
   --- U-Member
   (subtype τ_lhs (U τ_0 ... τ_rhs τ_1 ...))]
  [
   --- U-Empty
   (subtype (U) (U τ ...))]
  [
   (subtype τ_lhs τ_rhs)
   (subtype (U τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))
   ---
   (subtype (U τ_lhs τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))])

(module+ test
  (test-case "coerce-→"
    (check-mf-apply*
     ((coerce-→ (→ Int Bool))
      (→ Int Bool))
     ((coerce-→ TST)
      (→ TST TST))))

  (test-case "simple-type->constructor"
    (check-apply* simple-type->constructor
     ((term Int)
      ==> 'Int)
     ((term Bool)
      ==> 'Bool)
     ((term (Pair Int Int))
      ==> 'Pair)
     ((term (→ Int Int))
      ==> '→)))

  (test-case "type-normalize"
    (check-mf-apply*
     ((type-normalize (U Int Int))
      Int)
     ((type-normalize (U Int Bool))
      (U Bool Int))
     ((type-normalize (U Int Int (Pair Int Int) (Pair Bool Int)))
      (U Int (Pair Int Int) (Pair Bool Int)))
     ((type-normalize (U (Pair Int Int) (Pair Int Int) Int))
      (U Int (Pair Int Int)))))
)

;; -----------------------------------------------------------------------------
;; --- environment helpers

(define-metafunction μTR
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction μTR
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

