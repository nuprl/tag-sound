#lang mf-apply racket/base

;; Model of a statically-typed lambda calculus.
;; - values are: integers, pairs, functions
;; - types are for: integers, pairs, functions, and natural numbers
;; - well-typed terms: simple type inference, see `well-typed` judgment form
;; - safety: progress/preservation for well-typed terms

;; This is just a simple statically-typed language.

(require
  "redex-helpers.rkt"
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language LS
  (e ::= v x (e e) (× e e) (BINOP e e) (UNOP e))
  (v ::= integer (× v v) (λ (x : τ) e))
  (UNOP ::= fst snd)
  (BINOP ::= + /)

  (τ ::= Nat Int (× τ τ) (→ τ τ))
  ;; The `Nat` type is an example of how types can express more than
  ;;  "every primop gets values within its domain", and how ignoring
  ;;  the static types can lead to "silent failures"

  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E))

  (Γ ::= ((x : τ) Γ) ())

  (A ::= e TE BE)
  (BE ::= (Boundary-Error e string))
  (TE ::= (Type-Error e string))

  (MAYBE-τ ::= #f τ)
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x : τ) e #:refers-to x))

(module+ test
  (test-case "valid terms"
    ;; grammatically-valid terms may not be well-typed
    (check-true (redex-match? LS e (term (+ 1 -4))))
    (check-true (redex-match? LS e (term (f x))))
    (check-true (redex-match? LS e (term (0 1))))))

(define-metafunction LS
  error? : A -> boolean
  [(error? TE)
   #true]
  [(error? BE)
   #true]
  [(error? _)
   #false])

(define-metafunction LS
  integer? : v -> boolean
  [(integer? integer)
   #true]
  [(integer? _)
   #false])

(define-metafunction LS
  negative? : integer -> boolean
  [(negative? natural)
   #false]
  [(negative? integer)
   #true])

(define-metafunction LS
  pair? : v -> boolean
  [(pair? (× _ _))
   #true]
  [(pair? _)
   #false])

(define-metafunction LS
  procedure? : v -> boolean
  [(procedure? (λ (x : τ) e))
   #true]
  [(procedure? _)
   #false])

(define-metafunction LS
  type-env-ref : Γ x -> MAYBE-τ
  [(type-env-ref () x)
   #false]
  [(type-env-ref ((x : τ) Γ) x)
   τ]
  [(type-env-ref ((x_0 : _) Γ) x)
   (type-env-ref Γ x)])

;; -----------------------------------------------------------------------------

;; (well-typed Γ e τ) if and only if `e` has the static type `τ` under the
;;  environment `Γ`.
(define-judgment-form LS
  #:mode (well-typed I I I)
  #:contract (well-typed Γ e τ)
  [
   (infer-type Γ e τ_infer)
   (subtype τ_infer τ)
   ---
   (well-typed Γ e τ)])

;; Basic subtyping:
;; - pairs are co-variant
;; - functions are contra-variant in the domain and co-variant in the codomain
;; - Nat is a subtype of Int
(define-judgment-form LS
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [
   --- S-Nat
   (subtype Nat Int)]
  [
   (subtype τ_0 τ_2)
   (subtype τ_1 τ_3)
   --- S-Pair
   (subtype (× τ_0 τ_1) (× τ_2 τ_3))]
  [
   (subtype τ_2 τ_0)
   (subtype τ_1 τ_3)
   --- S-Fun
   (subtype (→ τ_0 τ_1) (→ τ_2 τ_3))]
  [
   --- S-Refl
   (subtype τ τ)])

(define-metafunction LS
  type-join : τ τ -> MAYBE-τ
  [(type-join τ_0 τ_1)
   τ_1
   (judgment-holds (subtype τ_0 τ_1))]
  [(type-join τ_0 τ_1)
   τ_0
   (judgment-holds (subtype τ_1 τ_0))]
  [(type-join τ_0 τ_1)
   #false])

(define-judgment-form LS
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e τ)
  [
   (where #true (negative? integer))
   --- I-Int
   (infer-type Γ integer Int)]
  [
   --- I-Nat
   (infer-type Γ natural Nat)]
  [
   (infer-type Γ e_0 τ_0)
   (infer-type Γ e_1 τ_1)
   --- I-Pair
   (infer-type Γ (× e_0 e_1) (× τ_0 τ_1))]
  [
   (where Γ_x ((x : τ_0) Γ))
   (infer-type Γ_x e τ_1)
   --- I-Fun
   (infer-type Γ (λ (x : τ_0) e) (→ τ_0 τ_1))]
  [
   (where τ (type-env-ref Γ x))
   --- I-Var
   (infer-type Γ x τ)]
  [
   (infer-type Γ e_0 (→ τ_dom τ_cod))
   (infer-type Γ e_1 τ_1)
   (subtype τ_1 τ_dom)
   --- I-App
   (infer-type Γ (e_0 e_1) τ_cod)]
  [
   (infer-type Γ e_0 τ_0)
   (infer-type Γ e_1 τ_1)
   (subtype τ_0 Int)
   (subtype τ_1 Int)
   (where τ (type-join τ_0 τ_1))
   --- I-+
   (infer-type Γ (+ e_0 e_1) τ)]
  [
   (infer-type Γ e_0 τ_0)
   (infer-type Γ e_1 τ_1)
   (subtype τ_0 Int)
   (subtype τ_1 Int)
   (where τ (type-join τ_0 τ_1))
   --- I-/
   (infer-type Γ (/ e_0 e_1) τ)]
  [
   (infer-type Γ e (× τ_0 τ_1))
   --- I-Fst
   (infer-type Γ (fst e) τ_0)]
  [
   (infer-type Γ e (× τ_0 τ_1))
   --- I-Snd
   (infer-type Γ (snd e) τ_1)])

(module+ test
  (test-case "well-typed"
    (check-true (judgment-holds (well-typed () (+ 2 2) Int)))
    (check-true (judgment-holds (well-typed () (+ 2 2) Nat)))
    (check-true (judgment-holds (well-typed ((x : Int) ()) (λ (y : Nat) (+ y x)) (→ Nat Int))))
    (check-false (judgment-holds (well-typed () (λ (C : Int) C) (→ Nat Nat))))
  )

  (test-case "not well-typed"
    (check-false (judgment-holds (well-typed () x Int)))
    (check-false (judgment-holds (well-typed () (2 2) Int)))
    (check-false (judgment-holds (well-typed ((x : Nat) ()) (λ (x : (× Int Int)) z) (→ (× Int Int) Int))))))

;; This reduction relation assumes its inputs are well-typed terms.
(define typed-step
  (reduction-relation LS
    #:domain A
    (--> (in-hole E (v_0 v_1))
         (in-hole E e_subst)
         E-App
         (where (λ (x : τ) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (in-hole E (+ integer_0 integer_1))
         (in-hole E integer_2)
         E-+
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (/ integer_0 integer_1))
         (in-hole E integer_2)
         E-/-0
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (in-hole E (/ integer_0 integer_1))
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (side-condition (zero? (term integer_1))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))))

(module+ test
  (define typed-step*
    (make--->* typed-step))

  (test-case "typed-step*"
    (check-equal?
      (typed-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (typed-step* (term ((λ (x : Int) (+ x x)) 2)))
      (term 4))
    (check-false (redex-match? LS v
       (typed-step* (term (0 0)))))
    (check-false (redex-match? LS v
      (typed-step* (term (+ (λ (z : Int) z) 0)))))
    (check-true (redex-match? LS BE
      (typed-step* (term (/ 1 0)))))
    (check-equal?
      (typed-step* (term (/ 7 6)))
      (term 1))
    (check-false (redex-match? LS v
      (typed-step* (term (fst 0)))))))

;; -----------------------------------------------------------------------------

(define-metafunction LS
  theorem:typed-safety : e τ -> any
  [(theorem:typed-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-step* (term e) (term τ) is-error? assert-well-typed typed-step))])

(define (is-error? A)
  (term #{error? ,A}))

(define (assert-well-typed e ty)
  (unless (judgment-holds (well-typed () ,e ,ty))
    (raise-arguments-error 'safe-step* "well-typed expression"
      "term" e
      "type" ty)))

(module+ test
  (test-case "typed-safety"
    (check-true
      (redex-check LS #:satisfying (well-typed () e τ)
        (term (theorem:typed-safety e τ))
        #:attempts 1000
        #:print? #f))))

