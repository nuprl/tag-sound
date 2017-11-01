#lang mf-apply racket/base

(require
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language LS
  (e ::= v x (e e) (× e e) (BINOP e e) (UNOP e))
  (BINOP ::= + /)
  (UNOP ::= fst snd)
  (v ::= integer (× v v) (λ (x : τ) e))
  (τ ::= Int Nat (× τ τ) (→ τ τ))
  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E))
  (Γ ::= ((x : τ) ...))
  (A ::= e TE BE)
  (BE ::= (Boundary-Error e string))
  (TE ::= (Type-Error e string))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x : τ) e #:refers-to x))

(module+ test
  (test-case "valid terms"
    (check-true (redex-match? LS e (term (+ 1 -4))))
    (check-true (redex-match? LS e (term (f x))))
    (check-true (redex-match? LS e (term (0 1))))))

(define-judgment-form LS
  #:mode (well-typed I I I)
  #:contract (well-typed Γ e τ)
  [
   (infer-type Γ e τ_infer)
   (subtype τ_infer τ)
   ---
   (well-typed Γ e τ)])

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
  type-join : τ τ -> τ
  [(type-join τ_0 τ_1)
   τ_1
   (judgment-holds (subtype τ_0 τ_1))]
  [(type-join τ_0 τ_1)
   τ_0
   (judgment-holds (subtype τ_1 τ_0))]
  [(type-join τ_0 τ_1)
   ,(raise-arguments-error 'type-join "types do not have common super"
      "τ0" (term τ_0)
      "τ1" (term τ_1))])

(define-judgment-form LS
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e τ)
  [
   (side-condition ,(not (redex-match? LS natural (term integer))))
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
   (where Γ_x ,(cons (term (x : τ_0)) (term Γ)))
   (infer-type Γ_x e τ_1)
   --- I-Fun
   (infer-type Γ (λ (x : τ_0) e) (→ τ_0 τ_1))]
  [
   (where ((x_0 : τ_0) ... (x : τ) (x_1 : τ_1) ...) Γ)
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
    (check-true (judgment-holds (well-typed ((x : Int)) (λ (y : Nat) (+ y x)) (→ Nat Int)))))

  (test-case "not well-typed"
    (check-false (judgment-holds (well-typed () x Int)))
    (check-false (judgment-holds (well-typed () (2 2) Int)))
    (check-false (judgment-holds (well-typed ((x : Nat)) (λ (x : (× Int Int)) z) (→ (× Int Int) Int))))))

(define typed-step
  (reduction-relation LS
    #:domain A
    (--> (in-hole E (v_0 v_1))
         (in-hole E e_subst)
         E-App
         (where (λ (x : τ) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (/ v_0 v_1))
         (in-hole E integer_2)
         E-/-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (in-hole E (/ v_0 v_1))
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (zero? (term integer_1))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))))

(define typed-step*
  (make--->* typed-step))

(module+ test
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

(define-metafunction LS
  theorem:typed-safety : e τ -> any
  [(theorem:typed-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (let ([r (term #{safe-typed-step* e τ})])
          (if (or (redex-match? LS v r) (redex-match? LS BE r))
            r
            #false)))])

(define-metafunction LS
  safe-typed-step* : A τ -> A
  [(safe-typed-step* TE τ)
   TE]
  [(safe-typed-step* BE τ)
   BE]
  [(safe-typed-step* e τ)
   (Type-Error e ,(format "~a" (term τ)))
   (side-condition (not (judgment-holds (well-typed () e τ))))]
  [(safe-typed-step* e τ)
   ,(let ([A* (apply-reduction-relation typed-step (term e))])
      (cond
       [(null? A*)
        (term e)]
       [(null? (cdr A*))
        (term #{safe-typed-step* ,(car A*) τ})]
       [else
        (raise-arguments-error 'safe-typed-step* "typed-step is non-deterministic for expression"
          "e" (term e)
          "answers" A*)]))])

(module+ test
  (check-metafunction theorem:typed-safety
    (λ (args) (term #{theorem:typed-safety ,@args}))))

