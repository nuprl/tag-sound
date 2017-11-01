#lang mf-apply racket/base

(require
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language LD
  (e ::= v x (e e) (× e e) (BINOP e e) (UNOP e))
  (BINOP ::= + /)
  (UNOP ::= fst snd)
  (v ::= integer (× v v) (λ (x) e))
  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E))
  (Γ ::= (x ...))
  (A ::= e TE BE)
  (BE ::= (Boundary-Error e string))
  (TE ::= (Type-Error e string))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))

(module+ test
  (test-case "valid terms"
    (check-true (redex-match? LD e (term (+ 1 -4))))
    (check-true (redex-match? LD e (term (f x))))
    (check-true (redex-match? LD e (term (0 1))))))

(define-judgment-form LD
  #:mode (well-dyn I I)
  #:contract (well-dyn Γ e)
  [
   --- T-Int
   (well-dyn Γ integer)]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- T-Pair
   (well-dyn Γ (× e_0 e_1))]
  [
   (where Γ_x ,(cons (term x) (term Γ)))
   (well-dyn Γ_x e)
   --- T-Fun
   (well-dyn Γ (λ (x) e))]
  [
   (where (x_0 ... x x_1 ...) Γ)
   --- T-Var
   (well-dyn Γ x)]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- T-App
   (well-dyn Γ (e_0 e_1))]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- T-Binop
   (well-dyn Γ (BINOP e_0 e_1))]
  [
   (well-dyn Γ e)
   --- T-Unop
   (well-dyn Γ (UNOP e))])

(module+ test
  (test-case "well-dyn"
    (check-true (judgment-holds (well-dyn () (+ 2 2))))
    (check-true (judgment-holds (well-dyn () (2 2))))
    (check-true (judgment-holds (well-dyn (x) (λ (y) (+ y x))))))

  (test-case "not well-dyn"
    (check-false (judgment-holds (well-dyn () x)))
    (check-false (judgment-holds (well-dyn (x) (λ (x) z))))))

(define dyn-step
  (reduction-relation LD
    #:domain A
    (--> (in-hole E (v_0 v_1))
         (in-hole E e_subst)
         E-App-0
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (in-hole E (v_0 v_1))
         (Type-Error v_0 "procedure?")
         E-App-1
         (side-condition (not (redex-match? LD (λ (x) e) (term v_0)))))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error ,(if (redex-match? LD integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LD integer (term v_0))
                                   (redex-match? LD integer (term v_1))))))
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
    (--> (in-hole E (/ v_0 v_1))
         (Type-Error ,(if (redex-match? LD integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LD integer (term v_0))
                                   (redex-match? LD integer (term v_1))))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (fst v))
         (Type-Error v "pair?")
         E-fst-1
         (side-condition (not (redex-match? LD (× v_0 v_1) (term v)))))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (Type-Error v "pair?")
         E-snd-1
         (side-condition (not (redex-match? LD (× v_0 v_1) (term v)))))))

(define dyn-step*
  (make--->* dyn-step))

(module+ test
  (test-case "dyn-step*"
    (check-equal?
      (dyn-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (dyn-step* (term ((λ (x) (+ x x)) 2)))
      (term 4))
    (check-true (redex-match? LD TE
      (dyn-step* (term (0 0)))))
    (check-true (redex-match? LD TE
      (dyn-step* (term (+ (λ (z) z) 0)))))
    (check-true (redex-match? LD BE
      (dyn-step* (term (/ 1 0)))))
    (check-equal?
      (dyn-step* (term (/ 1 3)))
      (term 0))
    (check-true (redex-match? LD TE
      (dyn-step* (term (fst 0)))))))

(define-metafunction LD
  theorem:dyn-safety : e -> any
  [(theorem:dyn-safety e)
   ,(or (not (judgment-holds (well-dyn () e)))
        (term #{safe-dyn-step* e}))])

(define-metafunction LD
  safe-dyn-step* : A -> A
  [(safe-dyn-step* TE)
   TE]
  [(safe-dyn-step* BE)
   BE]
  [(safe-dyn-step* e)
   ,(let ([A* (apply-reduction-relation dyn-step (term e))])
      (cond
       [(null? A*)
        (term e)]
       [(null? (cdr A*))
        (term #{safe-dyn-step* ,(car A*)})]
       [else
        (raise-arguments-error 'safe-dyn-step* "dyn-step is non-deterministic for expression"
          "e" (term e)
          "answers" A*)]))])

(module+ test
  (check-metafunction theorem:dyn-safety
    (λ (args) (term #{theorem:dyn-safety ,@args}))))

