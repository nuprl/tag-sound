#lang mf-apply racket/base

(require
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language LM
  (e ::= v x (e e) (× e e) (BINOP e e) (UNOP e) (static τ e) (dynamic τ e))
  (BINOP ::= + /)
  (UNOP ::= fst snd)
  (v ::= integer (× v v) Λ)
  (Λ ::= (λ (x : τ) e) (λ (x) e))
  (τ ::= Int Nat (× τ τ) (→ τ τ))
  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E)
         (static τ E) (dynamic τ E))
  (Γ ::= (x:τ ...))
  (x:τ ::= x (x : τ))
  (A ::= e TE BE)
  (BE ::= (Boundary-Error e string))
  (TE ::= (Type-Error e string))
  (MAYBE-τ ::= #f τ)
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x)
  (λ (x : τ) e #:refers-to x))

(module+ test
  (test-case "valid terms"
    (check-true (redex-match? LM e (term (+ 1 -4))))
    (check-true (redex-match? LM e (term (f x))))
    (check-true (redex-match? LM e (term (0 1))))))

(define-judgment-form LM
  #:mode (well-typed I I I)
  #:contract (well-typed Γ e τ)
  [
   (infer-type Γ e τ_infer)
   (subtype τ_infer τ)
   ---
   (well-typed Γ e τ)])

(define-judgment-form LM
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

(define-metafunction LM
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

(define-judgment-form LM
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e τ)
  [
   (side-condition ,(not (redex-match? LM natural (term integer))))
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
   (where (x:τ_0 ... (x : τ) x:τ_1 ...) Γ)
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
   (infer-type Γ (snd e) τ_1)]
  [
   (well-dyn Γ e)
   --- I-Dynamic
   (infer-type Γ (dynamic τ e) τ)])

(define-judgment-form LM
  #:mode (well-dyn I I)
  #:contract (well-dyn Γ e)
  [
   --- D-Int
   (well-dyn Γ integer)]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- D-Pair
   (well-dyn Γ (× e_0 e_1))]
  [
   (where Γ_x ,(cons (term x) (term Γ)))
   (well-dyn Γ_x e)
   --- D-Fun
   (well-dyn Γ (λ (x) e))]
  [
   (where (x:τ_0 ... x x:τ_1 ...) Γ)
   --- D-Var
   (well-dyn Γ x)]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- D-App
   (well-dyn Γ (e_0 e_1))]
  [
   (well-dyn Γ e_0)
   (well-dyn Γ e_1)
   --- D-Binop
   (well-dyn Γ (BINOP e_0 e_1))]
  [
   (well-dyn Γ e)
   --- D-Unop
   (well-dyn Γ (UNOP e))]
  [
   (well-typed Γ e τ)
   --- D-Static
   (well-dyn Γ (static τ e))])

(module+ test
  (test-case "well-typed"
    (check-true
      (judgment-holds (well-typed () (+ 2 (dynamic Int 2)) Int)))
    (check-true
      (judgment-holds (well-typed () (+ 2 (dynamic Int (static Nat 3))) Int)))
    (check-true
      (judgment-holds (well-typed () (+ 2 (dynamic Int (λ (x) x))) Int)))
    (check-true
      (judgment-holds (well-typed () ((dynamic (→ Int Int) (λ (x) (+ x 42))) 1) Int))))

  (test-case "well-dyn"
    (check-true
      (judgment-holds (well-dyn () (+ 2 (static Int 2)))))
    (check-true
      (judgment-holds (well-dyn () (+ 2 (static Int (dynamic Int (λ (x) x)))))))
    (check-true
      (judgment-holds (well-dyn () ((static (→ Int Int) (λ (x : Int) (+ x 1))) 4))))
    (check-false
      (judgment-holds (well-dyn () (λ (h : Nat) 2))))))

;; This `mixed-step` is just a `dyn-step` that passes through boundaries.
(define mixed-step
  (reduction-relation LM
    #:domain A
    (--> (in-hole E (v_0 v_1))
         (in-hole E e_subst)
         E-App-0
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (in-hole E (v_0 v_1))
         (in-hole E e_subst)
         E-App-1
         (where (λ (x : τ) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (in-hole E (v_0 v_1))
         (Type-Error v_0 "procedure?")
         E-App-2
         (side-condition (not (redex-match? LM Λ (term v_0)))))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error ,(if (redex-match? LM integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LM integer (term v_0))
                                   (redex-match? LM integer (term v_1))))))
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
         (Type-Error ,(if (redex-match? LM integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LM integer (term v_0))
                                   (redex-match? LM integer (term v_1))))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (fst v))
         (Type-Error v "pair?")
         E-fst-1
         (side-condition (not (redex-match? LM (× v_0 v_1) (term v)))))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (Type-Error v "pair?")
         E-snd-1
         (side-condition (not (redex-match? LM (× v_0 v_1) (term v)))))
    (--> (in-hole E (static τ v))
         (in-hole E v)
         E-static)
    (--> (in-hole E (dynamic τ v))
         (in-hole E v)
         E-dynamic)))

(define mixed-step*
  (make--->* mixed-step))

(module+ test
  (test-case "mixed-step*"
    (check-equal?
      (mixed-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (mixed-step* (term ((λ (x) (+ x x)) 2)))
      (term 4))
    (check-equal?
      (mixed-step* (term ((λ (x : Int) (+ x x)) 2)))
      (term 4))
    (check-true (redex-match? LM TE
      (mixed-step* (term (0 0)))))
    (check-true (redex-match? LM TE
      (mixed-step* (term (+ (λ (z) z) 0)))))
    (check-true (redex-match? LM TE
      (mixed-step* (term (+ (λ (z : Int) z) 0)))))
    (check-true (redex-match? LM BE
      (mixed-step* (term (/ 1 0)))))
    (check-equal?
      (mixed-step* (term (/ 1 3)))
      (term 0))
    (check-true (redex-match? LM TE
      (mixed-step* (term (fst 0)))))))

(define-metafunction LM
  theorem:identity-safety : e MAYBE-τ -> any
  [(theorem:identity-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (term #{safe-mixed-step* e}))]
  [(theorem:identity-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (term #{safe-mixed-step* e}))])

(define-metafunction LM
  safe-mixed-step* : A -> A
  [(safe-mixed-step* TE)
   TE]
  [(safe-mixed-step* BE)
   BE]
  [(safe-mixed-step* e)
   ,(raise-arguments-error 'safe-mixed-step* "well-mixed expression" "term" (term e))
   (side-condition (not (judgment-holds (well-mixed () e))))]
  [(safe-mixed-step* e)
   ,(let ([A* (apply-reduction-relation mixed-step (term e))])
      (cond
       [(null? A*)
        (term e)]
       [(null? (cdr A*))
        (term #{safe-mixed-step* ,(car A*)})]
       [else
        (raise-arguments-error 'safe-mixed-step* "mixed-step is non-deterministic for expression"
          "e" (term e)
          "answers" A*)]))])

;; `well-mixed` is invariant over evaluation,
;;  similar to `well-dyn` but allows more terms
(define-judgment-form LM
  #:mode (well-mixed I I)
  #:contract (well-mixed Γ e)
  [
   --- M-Int
   (well-mixed Γ integer)]
  [
   (well-mixed Γ e_0)
   (well-mixed Γ e_1)
   --- M-Pair
   (well-mixed Γ (× e_0 e_1))]
  [
   (where Γ_x ,(cons (term x) (term Γ)))
   (well-mixed Γ_x e)
   --- M-Fun-0
   (well-mixed Γ (λ (x) e))]
  [
   (where Γ_x ,(cons (term x) (term Γ)))
   (well-mixed Γ_x e)
   --- M-Fun-1
   (well-mixed Γ (λ (x : τ) e))]
  [
   (where (x:τ_0 ... x x:τ_1 ...) Γ)
   --- M-Var
   (well-mixed Γ x)]
  [
   (well-mixed Γ e_0)
   (well-mixed Γ e_1)
   --- M-App
   (well-mixed Γ (e_0 e_1))]
  [
   (well-mixed Γ e_0)
   (well-mixed Γ e_1)
   --- M-Binop
   (well-mixed Γ (BINOP e_0 e_1))]
  [
   (well-mixed Γ e)
   --- M-Unop
   (well-mixed Γ (UNOP e))]
  [
   (well-mixed Γ e)
   --- M-Static
   (well-mixed Γ (static τ e))]
  [
   (well-mixed Γ e)
   --- M-Dynamic
   (well-mixed Γ (dynamic τ e))])

(module+ test
  (check-metafunction theorem:identity-safety
    (λ (args) (term #{theorem:identity-safety ,@args}))))

