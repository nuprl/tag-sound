#lang mf-apply racket/base

(provide
  LM
  well-typed
  well-dyn
  subtype
  type-join
  type-env-contains
  type-env-ref
  negative?

  safe-step*
  stuck?
)

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
  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E))
  (Γ ::= (x:τ Γ) ())
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
  type-join : τ τ -> MAYBE-τ
  [(type-join τ_0 τ_1)
   τ_1
   (judgment-holds (subtype τ_0 τ_1))]
  [(type-join τ_0 τ_1)
   τ_0
   (judgment-holds (subtype τ_1 τ_0))])

(define-judgment-form LM
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e τ)
  [
   (where #true #{negative? integer})
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
   (infer-type Γ (snd e) τ_1)]
  [
   (well-dyn Γ e)
   --- I-Dynamic
   (infer-type Γ (dynamic τ e) τ)])

(define-metafunction LM
  negative? : integer -> boolean
  [(negative? natural)
   #false]
  [(negative? integer)
   #true])

(define-metafunction LM
  type-env-ref : Γ x -> MAYBE-τ
  [(type-env-ref () x)
   #false]
  [(type-env-ref ((x : τ) Γ) x)
   τ]
  [(type-env-ref (x:τ Γ) x)
   (type-env-ref Γ x)])

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
   (where Γ_x (x Γ))
   (well-dyn Γ_x e)
   --- D-Fun
   (well-dyn Γ (λ (x) e))]
  [
   (where #true (type-env-contains Γ x))
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

(define-metafunction LM
  type-env-contains : Γ x -> boolean
  [(type-env-contains () x)
   #false]
  [(type-env-contains (x Γ) x)
   #true]
  [(type-env-contains (x:τ Γ) x)
   (type-env-contains Γ x)])

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

(define (stuck? r t)
  (null? (apply-reduction-relation r t)))

(define (safe-step* A ty done? check-invariant step)
  (let loop ([A A])
    (cond
     [(done? A)
      A]
     [else
      (check-invariant A ty)
      (define A* (apply-reduction-relation step A))
      (cond
       [(null? A*)
        A]
       [(null? (cdr A*))
        (loop (car A*))]
       [else
        (raise-arguments-error 'safe-step* "step is non-deterministic for expression"
          "e" A
          "answers" A*)])])))

