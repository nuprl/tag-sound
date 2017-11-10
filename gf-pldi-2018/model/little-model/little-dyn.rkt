#lang mf-apply racket/base

;; Model of a dynamically-typed lambda calculus.
;; - values are: integers, pairs, functions
;; - well-formed terms: are closed --- no free variables
;; - safety: progress/preservation for well-formed terms

;; This is just a simple dynamically typed language.
;; No surprises.

(require
  "redex-helpers.rkt"
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-language LD
  (e ::= v x (e e) (× e e) (BINOP e e) (UNOP e))
  (v ::= integer (× v v) (λ (x) e))
  (UNOP ::= fst snd)
  (BINOP ::= + /)
  ;; Integer division `/` is an example of a partial primitive operation

  (E ::= hole (E e) (v E) (× E e) (× v E) (BINOP E e) (BINOP v E) (UNOP E))
  ;; Left-to-right evaluation contexts

  (Γ ::= () (x Γ))
  ;; Variable environment, used to check that expressions are closed

  (A ::= e TE BE)
  ;; The operational semantics is a partial function on answers `A`.
  ;; An answer is one of:
  ;; - `e` : an expression
  ;; - `BE` : a boundary error message
  ;; - `TE` : a type error message

  (BE ::= (Boundary-Error e string))
  ;; A boundary error occurs when a bad value attempts to cross
  ;;  from the language to a primitive operation.
  ;; In this language, the only boundary error is from division by zero.

  (TE ::= (Type-Error e string))
  ;; A type error occurs when the reduction relation finds an expression
  ;;  with "the wrong shape", e.g. an application where the left-side value
  ;;  is not a function or primitive operation.

  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))

(module+ test
  (test-case "valid terms"
    ;; The grammar can express terms that have a well-defined semantics
    ;;  (reduce to a value or error)
    ;;  and terms that have undefined behavior

    (check-true (redex-match? LD e (term (+ 1 -4))))
    ;; Reduces to a value

    (check-true (redex-match? LD e (term (0 1))))
    ;; Reduces to a type error

    (check-true (redex-match? LD e (term (/ 0 0))))
    ;; Reduces to a boundary error

    (check-true (redex-match? LD e (term (f x))))
    ;; Undefined behavior

    (check-true (redex-match? LD e (term ((λ (x) (x x)) (λ (x) (x x))))))
    ;; Diverges

    (void)))

(define-metafunction LD
  error? : A -> boolean
  [(error? TE)
   #true]
  [(error? BE)
   #true]
  [(error? _)
   #false])

(define-metafunction LD
  integer? : v -> boolean
  [(integer? integer)
   #true]
  [(integer? _)
   #false])

(define-metafunction LD
  pair? : v -> boolean
  [(pair? (× _ _))
   #true]
  [(pair? _)
   #false])

(define-metafunction LD
  procedure? : v -> boolean
  [(procedure? (λ (x) e))
   #true]
  [(procedure? _)
   #false])

(define-metafunction LD
  type-env-contains : Γ x -> boolean
  [(type-env-contains () x)
   #false]
  [(type-env-contains (x Γ) x)
   #true]
  [(type-env-contains (x_0 Γ) x)
   (type-env-contains Γ x)])

;; -----------------------------------------------------------------------------

;; A `well-dyn` term is closed; it contains no free variables.
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
   (where Γ_x (x Γ))
   (well-dyn Γ_x e)
   --- T-Fun
   (well-dyn Γ (λ (x) e))]
  [
   (where #true (type-env-contains Γ x))
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
    (check-true (judgment-holds (well-dyn (x ()) (λ (y) (+ y x))))))

  (test-case "not well-dyn"
    (check-false (judgment-holds (well-dyn () x)))
    (check-false (judgment-holds (well-dyn (x ()) (λ (x) z))))))

;; Reduction relation,
;;  maps dynamically-typed terms to "terms or errors"
;; Undefined for free variables, values, and error labels.
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
         (where #false #{procedure? v_0}))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+-0
         (where #true #{integer? v_0})
         (where #true #{integer? v_1})
         (where integer_2 ,(+ (term v_0) (term v_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error v_0 "integer?")
         E-+-1
         (where #false #{integer? v_0}))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error v_1 "integer?")
         E-+-2
         (where #true #{integer? v_0})
         (where #false #{integer? v_1}))
    (--> (in-hole E (/ v_0 v_1))
         (in-hole E integer_2)
         E-/-0
         (where #true #{integer? v_0})
         (where #true #{integer? v_1})
         (side-condition (not (zero? (term v_1))))
         (where integer_2 ,(quotient (term v_0) (term v_1))))
    (--> (in-hole E (/ v_0 v_1))
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (where #true #{integer? v_0})
         (where #true #{integer? v_1})
         (side-condition (zero? (term v_1))))
    (--> (in-hole E (/ v_0 v_1))
         (Type-Error v_0 "integer")
         E-/-2
         (where #false #{integer? v_0}))
    (--> (in-hole E (/ v_0 v_1))
         (Type-Error v_1 "integer")
         E-/-3
         (where #true #{integer? v_0})
         (where #false #{integer? v_1}))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (fst v))
         (Type-Error v "pair?")
         E-fst-1
         (where #false #{pair? v}))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (Type-Error v "pair?")
         E-snd-1
         (where #false #{pair? v}))))

(module+ test
  (define dyn-step*
    (make--->* dyn-step))

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

;; -----------------------------------------------------------------------------

;; Safety theorem:
;;  if `e` is a well-formed expression, then evaluating `e` either:
;;  - reduces to a value
;;  - reduces to a type error
;;  - reduces to a boundary error
;;  - diverges
(define-metafunction LD
  theorem:dyn-safety : e -> any
  [(theorem:dyn-safety e)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term e) #f is-error? assert-well-dyn dyn-step))])

(define (is-error? A)
  (term #{error? ,A}))

(define (assert-well-dyn e ty)
  (unless (judgment-holds (well-dyn () ,e))
    (raise-argument-error 'safe-dyn-step* "well-dyn expression" e)))

(module+ test
  (test-case "dyn-safety"
    (check-true
      (redex-check LD #:satisfying (well-dyn () e)
        (term (theorem:dyn-safety e))
        #:attempts 500
        #:print? #f))))

