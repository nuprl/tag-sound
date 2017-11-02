#lang mf-apply racket/base


(require
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-identity
  LM
  (E ::= .... (static τ E) (dynamic τ E)))

;; This `identity-step` is just a `dyn-step` that passes through boundaries.
(define identity-step
  (reduction-relation LM-identity
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
         (side-condition (not (redex-match? LM-identity Λ (term v_0)))))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error ,(if (redex-match? LM-identity integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LM-identity integer (term v_0))
                                   (redex-match? LM-identity integer (term v_1))))))
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
         (Type-Error ,(if (redex-match? LM-identity integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LM-identity integer (term v_0))
                                   (redex-match? LM-identity integer (term v_1))))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (fst v))
         (Type-Error v "pair?")
         E-fst-1
         (side-condition (not (redex-match? LM-identity (× v_0 v_1) (term v)))))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (Type-Error v "pair?")
         E-snd-1
         (side-condition (not (redex-match? LM-identity (× v_0 v_1) (term v)))))
    (--> (in-hole E (static τ v))
         (in-hole E v)
         E-static)
    (--> (in-hole E (dynamic τ v))
         (in-hole E v)
         E-dynamic)))

(define identity-step*
  (make--->* identity-step))

(module+ test
  (test-case "identity-step*"
    (check-equal?
      (identity-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (identity-step* (term ((λ (x) (+ x x)) 2)))
      (term 4))
    (check-equal?
      (identity-step* (term ((λ (x : Int) (+ x x)) 2)))
      (term 4))
    (check-true (redex-match? LM-identity TE
      (identity-step* (term (0 0)))))
    (check-true (redex-match? LM-identity TE
      (identity-step* (term (+ (λ (z) z) 0)))))
    (check-true (redex-match? LM-identity TE
      (identity-step* (term (+ (λ (z : Int) z) 0)))))
    (check-true (redex-match? LM-identity BE
      (identity-step* (term (/ 1 0)))))
    (check-equal?
      (identity-step* (term (/ 1 3)))
      (term 0))
    (check-true (redex-match? LM-identity TE
      (identity-step* (term (fst 0)))))))

(define (assert-well-mixed t)
  (unless (judgment-holds (well-mixed () ,t))
    (raise-arguments-error 'safe-identity-step* "well-mixed expression" "term" t)))

(define-metafunction LM-identity
  theorem:identity-safety : e MAYBE-τ -> any
  [(theorem:identity-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (term #{safe-identity-step* e}))]
  [(theorem:identity-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (term #{safe-identity-step* e}))])

(define-metafunction LM-identity
  safe-identity-step* : A -> A
  [(safe-identity-step* TE)
   TE]
  [(safe-identity-step* BE)
   BE]
  [(safe-identity-step* e)
   ,(begin
      (void (assert-well-mixed (term e)))
      (let ([A* (apply-reduction-relation identity-step (term e))])
        (cond
         [(null? A*)
          (term e)]
         [(null? (cdr A*))
          (term #{safe-identity-step* ,(car A*)})]
         [else
          (raise-arguments-error 'safe-identity-step* "identity-step is non-deterministic for expression"
            "e" (term e)
            "answers" A*)])))])

;; `well-mixed` is invariant over evaluation,
;;  similar to `well-dyn` but allows more terms
(define-judgment-form LM-identity
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
   (where Γ_x (x Γ))
   (well-mixed Γ_x e)
   --- M-Fun-0
   (well-mixed Γ (λ (x) e))]
  [
   (where Γ_x (x Γ))
   (well-mixed Γ_x e)
   --- M-Fun-1
   (well-mixed Γ (λ (x : τ) e))]
  [
   (where #true #{type-env-contains Γ x})
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

  (define (safe? t ty)
    (and (term #{theorem:identity-safety ,t ,ty}) #true))

  (test-case "identity-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
  )

  (test-case "identity-safety:auto"
    (check-true
      (redex-check LM-identity #:satisfying (well-dyn () e)
        (term (theorem:identity-safety e #f))
        #:attempts 10
        #:print? #f))
    (check-true
      (redex-check LM-identity #:satisfying (well-typed () e τ)
        (term (theorem:identity-safety e τ))
        #:attempts 10
        #:print? #f))))

