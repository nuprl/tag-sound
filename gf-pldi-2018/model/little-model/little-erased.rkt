#lang mf-apply racket/base


(require
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-erased
  LM
  (E ::= .... (static τ E) (dynamic τ E)))

;; This `erased-step` is just a `dyn-step` that passes through boundaries.
(define erased-step
  (reduction-relation LM-erased
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
         (side-condition (not (redex-match? LM-erased Λ (term v_0)))))
    (--> (in-hole E (+ v_0 v_1))
         (in-hole E integer_2)
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error ,(if (redex-match? LM-erased integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LM-erased integer (term v_0))
                                   (redex-match? LM-erased integer (term v_1))))))
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
         (Type-Error ,(if (redex-match? LM-erased integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LM-erased integer (term v_0))
                                   (redex-match? LM-erased integer (term v_1))))))
    (--> (in-hole E (fst v))
         (in-hole E v_0)
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (fst v))
         (Type-Error v "pair?")
         E-fst-1
         (side-condition (not (redex-match? LM-erased (× v_0 v_1) (term v)))))
    (--> (in-hole E (snd v))
         (in-hole E v_1)
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (in-hole E (snd v))
         (Type-Error v "pair?")
         E-snd-1
         (side-condition (not (redex-match? LM-erased (× v_0 v_1) (term v)))))
    (--> (in-hole E (static τ v))
         (in-hole E v)
         E-static)
    (--> (in-hole E (dynamic τ v))
         (in-hole E v)
         E-dynamic)))

(define erased-step*
  (make--->* erased-step))

(module+ test
  (test-case "erased-step*"
    (check-equal?
      (erased-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (erased-step* (term ((λ (x) (+ x x)) 2)))
      (term 4))
    (check-equal?
      (erased-step* (term ((λ (x : Int) (+ x x)) 2)))
      (term 4))
    (check-true (redex-match? LM-erased TE
      (erased-step* (term (0 0)))))
    (check-true (redex-match? LM-erased TE
      (erased-step* (term (+ (λ (z) z) 0)))))
    (check-true (redex-match? LM-erased TE
      (erased-step* (term (+ (λ (z : Int) z) 0)))))
    (check-true (redex-match? LM-erased BE
      (erased-step* (term (/ 1 0)))))
    (check-equal?
      (erased-step* (term (/ 1 3)))
      (term 0))
    (check-true (redex-match? LM-erased TE
      (erased-step* (term (fst 0)))))))

(define (assert-well-mixed t)
  (unless (judgment-holds (well-mixed () ,t))
    (raise-arguments-error 'safe-erased-step* "well-mixed expression" "term" t)))

(define-metafunction LM-erased
  theorem:erased-safety : e MAYBE-τ -> any
  [(theorem:erased-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (term #{safe-erased-step* e}))]
  [(theorem:erased-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (term #{safe-erased-step* e}))])

(define-metafunction LM-erased
  safe-erased-step* : A -> A
  [(safe-erased-step* TE)
   TE]
  [(safe-erased-step* BE)
   BE]
  [(safe-erased-step* e)
   ,(begin
      (void (assert-well-mixed (term e)))
      (let ([A* (apply-reduction-relation erased-step (term e))])
        (cond
         [(null? A*)
          (term e)]
         [(null? (cdr A*))
          (term #{safe-erased-step* ,(car A*)})]
         [else
          (raise-arguments-error 'safe-erased-step* "erased-step is non-deterministic for expression"
            "e" (term e)
            "answers" A*)])))])

;; `well-mixed` is invariant over evaluation,
;;  similar to `well-dyn` but allows more terms
(define-judgment-form LM-erased
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
    (and (term #{theorem:erased-safety ,t ,ty}) #true))

  (test-case "erased-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
  )

  (test-case "erased-safety:auto"
    (check-true
      (redex-check LM-erased #:satisfying (well-dyn () e)
        (term (theorem:erased-safety e #f))
        #:attempts 1000
        #:print? #f))
    (check-true
      (redex-check LM-erased #:satisfying (well-typed () e τ)
        (term (theorem:erased-safety e τ))
        #:attempts 1000
        #:print? #f)))
)
