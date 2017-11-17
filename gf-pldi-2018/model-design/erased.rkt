#lang mf-apply racket/base

;; Type-erased embedding.
;; - ignore types at runtime
;; - static->dynamic: no-op
;; - dynamic->static: no-op
;; - use a dynamically-typed semantics; always check e.g. that + gets 2 integers

(require
  "mixed.rkt"
  "redex-helpers.rkt"
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-erased
  LM
  (E ::= .... (static τ E) (dynamic τ E))
  ;; The erased semantics uses the same reduction relation
  ;;  for all terms (whether statically-typed or dynamically-typed).
  ;; So it's safe to reduce under a type boundary.
)

;; -----------------------------------------------------------------------------

;; This `erased-step` is just an extension of `dyn-step` that passes through
;;  type boundaries.
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
         (where #false #{procedure? v_0}))
    (--> (in-hole E (+ integer_0 integer_1))
         (in-hole E integer_2)
         E-+-0
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error v_0 "integer")
         E-+-1
         (where #false #{integer? v_0}))
    (--> (in-hole E (+ v_0 v_1))
         (Type-Error v_1 "integer")
         E-+-2
         (where #true #{integer? v_0})
         (where #false #{integer? v_1}))
    (--> (in-hole E (/ integer_0 integer_1))
         (in-hole E integer_2)
         E-/-0
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (in-hole E (/ integer_0 integer_1))
         (Boundary-Error integer_1 "non-zero integer")
         E-/-1
         (side-condition (zero? (term integer_1))))
    (--> (in-hole E (/ v_0 v_1))
         (Type-Error v_0 "integer")
         E-/-2
         (where #false #{integer? v_0}))
    (--> (in-hole E (/ v_0 v_1))
         (Type-Error v_1 "integer")
         E-/-3
         (where #true #{integer? v_0})
         (where #false #{integer? v_0}))
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
         (where #false #{pair? v}))
    (--> (in-hole E (static τ v))
         (in-hole E v)
         E-static)
    (--> (in-hole E (dynamic τ v))
         (in-hole E v)
         E-dynamic)))

(module+ test
  (define erased-step*
    (make--->* erased-step))

  (test-case "erased-step*"
    (check-equal?
      (erased-step* (term (+ 2 2)))
      (term 4))
    (check-equal?
      (erased-step* (term ((λ (x) (+ x x)) 2)))
      (term 4))
    (check-equal?
      (erased-step* (term ((λ (x) (+ x x)) 2)))
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

;; -----------------------------------------------------------------------------

;; Safety for the type-erased language is just term safety (from the
;;  dynamically-typed language).
;; If `e` is well-typed, or `e` is well-dyn, then either:
;; - e reduces to a value
;; - e reduces to a type error
;; - e reduces to a boundary error
;; - e diverges
;;
;; There is no guarantee that reduction preserves or respects types

(define-metafunction LM-erased
  theorem:erased-safety : e MAYBE-τ -> any
  [(theorem:erased-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term e) #f is-error? assert-well-mixed erased-step))]
  [(theorem:erased-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-step* (term e) (term τ) is-error? assert-well-mixed erased-step))])

(define (is-error? A)
  (term #{error? ,A}))

(define (assert-well-mixed t ty)
  (unless (judgment-holds (well-mixed () ,t))
    (raise-arguments-error 'safe-erased-step* "well-mixed expression" "term" t)))

;; `well-mixed` extends `well-dyn` to boundaries
;; (Strictly-speaking, we could erase type boundaries,
;;  but none of the other example languages do this.
;;  So it's better to keep them to prepare for what's next.)
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
    (check-true (safe? (term (λ (n) (× 0 0))) #f)))

  (test-case "erased-is-type-unsound"
    ;; "safe" terms can commit type errors at runtime ...
    ;; in other words it's possible that `Γ ⊢ e : τ` statically,
    ;;  but at run-time `e` evaluates to a value with a different type
    ;; (Dangers of moral turpitude)

    (check-equal?
      (term #{theorem:erased-safety (dynamic Int (λ (z) z)) Int})
      (term (λ (z) z)))
    ;; Simple example of type-unsoundness

    (check-equal?
      (term #{theorem:erased-safety ((λ (x : Int) x) (dynamic Int (× 0 0))) Int})
      (term (× 0 0)))
    ;; Type-unsound function application

    (check-equal?
      (term #{theorem:erased-safety ((λ (x : Nat) (+ x x)) (dynamic Nat -4)) Nat})
      (term -8))
    ;; Typed function returns value that doesn't match its codomain type
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
