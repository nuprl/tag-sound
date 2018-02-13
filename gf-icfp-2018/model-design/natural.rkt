#lang mf-apply racket/base

;; Natural embedding
;; - preserve types at runtime
;; - static->dynamic: defends typed functions, lets other values through
;; - dynamic->static: checks all untyped values, monitors functions to check all calls
;;
;; A type "is forever".
;; If an untyped function passes through a type boundary,
;;  then **every** time that function is called it gets checked against the
;;  return type.
;; This means function calls in untyped contexts can raise a boundary error
;;  (because of the latent type boundary around the lambda).
;;
;; - values include "monitors" that attach a type to a function
;; - semantics is via two mutually-recursive reduction relations,
;;   one for statically-typed terms
;;   and one for dynamically-typed terms.
;; - all statically-typed terms have a type safety ---
;;   this safety allows type errors in (embedded) untyped code

(require
  "mixed.rkt"
  "redex-helpers.rkt"
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-natural
  LM
  (v ::= .... (mon (→ τ τ) v))
  ;; A monitor value associates a type with a function, i.e. a monitor is
  ;;  a latent type boundary
)

(define-metafunction LM-natural
  maybe-in-hole : E A -> A
  [(maybe-in-hole E BE)
   BE]
  [(maybe-in-hole E TE)
   TE]
  [(maybe-in-hole E e)
   (in-hole E e)])

(define-metafunction LM-natural
  boundary? : e -> boolean
  [(boundary? (static τ _))
   #true]
  [(boundary? (dynamic τ _))
   #true]
  [(boundary? _)
   #false])

(define-metafunction LM-natural
  error? : A -> boolean
  [(error? BE)
   #true]
  [(error? TE)
   #true]
  [(error? _)
   #false])

(define-metafunction LM-natural
  pair? : v -> boolean
  [(pair? (× _ _))
   #true]
  [(pair? _)
   #false])

(define-metafunction LM-natural
  procedure? : v -> boolean
  [(procedure? Λ)
   #true]
  [(procedure? (mon (→ τ_dom τ_cod) v))
   #true] ;; could recur, but always true currently
  [(procedure? _)
   #false])

;; -----------------------------------------------------------------------------

;; The most interesting part of the natural embedding is how it
;;  brings terms across a type boundary

(define-metafunction LM-natural
  static->dynamic : τ v -> A
  [(static->dynamic (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)]
  [(static->dynamic (× τ_0 τ_1) (× v_0 v_1))
   BE
   (where BE #{static->dynamic τ_0 v_0})]
  [(static->dynamic (× τ_0 τ_1) (× v_0 v_1))
   BE
   (where BE #{static->dynamic τ_1 v_1})]
  [(static->dynamic (× τ_0 τ_1) (× v_0 v_1))
   (× #{static->dynamic τ_0 v_0} #{static->dynamic τ_1 v_1})]
  [(static->dynamic τ v)
   v])

(define-metafunction LM-natural
  dynamic->static : τ v -> A
  [(dynamic->static Nat natural)
   natural]
  [(dynamic->static Nat v)
   (Boundary-Error v "Nat")]
  [(dynamic->static Int integer)
   integer]
  [(dynamic->static Int v)
   (Boundary-Error v "Int")]
  [(dynamic->static (× τ_0 τ_1) (× v_0 v_1))
   BE
   (where BE (dynamic->static τ_0 v_0))]
  [(dynamic->static (× τ_0 τ_1) (× v_0 v_1))
   BE
   (where BE (dynamic->static τ_1 v_1))]
  [(dynamic->static (× τ_0 τ_1) (× v_0 v_1))
   (× (dynamic->static τ_0 v_0) (dynamic->static τ_1 v_1))]
  [(dynamic->static (× τ_0 τ_1) v)
   (Boundary-Error v ,(format "~a" (term (× τ_0 τ_1))))]
  [(dynamic->static (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)
   (where #true (procedure? v))]
  [(dynamic->static (→ τ_dom τ_cod) v)
   (Boundary-Error v ,(format "~a" (term (→ τ_dom τ_cod))))])

;; -----------------------------------------------------------------------------

;; Summary of reduction relations:
;; - `dyn-step` reduces dynamically-typed leaf terms
;; - `sta-step` reduces statically-typed leaf terms
;; - `dyn-boundary-step` : cross type boundaries, applied dyn-step or sta-step at leaf
;; - `sta-boundary-step` : ditto, but outermost context is statically typed

;; dyn-step checks for ill-typed terms
(define dyn-step
  (reduction-relation LM-natural
    #:domain A
    (--> (v_0 v_1)
         e_subst
         E-App-0
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (v_0 v_1)
         (static τ_cod (v (dynamic τ_dom v_1)))
         E-App-1
         (where (mon (→ τ_dom τ_cod) v) v_0))
    (--> (v_0 v_1)
         (Type-Error v_0 "procedure?")
         E-App-2
         (where #false (procedure? v_0)))
    (--> (+ integer_0 integer_1)
         integer_2
         E-+-0
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (+ v_0 v_1)
         (Type-Error v_0 "integer")
         E-+-1
         (where #false #{integer? v_0}))
    (--> (+ v_0 v_1)
         (Type-Error v_1 "integer")
         E-+-2
         (where #true #{integer? v_0})
         (where #false #{integer? v_1}))
    (--> (/ integer_0 integer_1)
         integer_2
         E-/-0
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (/ integer_0 integer_1)
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (side-condition (zero? (term integer_1))))
    (--> (/ v_0 v_1)
         (Type-Error v_0 "integer")
         E-/-2
         (where #false #{integer? v_0}))
    (--> (/ v_0 v_1)
         (Type-Error v_1 "integer")
         E-/-3
         (where #true #{integer? v_0})
         (where #false #{integer? v_1}))
    (--> (fst v)
         v_0
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (fst v)
         (Type-Error v "pair?")
         E-fst-1
         (where #false #{pair? v}))
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (snd v)
         (Type-Error v "pair?")
         E-snd-1
         (where #false #{pair? v}))))

(define sta-step
  (reduction-relation LM-natural
    #:domain A
    (--> (v_0 v_1)
         e_subst
         E-App-0
         (where (λ (x : τ) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (v_0 v_1)
         (dynamic τ_cod (v (static τ_dom v_1)))
         E-App-1
         (where (mon (→ τ_dom τ_cod) v) v_0))
    (--> (+ integer_0 integer_1)
         integer_2
         E-+
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (/ integer_0 integer_1)
         integer_2
         E-/-0
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (/ integer_0 integer_1)
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (side-condition (zero? (term integer_1))))
    (--> (fst v)
         v_0
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))))

(module+ test

  (test-case "dyn-step"
    (check-true (stuck? dyn-step (term (dynamic Int 3))))
    (check-true (stuck? dyn-step (term (static Int 3))))
    (check-true (stuck? dyn-step (term ((λ (x : Int) x) 42))))

    (check-equal? (apply-reduction-relation dyn-step (term ((λ (x) x) 42))) '(42))
    (check-equal? (apply-reduction-relation dyn-step (term (+ 2 3))) '(5))
    (check-equal? (apply-reduction-relation dyn-step (term ((mon (→ Int Int) (λ (x : Int) x)) 5)))
                  (list (term (static Int ((λ (x : Int) x) (dynamic Int 5))))))
    )

  (test-case "sta-step"
    (check-true (stuck? sta-step (term (dynamic Int 3))))
    (check-true (stuck? sta-step (term (static Int 3))))
    (check-true (stuck? sta-step (term ((λ (x) x) 42))))
    (check-true (stuck? sta-step (term (+ 1 (λ (x) x)))))
    (check-true (stuck? sta-step (term (snd (λ (x) x)))))

    (check-equal? (apply-reduction-relation sta-step (term ((λ (x : Int) x) 42))) '(42))
    (check-equal? (apply-reduction-relation sta-step (term (/ 7 2))) '(3))
    (check-equal? (apply-reduction-relation sta-step (term ((mon (→ Int Int) (λ (x) x)) 5)))
                  (list (term (dynamic Int ((λ (x) x) (static Int 5))))))
  )
)

(define dyn-boundary-step
  (reduction-relation LM-natural
    #:domain A
    (--> (in-hole E (static τ v))
         (maybe-in-hole E A)
         E-Cross-Boundary
         (where A (static->dynamic τ v)))
    (--> (in-hole E (static τ e))
         (in-hole E (static τ e_+))
         E-Advance-0
         (where (e_+) ,(apply-reduction-relation sta-boundary-step (term e))))
    (--> (in-hole E (static τ e))
         A
         E-Advance-1
         (where (A) ,(apply-reduction-relation sta-boundary-step (term e)))
         (where #true #{error? A}))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Dyn
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation dyn-step (term e))))))

(define sta-boundary-step
  (reduction-relation LM-natural
    #:domain A
    (--> (in-hole E (dynamic τ v))
         (maybe-in-hole E A)
         E-Cross-Boundary
         (where A (dynamic->static τ v)))
    (--> (in-hole E (dynamic τ e))
         (in-hole E (dynamic τ e_+))
         E-Advance-0
         (where (e_+) ,(apply-reduction-relation dyn-boundary-step (term e))))
    (--> (in-hole E (dynamic τ e))
         A
         E-Advance-1
         (where (A) ,(apply-reduction-relation dyn-boundary-step (term e)))
         (where #true #{error? A}))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Sta
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation sta-step (term e))))))

(module+ test

  (test-case "dyn-boundary-step"
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (+ 2 2)))
                  '(4))
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (static Int 3)))
                  '(3))
    (check-true (redex-match? LM-natural A
      (term (in-hole hole (static Int (+ 1 2))))))
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (static Int (+ 1 2))))
                  (list (term (static Int 3))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation dyn-boundary-step (term (/ 1 0))))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation dyn-boundary-step (term (static Int (/ 1 0)))))))

    (check-true (stuck? dyn-boundary-step (term (dynamic Int 3))))

    (check-equal? (apply-reduction-relation dyn-boundary-step
                    (term (static Nat ((λ (x : Nat) (+ x x)) (dynamic Nat 7)))))
                  (list (term (static Nat ((λ (x : Nat) (+ x x)) 7)))))
    (check-equal? (apply-reduction-relation dyn-boundary-step
                    (term (static Nat ((λ (x : Nat) (+ x x)) 7))))
                  (list (term (static Nat (+ 7 7)))))
    (check-equal? (apply-reduction-relation dyn-boundary-step
                    (term (static Nat (+ 7 7))))
                  (list (term (static Nat 14))))

    (check-true (redex-match? LM-natural TE
      (car (apply-reduction-relation dyn-boundary-step
             (term (static Int (dynamic Int (fst 0))))))))
  )

  (test-case "sta-boundary-step"
    (check-equal? (apply-reduction-relation sta-boundary-step (term (+ 2 2)))
                  '(4))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat 3)))
                  '(3))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat (+ 1 2))))
                  (list (term (dynamic Nat 3))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation sta-boundary-step (term (/ 1 0))))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (/ 1 0)))))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (λ (x) x)))))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (× 0 0)))))))
    (check-true (redex-match? LM-natural BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Nat -1))))))

    (check-true (stuck? sta-boundary-step (term (static Int 3))))

    (check-true (redex-match? LM-natural TE
      (car (apply-reduction-relation sta-boundary-step
             (term (dynamic Int (fst 0)))))))
  )
)

(module+ test
  (define dyn-step*
    (make--->* dyn-boundary-step))

  (define sta-step*
    (make--->* sta-boundary-step))

  (test-case "dyn-step*"
    (check-equal? (dyn-step* (term (+ (+ 1 1) (+ 1 1))))
                  4)
    (check-equal? (dyn-step* (term ((mon (→ Nat Nat) (λ (x : Nat) (+ x x))) 7)))
                  14)
    (check-equal? (dyn-step* (term ((static (→ Nat Nat) (λ (n : Nat) (+ n n))) 7)))
                  14)
    (check-equal? (dyn-step* (term (/ 10 (static Nat ((λ (x : (× Int Int)) (fst x)) (× 2 5))))))
                  5))

  (test-case "sta-step*"
    (check-equal? (sta-step* (term ((λ (x : (× Nat Nat)) (+ (fst x) (snd x))) (× 2 3))))
                  5)
    (check-equal? (sta-step* (term ((λ (x : Nat) (+ x x)) (dynamic Nat 7))))
                  14)
    (check-equal? (sta-step* (term ((dynamic (→ Nat Nat) (λ (n) (+ n n))) 7)))
                  14)
    (check-equal? (sta-step* (term (/ 10 (dynamic Nat ((λ (x) (fst x)) (× 2 5))))))
                  5)
    (check-true (redex-match? LM-natural BE
      (sta-step* (term ((λ (f : (→ Nat Nat)) (f 0)) (dynamic (→ Nat Nat) (λ (z) -2)))))))
  )
)

;; -----------------------------------------------------------------------------

(define-metafunction LM-natural
  theorem:natural-safety : e MAYBE-τ -> any
  [(theorem:natural-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term e) #f is-error? assert-well-dyn dyn-boundary-step))]
  [(theorem:natural-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-step* (term e) (term τ) is-error? assert-well-typed sta-boundary-step))])

(define (is-error? A)
  (term #{error? ,A}))

(define (assert-well-dyn t dont-care)
  (unless (judgment-holds (well-dyn/natural () ,t))
    (raise-arguments-error 'current-runtime-invariant "expected well-dyn" "term" t)))

(define (assert-well-typed t ty)
  (unless (judgment-holds (well-typed/natural () ,t ,ty))
    (raise-arguments-error 'current-runtime-invariant "expected well-typed"
      "term" t
      "type" ty)))

;; -----------------------------------------------------------------------------
;; --- TODO: these judgments are very similar to the ones in `mixed.rkt`,
;;      just add new rules for monitors and dispatch to the correct judgment
;;      for the mutual recursion.
;;
;;     It would be nice to be able to use `define-extended-judgment-form`,
;;      but that doesn't work for recursive calls.

(define-judgment-form LM-natural
  #:mode (well-dyn/natural I I)
  #:contract (well-dyn/natural Γ e)
  [
   --- D-Int
   (well-dyn/natural Γ integer)]
  [
   (well-dyn/natural Γ e_0)
   (well-dyn/natural Γ e_1)
   --- D-Pair
   (well-dyn/natural Γ (× e_0 e_1))]
  [
   (where Γ_x (x Γ))
   (well-dyn/natural Γ_x e)
   --- D-Fun
   (well-dyn/natural Γ (λ (x) e))]
  [
   (where #true (type-env-contains Γ x))
   --- D-Var
   (well-dyn/natural Γ x)]
  [
   (well-dyn/natural Γ e_0)
   (well-dyn/natural Γ e_1)
   --- D-App
   (well-dyn/natural Γ (e_0 e_1))]
  [
   (well-dyn/natural Γ e_0)
   (well-dyn/natural Γ e_1)
   --- D-Binop
   (well-dyn/natural Γ (BINOP e_0 e_1))]
  [
   (well-dyn/natural Γ e)
   --- D-Unop
   (well-dyn/natural Γ (UNOP e))]
  [
   (well-typed/natural Γ e τ)
   --- D-Static
   (well-dyn/natural Γ (static τ e))]
  [
   --- D-Mon
   (well-dyn/natural Γ (mon (→ τ_dom τ_cod) v))])

(define-judgment-form LM-natural
  #:mode (well-typed/natural I I I)
  #:contract (well-typed/natural Γ e τ)
  [
   (infer-type Γ e τ_infer)
   (subtype τ_infer τ)
   ---
   (well-typed/natural Γ e τ)])

(define-judgment-form LM-natural
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
   (well-dyn/natural Γ e)
   --- I-Dynamic
   (infer-type Γ (dynamic τ e) τ)]
  [
   --- I-Mon
   (infer-type Γ (mon (→ τ_dom τ_cod) v) (→ τ_dom τ_cod))])

;; -----------------------------------------------------------------------------

(module+ test

  (define (safe? t ty)
    (and (term #{theorem:natural-safety ,t ,ty}) #true))

  (test-case "natural-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
    (check-true (safe? (term (λ (n : Nat) (× 0 0))) (term (→ Nat (× Nat Nat)))))
    (check-true (safe? (term (+ (fst (fst (fst (dynamic (× (× (× Int Nat) (→ Nat (× Int Int))) Int) 0)))) (fst (dynamic (× Int (× (× Int Int) Nat)) 0)))) (term Int)))
    (check-true (safe? (term (dynamic (→ Int Int) (λ (x) x))) (term (→ Int Int))))
    (check-true (safe? (term (static (× (→ (× (→ Int Int) Int) Nat) (→ Int Nat)) (× (λ (R : (× (→ Int Int) Int)) 2) (λ (r : Int) 2)))) #f))
  )

  (test-case "natural-is-type-sound"
    ;; Programs that succeed in the erased embedding but commit type errors
    ;;  are identified as unsafe by the natural embedding

    (check-true (redex-match? LM-natural BE
      (term #{theorem:natural-safety (dynamic Int (λ (z) z)) Int})))
    (check-true (redex-match? LM-natural BE
      (term #{theorem:natural-safety ((λ (x : Int) x) (dynamic Int (× 0 0))) Int})))
    (check-true (redex-match? LM-natural BE
      (term #{theorem:natural-safety ((λ (x : Nat) (+ x x)) (dynamic Nat -4)) Nat})))
  )

  (test-case "natural-eager-errors"
    (check-true (redex-match? LM-natural BE
      (term #{theorem:natural-safety (dynamic (× Int Int) (× 1 (λ (x) x))) (× Int Int)}))))

  (test-case "natural-safety:auto"
    (check-true
      (redex-check LM-natural #:satisfying (well-dyn () e)
        (term (theorem:natural-safety e #f))
        #:attempts 1000
        #:print? #f))
    (check-true
      (redex-check LM-natural #:satisfying (well-typed () e τ)
        (term (theorem:natural-safety e τ))
        #:attempts 1000
        #:print? #f)))
)

