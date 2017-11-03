#lang mf-apply racket/base

;; Lazy natural embedding
;; ... just add pair monitors
;;     otherwise its the same soundness

(provide
  LM-lazy
  procedure?
  pair?
  maybe-in-hole
  boundary?
)

(require
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-lazy
  LM
  (v ::= .... (mon (× τ τ) v) (mon (→ τ τ) v)))

(define-metafunction LM-lazy
  procedure? : v -> boolean
  [(procedure? Λ)
   #true]
  [(procedure? (mon (→ τ_dom τ_cod) v))
   #{procedure? v}]
  [(procedure? _)
   #false])

(define-metafunction LM-lazy
  pair? : v -> boolean
  [(pair? (× v_0 v_1))
   #true]
  [(pair? (mon (× τ_0 τ_1) v))
   #{pair? v}]
  [(pair? _)
   #false])

(define-metafunction LM-lazy
  maybe-in-hole : E A -> A
  [(maybe-in-hole E BE)
   BE]
  [(maybe-in-hole E TE)
   TE]
  [(maybe-in-hole E e)
   (in-hole E e)])

(define-metafunction LM-lazy
  boundary? : e -> boolean
  [(boundary? (static τ _))
   #true]
  [(boundary? (dynamic τ _))
   #true]
  [(boundary? _)
   #false])

(define dyn-step
  (reduction-relation LM-lazy
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
    (--> (+ v_0 v_1)
         integer_2
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (+ v_0 v_1)
         (Type-Error ,(if (redex-match? LM-lazy integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LM-lazy integer (term v_0))
                                   (redex-match? LM-lazy integer (term v_1))))))
    (--> (/ v_0 v_1)
         integer_2
         E-/-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (/ v_0 v_1)
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (zero? (term integer_1))))
    (--> (/ v_0 v_1)
         (Type-Error ,(if (redex-match? LM-lazy integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LM-lazy integer (term v_0))
                                   (redex-match? LM-lazy integer (term v_1))))))
    (--> (fst v)
         v_0
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (fst v)
         (static τ_0 (fst v_m))
         E-fst-1
         (where (mon (× τ_0 τ_1) v_m) v))
    (--> (fst v)
         (Type-Error v "pair?")
         E-fst-2
         (where #false #{pair? v}))
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (snd v)
         (static τ_1 (snd v_m))
         E-snd-1
         (where (mon (× τ_0 τ_1) v_m) v))
    (--> (snd v)
         (Type-Error v "pair?")
         E-snd-2
         (where #false #{pair? v}))))

(define sta-step
  (reduction-relation LM-lazy
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
    (--> (+ v_0 v_1)
         integer_2
         E-+
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (/ v_0 v_1)
         integer_2
         E-/-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (not (zero? (term integer_1))))
         (where integer_2 ,(quotient (term integer_0) (term integer_1))))
    (--> (/ v_0 v_1)
         (Boundary-Error v_1 "non-zero integer")
         E-/-1
         (where integer_0 v_0)
         (where integer_1 v_1)
         (side-condition (zero? (term integer_1))))
    (--> (fst v)
         v_0
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (fst v)
         (dynamic τ_0 (fst v_m))
         E-fst-1
         (where (mon (× τ_0 τ_1) v_m) v))
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (snd v)
         (dynamic τ_1 (snd v_m))
         E-snd-1
         (where (mon (× τ_0 τ_1) v_m) v))))

(module+ test
  (test-case "dyn-step"
    (check-true (stuck? dyn-step (term (dynamic Int 3))))
    (check-true (stuck? dyn-step (term (static Int 3))))
    (check-true (stuck? dyn-step (term ((λ (x : Int) x) 42))))

    (check-equal? (apply-reduction-relation dyn-step (term ((λ (x) x) 42))) '(42))
    (check-equal? (apply-reduction-relation dyn-step (term (+ 2 3))) '(5))
    (check-equal? (apply-reduction-relation dyn-step (term ((mon (→ Int Int) (λ (x : Int) x)) 5)))
                  (list (term (static Int ((λ (x : Int) x) (dynamic Int 5))))))
    (check-equal? (apply-reduction-relation dyn-step (term (fst (mon (× Nat Int) (× 1 -1)))))
                  (list (term (static Nat (fst (× 1 -1))))))
    (check-equal? (apply-reduction-relation dyn-step (term (snd (mon (× Nat Int) (× 1 -1)))))
                  (list (term (static Int (snd (× 1 -1))))))
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
    (check-equal? (apply-reduction-relation sta-step (term (fst (mon (× Nat Int) (× 1 -1)))))
                  (list (term (dynamic Nat (fst (× 1 -1))))))
    (check-equal? (apply-reduction-relation sta-step (term (snd (mon (× Nat Int) (× 1 -1)))))
                  (list (term (dynamic Int (snd (× 1 -1))))))
  )
)

;; Same as for `little-natural`
(define dyn-boundary-step
  (reduction-relation LM-lazy
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
         BE
         E-Advance-1
         (where (BE) ,(apply-reduction-relation sta-boundary-step (term e))))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Dyn
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation dyn-step (term e))))))

(define sta-boundary-step
  (reduction-relation LM-lazy
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
         BE
         E-Advance-1
         (where (BE) ,(apply-reduction-relation dyn-boundary-step (term e))))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Sta
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation sta-step (term e))))))

(define-metafunction LM-lazy
  static->dynamic : τ v -> A
  [(static->dynamic (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)]
  [(static->dynamic (× τ_0 τ_1) v)
   (mon (× τ_0 τ_1) v)]
  [(static->dynamic τ v)
   v])

(define-metafunction LM-lazy
  dynamic->static : τ v -> A
  [(dynamic->static Nat natural)
   natural]
  [(dynamic->static Nat v)
   (Boundary-Error v "Nat")]
  [(dynamic->static Int integer)
   integer]
  [(dynamic->static Int v)
   (Boundary-Error v "Int")]
  [(dynamic->static (× τ_0 τ_1) v)
   (mon (× τ_0 τ_1) v)
   (where #true (pair? v))]
  [(dynamic->static (× τ_0 τ_1) v)
   (Boundary-Error v ,(format "~a" (term (× τ_0 τ_1))))]
  [(dynamic->static (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)
   (where #true (procedure? v))]
  [(dynamic->static (→ τ_dom τ_cod) v)
   (Boundary-Error v ,(format "~a" (term (→ τ_dom τ_cod))))])

(module+ test

  (test-case "dyn-boundary-step"
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (+ 2 2)))
                  '(4))
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (static Int 3)))
                  '(3))
    (check-true (redex-match? LM-lazy A
      (term (in-hole hole (static Int (+ 1 2))))))
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (static Int (+ 1 2))))
                  (list (term (static Int 3))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation dyn-boundary-step (term (/ 1 0))))))
    (check-true (redex-match? LM-lazy BE
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
    (check-equal? (apply-reduction-relation dyn-boundary-step
                    (term (static (× Nat Int) (× 1 -1))))
                  (list (term (mon (× Nat Int) (× 1 -1)))))
  )

  (test-case "sta-boundary-step"
    (check-equal? (apply-reduction-relation sta-boundary-step (term (+ 2 2)))
                  '(4))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat 3)))
                  '(3))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat (+ 1 2))))
                  (list (term (dynamic Nat 3))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation sta-boundary-step (term (/ 1 0))))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (/ 1 0)))))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (λ (x) x)))))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (× 0 0)))))))
    (check-true (redex-match? LM-lazy BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Nat -1))))))

    (check-true (stuck? sta-boundary-step (term (static Int 3))))
    (check-equal? (apply-reduction-relation sta-boundary-step
                    (term (dynamic (× Nat Int) (× 1 -1))))
                  (list (term (mon (× Nat Int) (× 1 -1)))))
  )
)

(define dyn-step*
  (make--->* dyn-boundary-step))

(define sta-step*
  (make--->* sta-boundary-step))

(module+ test
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
    (check-true (redex-match? LM-lazy BE
      (sta-step* (term ((λ (f : (→ Nat Nat)) (f 0)) (dynamic (→ Nat Nat) (λ (z) -2)))))))
  )
)

(define (assert-well-dyn t dont-care)
  (unless (judgment-holds (well-dyn/lazy () ,t))
    (raise-arguments-error 'current-runtime-invariant "expected well-dyn" "term" t)))

(define (assert-well-typed t ty)
  (unless (judgment-holds (well-typed/lazy () ,t ,ty))
    (raise-arguments-error 'current-runtime-invariant "expected well-typed"
      "term" t
      "type" ty)))

(define (is-error? t)
  (or (redex-match? LM-lazy TE t)
      (redex-match? LM-lazy BE t)))

(define-metafunction LM-lazy
  theorem:lazy-safety : e MAYBE-τ -> any
  [(theorem:lazy-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term e) #f is-error? assert-well-dyn dyn-boundary-step))]
  [(theorem:lazy-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-step* (term e) (term τ) is-error? assert-well-typed sta-boundary-step))])

;; -----------------------------------------------------------------------------
;; --- NOTE: these judgments are very similar to the ones in `little-mixed.rkt`,
;;      just add new rules for monitors.
;;     It would be nice to be able to use `define-extended-judgment-form`,
;;      but that doesn't work for recursive calls.
;; ... okay, that, and it's important to distinguish environments!

(define-judgment-form LM-lazy
  #:mode (well-dyn/lazy I I)
  #:contract (well-dyn/lazy Γ e)
  [
   --- D-Int
   (well-dyn/lazy Γ integer)]
  [
   (well-dyn/lazy Γ e_0)
   (well-dyn/lazy Γ e_1)
   --- D-Pair
   (well-dyn/lazy Γ (× e_0 e_1))]
  [
   (where Γ_x (x Γ))
   (well-dyn/lazy Γ_x e)
   --- D-Fun
   (well-dyn/lazy Γ (λ (x) e))]
  [
   (where #true (type-env-contains Γ x))
   --- D-Var
   (well-dyn/lazy Γ x)]
  [
   (well-dyn/lazy Γ e_0)
   (well-dyn/lazy Γ e_1)
   --- D-App
   (well-dyn/lazy Γ (e_0 e_1))]
  [
   (well-dyn/lazy Γ e_0)
   (well-dyn/lazy Γ e_1)
   --- D-Binop
   (well-dyn/lazy Γ (BINOP e_0 e_1))]
  [
   (well-dyn/lazy Γ e)
   --- D-Unop
   (well-dyn/lazy Γ (UNOP e))]
  [
   (well-typed/lazy Γ e τ)
   --- D-Static
   (well-dyn/lazy Γ (static τ e))]
  [
   (well-typed/lazy Γ v (→ τ_dom τ_cod))
   --- D-Mon-Fun
   (well-dyn/lazy Γ (mon (→ τ_dom τ_cod) v))]
  [
   (well-typed/lazy Γ v (× τ_0 τ_1))
   --- D-Mon-Pair ;; same as D-Mon-Fun
   (well-dyn/lazy Γ (mon (× τ_0 τ_1) v))])

(define-judgment-form LM-lazy
  #:mode (well-typed/lazy I I I)
  #:contract (well-typed/lazy Γ e τ)
  [
   (infer-type Γ e τ_infer)
   (subtype τ_infer τ)
   ---
   (well-typed/lazy Γ e τ)])

(define-judgment-form LM-lazy
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
   (well-dyn/lazy Γ e)
   --- I-Dynamic
   (infer-type Γ (dynamic τ e) τ)]
  [
   (well-dyn/lazy Γ v)
   --- I-Mon-Fun
   (infer-type Γ (mon (→ τ_dom τ_cod) v) (→ τ_dom τ_cod))]
  [
   (well-dyn/lazy Γ v)
   --- I-Mon-Pair
   (infer-type Γ (mon (× τ_0 τ_1) v) (× τ_0 τ_1))])

(module+ test
  (test-case "well-dyn"
    (check-true (judgment-holds
      (well-dyn/lazy ()
        (static (→ (→ Nat (→ Int Nat)) Int)
          ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
           (λ (C : Int) C))))))
    (check-false (judgment-holds
      (well-dyn/lazy ()
        (mon (→ (× Int Int) (→ Nat Int))
             (λ (p) (λ (Okp) 2))))))
  )

  (test-case "well-typed"
    (check-true (judgment-holds (subtype (→ Int Nat) (→ Nat Int))))
    (check-true (judgment-holds
      (subtype (→ Nat Nat) (→ Nat Int))))
    (check-true (judgment-holds
      (subtype (→ (→ Nat (→ Nat Int)) Nat)
               (→ (→ Nat (→ Int Nat)) Int))))
    (check-true (judgment-holds
      (subtype
        (→ (→ Nat Int) Nat)
        (→ (→ Nat Nat) Nat))))
    (check-true (judgment-holds
      (subtype
        (× (→ (→ Nat Int) Nat) (→ Int Nat))
        (× (→ (→ Nat Nat) Nat) (→ Nat Int)))))
    (check-true (judgment-holds
      (well-typed/lazy ()
        ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
         (λ (C : Int) C))
        (→ (→ Nat (→ Int Nat)) Int))))
    ;; TODO
    #;(check-true (judgment-holds
      (well-typed/lazy ()
        (λ (C : Int) C)
        (→ Nat Nat))))
    (check-false (judgment-holds
      (well-typed/lazy ()
        (mon (→ Nat Int) (λ (C : Int) C))
        (→ (→ Nat (→ Nat Int)) Int))))
    (check-true (judgment-holds
      (well-typed/lazy ()
        (dynamic (× (→ (→ Nat Int) Nat) (→ Int Nat))
          3
          #;((λ (Qgk)
             (λ (IQ) 1))
           (mon (→ (× Int Int) (→ Nat Int))
                (λ (p) (λ (Okp) 2)))))
        (× (→ (→ Nat Nat) Nat)
           (→ Nat Int)))))
  )
)

;; -----------------------------------------------------------------------------

(module+ test

  (define (safe? t ty)
    (and (term #{theorem:lazy-safety ,t ,ty}) #true))

  (test-case "lazy-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
    (check-true (safe? (term (λ (n : Nat) (× 0 0))) (term (→ Nat (× Nat Nat)))))
    (check-true (safe? (term (+ (fst (fst (fst (dynamic (× (× (× Int Nat) (→ Nat (× Int Int))) Int) 0)))) (fst (dynamic (× Int (× (× Int Int) Nat)) 0)))) (term Int)))
    (check-true (safe? (term (dynamic (→ Int Int) (λ (x) x))) (term (→ Int Int))))
    (check-true (safe? (term (static (× (→ (× (→ Int Int) Int) Nat) (→ Int Nat)) (× (λ (R : (× (→ Int Int) Int)) 2) (λ (r : Int) 2)))) #f))
    (check-true (safe? (term (static (→ (→ Nat (→ Int Nat)) Int) ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs)) (λ (C : Int) C)))) #f))
  )

  (test-case "lazy-safety:auto"
    (check-true
      (redex-check LM-lazy #:satisfying (well-dyn () e)
        (term (theorem:lazy-safety e #f))
        #:attempts 1000
        #:print? #f))
    (check-true
      (redex-check LM-lazy #:satisfying (well-typed () e τ)
        (term (theorem:lazy-safety e τ))
        #:attempts 1000
        #:print? #f)))
)

