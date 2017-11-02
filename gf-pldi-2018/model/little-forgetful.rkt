#lang mf-apply racket/base

;; Forgetful lazy natural embedding
;; ... same soundness
;;     fewer errors
;;     "contracts exist to make partial operations safe"

;; Only difference here is `static->dynamic` and `dynamic->static`

(require
  "little-lazy.rkt"
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

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
  [(static->dynamic (→ τ_dom-new τ_cod-new) v_m)
   (mon (→ τ_dom-old τ_cod-new) v)
   (where (mon (→ τ_dom-old τ_cod-old) v) v_m)]
  [(static->dynamic (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)]
  [(static->dynamic (× τ_0-new τ_1-new) v_m)
   (mon (× τ_0-new τ_1-new) v)
   (where (mon (× τ_0-old τ_1-old) v) v_m)]
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
  [(dynamic->static (× τ_0 τ_1) (mon (× _ _) v))
   (mon (× τ_0 τ_1) v)]
  [(dynamic->static (× τ_0 τ_1) (× v_0 v_1))
   (mon (× τ_0 τ_1) (× v_0 v_1))]
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

(define-metafunction LM-lazy
  theorem:forgetful-safety : e MAYBE-τ -> any
  [(theorem:forgetful-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-lazy-step* (term e) #f assert-well-dyn dyn-boundary-step))]
  [(theorem:forgetful-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-lazy-step* (term e) (term τ) assert-well-typed sta-boundary-step))])

;; -----------------------------------------------------------------------------

(module+ test

  (define (safe? t ty)
    (and (term #{theorem:forgetful-safety ,t ,ty}) #true))

  (test-case "forgetful-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
    (check-true (safe? (term (λ (n : Nat) (× 0 0))) (term (→ Nat (× Nat Nat)))))
    (check-true (safe? (term (+ (fst (fst (fst (dynamic (× (× (× Int Nat) (→ Nat (× Int Int))) Int) 0)))) (fst (dynamic (× Int (× (× Int Int) Nat)) 0)))) (term Int)))
    (check-true (safe? (term (dynamic (→ Int Int) (λ (x) x))) (term (→ Int Int))))
    (check-true (safe? (term (static (× (→ (× (→ Int Int) Int) Nat) (→ Int Nat)) (× (λ (R : (× (→ Int Int) Int)) 2) (λ (r : Int) 2)))) #f))
  )

  (test-case "forgetful-safety:auto"
    (check-true
      (redex-check LM-lazy #:satisfying (well-dyn () e)
        (term (theorem:forgetful-safety e #f))
        #:attempts 1000
        #:print? #f))
    (check-true
      (redex-check LM-lazy #:satisfying (well-typed () e τ)
        (term (theorem:forgetful-safety e τ))
        #:attempts 1000
        #:print? #f)))
)


