#lang mf-apply racket/base

(require
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LM-natural
  LM
  (v ::= .... (mon (→ τ τ) v)))

(define-metafunction LM-natural
  procedure? : v -> boolean
  [(procedure? Λ)
   #true]
  [(procedure? (mon (→ τ_dom τ_cod) v))
   #true] ;; could recur, but always true currently
  [(procedure? _)
   #false])

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

;; Have 3 reduction relations:
;; - dyn-step : reduces dynamically-typed leaf terms
;; - sta-step : reduces statically-typed leaf terms
;; - dyn-boundary-step : cross type boundaries, applied dyn-step or sta-step at leaf
;; - sta-boundary-step : ditto, but outermost context is statically typed
;; - dyn-step* : closure of dyn-boundary-step
;; - sta-step* : closure of sta-boundary-step

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
    (--> (+ v_0 v_1)
         integer_2
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (+ v_0 v_1)
         (Type-Error ,(if (redex-match? LM-natural integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LM-natural integer (term v_0))
                                   (redex-match? LM-natural integer (term v_1))))))
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
         (Type-Error ,(if (redex-match? LM-natural integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LM-natural integer (term v_0))
                                   (redex-match? LM-natural integer (term v_1))))))
    (--> (fst v)
         v_0
         E-fst-0
         (where (× v_0 v_1) v))
    (--> (fst v)
         (Type-Error v "pair?")
         E-fst-1
         (side-condition (not (redex-match? LM-natural (× v_0 v_1) (term v)))))
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))
    (--> (snd v)
         (Type-Error v "pair?")
         E-snd-1
         (side-condition (not (redex-match? LM-natural (× v_0 v_1) (term v)))))))

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
    (--> (snd v)
         v_1
         E-snd-0
         (where (× v_0 v_1) v))))

(module+ test
  (define (stuck? r t)
    (null? (apply-reduction-relation r t)))

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
         BE
         E-Advance-1
         (where (BE) ,(apply-reduction-relation sta-boundary-step (term e))))
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
         BE
         E-Advance-1
         (where (BE) ,(apply-reduction-relation dyn-boundary-step (term e))))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Sta
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation sta-step (term e))))))

(define-metafunction LM-natural
  static->dynamic : τ v -> A
  [(static->dynamic (→ τ_dom τ_cod) v)
   (mon (→ τ_dom τ_cod) v)]
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
   (× (dynamic->static τ_0 v_0) (dynamic->static τ_1 v_1))]
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
    ))

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
    (check-true (redex-match? LM-natural BE
      (sta-step* (term ((λ (f : (→ Nat Nat)) (f 0)) (dynamic (→ Nat Nat) (λ (z) -2)))))))
  )
)

(define (assert-well-dyn t dont-care)
  (unless (judgment-holds (well-dyn () ,t))
    (raise-arguments-error 'current-runtime-invariant "expected well-dyn" "term" t)))

(define (assert-well-typed t ty)
  (unless (judgment-holds (well-typed () ,t ,ty))
    (raise-arguments-error 'current-runtime-invariant "expected well-typed"
      "term" t
      "type" ty)))

(define-metafunction LM-natural
  theorem:natural-safety : e MAYBE-τ -> any
  [(theorem:natural-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-natural-step* (term e) #f assert-well-dyn dyn-boundary-step))]
  [(theorem:natural-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (safe-natural-step* (term e) (term τ) assert-well-typed sta-boundary-step))])

(define (safe-natural-step* A ty check-invariant step)
  (let loop ([A A])
    (cond
     [(or (redex-match? LM-natural TE A)
          (redex-match? LM-natural BE A))
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
        (raise-arguments-error 'safe-natural-step* "step is non-deterministic for expression"
          "e" A
          "answers" A*)])])))

(module+ test

  (define (safe? t ty)
    (and (term #{theorem:natural-safety ,t ,ty}) #true))

  (test-case "natural-safety"
    (check-true (safe? (term ((× 0 2) (× 2 1))) #f))
    (check-true (safe? (term (λ (n) (× 0 0))) #f))
    (check-true (safe? (term (λ (n : Nat) (× 0 0))) (term (→ Nat (× Nat Nat)))))
    (check-true (safe? (term (+ (fst (fst (fst (dynamic (× (× (× Int Nat) (→ Nat (× Int Int))) Int) 0)))) (fst (dynamic (× Int (× (× Int Int) Nat)) 0)))) (term Int)))
  )

  (test-case "identity-safety:auto"
    (check-true
      (redex-check LM-natural #:satisfying (well-dyn () e)
        (term (theorem:natural-safety e #f))
        #:attempts 10
        #:print? #f))
    (check-true
      (redex-check LM-natural #:satisfying (well-typed () e τ)
        (term (theorem:natural-safety e τ))
        #:attempts 10
        #:print? #f)))
)

