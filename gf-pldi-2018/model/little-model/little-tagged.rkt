#lang mf-apply racket/base

;; Tagged embedding,
;;  combine the lessons of lazy and forgetful

;; Needs:
;; - good old well-typed and well-dyn
;; - new semantics
;;   ... tag checks, never type checks never wraps
;;   ... probably very easy
;; - new run-time typing (well-tagged)
;;   ... (fst x) : TST, never has type τ
;;   ...
;; - check insertion
;;   ... only in typed code
;;   ... semantics preserving
;; - BEWARE 71498 of variables, typed referencing untyped

(require
  "little-lazy.rkt"
  "little-mixed.rkt"
  (only-in redex-abbrevs
    make--->*)
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

;; HMPH
;; really not happy about these "static" and "dynamic" fences
;; but the trouble is...
;; - all checks are necessary
;; - not all checks are boundaries
;; - need to distinguish boundaries (no type errors in typed code)

(define-extended-language LK
  LM
  (e ::= .... (check K e) (static e) (dynamic e))
  (K ::= Int Nat Pair Fun)
  (E ::= .... (check K E)))

(define-metafunction LK
  static->dynamic : τ v -> A
  [(static->dynamic τ v)
   #{do-check K v}
   (where K #{type->tag τ})])

(define-metafunction LK
  dynamic->static : τ v -> A
  [(dynamic->static τ v)
   #{static->dynamic τ v}])

(define-metafunction LK
  do-check : K v -> A
  [(do-check Int integer)
   integer]
  [(do-check Nat natural)
   natural]
  [(do-check Pair (× v_0 v_1))
   (× v_0 v_1)]
  [(do-check Fun Λ)
   Λ]
  [(do-check K v)
   (Boundary-Error v ,(format "~a" (term K)))])

(define-metafunction LK
  type->tag : τ -> K
  [(type->tag Nat)
   Nat]
  [(type->tag Int)
   Int]
  [(type->tag (× _ _))
   Pair]
  [(type->tag (→ _ _))
   Fun])

(define-metafunction LK
  error? : A -> boolean
  [(error? BE)
   #true]
  [(error? TE)
   #true]
  [(error? _)
   #false])

;; -----------------------------------------------------------------------------

(define dyn-step
  (reduction-relation LK
    #:domain A
    (--> (v_0 v_1)
         e_subst
         E-App-0
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (v_0 v_1)
         BE
         E-App-1.0
         (where (λ (x : τ) e) v_0)
         (where K #{type->tag τ})
         (where BE #{do-check K v_1}))
    (--> (v_0 v_1)
         (static e_subst)
         ;; TODO can remove this boundary??? probably not!
         E-App-1.1
         (where (λ (x : τ) e) v_0)
         (where K #{type->tag τ})
         (where v_+ #{do-check K v_1})
         (where e_subst (substitute e x v_+)))
    (--> (v_0 v_1)
         (Type-Error v_0 "procedure?")
         E-App-2
         (where #false #{procedure? v_0}))
    (--> (+ v_0 v_1)
         integer_2
         E-+-0
         (where integer_0 v_0)
         (where integer_1 v_1)
         (where integer_2 ,(+ (term integer_0) (term integer_1))))
    (--> (+ v_0 v_1)
         (Type-Error ,(if (redex-match? LK integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-+-1
         (side-condition (not (and (redex-match? LK integer (term v_0))
                                   (redex-match? LK integer (term v_1))))))
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
         (Type-Error ,(if (redex-match? LK integer (term v_0)) (term v_1) (term v_0)) "integer")
         E-/-2
         (side-condition (not (and (redex-match? LK integer (term v_0))
                                   (redex-match? LK integer (term v_1))))))
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
         E-snd-1
         (where (× v_0 v_1) v))
    (--> (snd v)
         (Type-Error v "pair?")
         E-snd-2
         (where #false #{pair? v}))))

(define sta-step
  (reduction-relation LK
    #:domain A
    (--> (v_0 v_1)
         e_subst
         E-App-0
         (where (λ (x : τ) e) v_0)
         (where e_subst (substitute e x v_1)))
    (--> (v_0 v_1)
         (dynamic e_subst)
         ;; TODO
         E-App-1
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
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
         E-fst
         (where (× v_0 v_1) v))
    (--> (snd v)
         v_1
         E-snd
         (where (× v_0 v_1) v))))

;; static,dynamic are boundaries; check is not
(define dyn-boundary-step
  (reduction-relation LK
    #:domain A
    (--> (in-hole E (static τ v))
         (maybe-in-hole E A)
         E-Cross-Boundary-0.0
         (where A #{static->dynamic τ v}))
    (--> (in-hole E (static v))
         (maybe-in-hole E v)
         E-Cross-Boundary-0.1)
    (--> (in-hole E (static τ e))
         (in-hole E (static τ e_+))
         E-Advance-0.0
         (where (e_+) ,(apply-reduction-relation sta-boundary-step (term e))))
    (--> (in-hole E (static e))
         (in-hole E (static e_+))
         E-Advance-0.1
         (where (e_+) ,(apply-reduction-relation sta-boundary-step (term e))))
    (--> (in-hole E (static τ e))
         A
         E-Advance-1.0
         (where (A) ,(apply-reduction-relation sta-boundary-step (term e)))
         (where #true #{error? A}))
    (--> (in-hole E (static e))
         A
         E-Advance-1.1
         (where (A) ,(apply-reduction-relation sta-boundary-step (term e)))
         (where #true #{error? A}))
    (--> (in-hole E e)
         (maybe-in-hole E A)
         E-Dyn
         (where #false (boundary? e))
         (where (A) ,(apply-reduction-relation dyn-step (term e))))))

(define sta-boundary-step
  (reduction-relation LK
    #:domain A
    (--> (in-hole E (dynamic τ v))
         (maybe-in-hole E A)
         E-Cross-Boundary-0.0
         (where A #{dynamic->static τ v}))
    (--> (in-hole E (dynamic v))
         (in-hole E v)
         E-Cross-Boundary-0.1)
    (--> (in-hole E (dynamic τ e))
         (in-hole E (dynamic τ e_+))
         E-Advance-0.0
         (where (e_+) ,(apply-reduction-relation dyn-boundary-step (term e))))
    (--> (in-hole E (dynamic e))
         (in-hole E (dynamic e_+))
         E-Advance-0.1
         (where (e_+) ,(apply-reduction-relation dyn-boundary-step (term e))))
    (--> (in-hole E (dynamic τ e))
         A
         E-Advance-1.0
         (where (A) ,(apply-reduction-relation dyn-boundary-step (term e)))
         (where #true #{error? A}))
    (--> (in-hole E (dynamic e))
         A
         E-Advance-1.1
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
    (check-true (redex-match? LK A
      (term (in-hole hole (static Int (+ 1 2))))))
    (check-equal? (apply-reduction-relation dyn-boundary-step (term (static Int (+ 1 2))))
                  (list (term (static Int 3))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation dyn-boundary-step (term (/ 1 0))))))

    (check-true (redex-match? LK BE
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
                  (list (term (× 1 -1))))
    (check-true (redex-match? LK TE
      (car (apply-reduction-relation sta-boundary-step
             (term (dynamic Int (fst 0)))))))
  )

  (test-case "sta-boundary-step"
    (check-equal? (apply-reduction-relation sta-boundary-step (term (+ 2 2)))
                  '(4))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat 3)))
                  '(3))
    (check-equal? (apply-reduction-relation sta-boundary-step (term (dynamic Nat (+ 1 2))))
                  (list (term (dynamic Nat 3))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation sta-boundary-step (term (/ 1 0))))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (/ 1 0)))))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (λ (x) x)))))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Int (× 0 0)))))))
    (check-true (redex-match? LK BE
      (car (apply-reduction-relation sta-boundary-step (term (dynamic Nat -1))))))

    (check-true (stuck? sta-boundary-step (term (static Int 3))))
    (check-equal? (apply-reduction-relation sta-boundary-step
                    (term (dynamic (× Nat Int) (× 1 -1))))
                  (list (term (× 1 -1))))

    (check-true (redex-match? LK TE
      (car (apply-reduction-relation dyn-boundary-step
             (term (static Int (dynamic Int (fst 0))))))))
  )
)
