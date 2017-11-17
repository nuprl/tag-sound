#lang mf-apply racket/base

;; Tagged embedding
;;
;; Similar to forgetful, but removes the monitors altogether.
;;
;; In forgetful, the monitors just make sure that every term has
;;  a well-defined semantics.
;; Monitors do that by putting the right checks in the right places.
;;
;; Don't need a monitor (dynamic analysis) to say where the right places
;;  are. Obviously!
;; Dynamic typing doesn't use monitors and it has just enough checks to
;;  make things well-defined.
;;
;; Idea:
;; - if tag-checks are always enough to make sure a valid is within the
;;   domain of a primop
;; - then tag-check every value that enters typed code
;; - and tag-check every value extracted from such values
;;
;; so if `e` has the static type `τ` then the checks make sure `e` evaluates
;;  to a value with the same type-tag as `τ`

(require
  "mixed.rkt"
  "redex-helpers.rkt"
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================

(define-extended-language LK
  LM
  (e ::= .... (check K e) (static e) (dynamic e))
  ;; A `check` is a plain old assert statement, insert these where
  ;;  you're "not sure" whether a value has the right type tag.
  ;; (This "not sure" is made precise with a type system, later.)

  (K ::= Int Nat Pair Fun Any)
  ;; One type tag for each non-terminal + terminal in the grammar of types

  (MAYBE-K ::= #f K)

  (E ::= .... (check K E)))

(define (LK=? t0 t1)
  (alpha-equivalent? LK t0 t1))

;; Boundary crossing = check the tag

(define-metafunction LK
  dynamic->static : τ v -> A
  [(dynamic->static τ v)
   #{static->dynamic τ v}])

(define-metafunction LK
  static->dynamic : τ v -> A
  [(static->dynamic τ v)
   #{do-check K v}
   (where K #{type->tag τ})])

;; Tag checks are the simple thing
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
  [(do-check Any v)
   v]
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
  maybe-in-hole : E A -> A
  [(maybe-in-hole E BE)
   BE]
  [(maybe-in-hole E TE)
   TE]
  [(maybe-in-hole E e)
   (in-hole E e)])

(define-metafunction LK
  boundary? : e -> boolean
  [(boundary? (static τ _))
   #true]
  [(boundary? (static _))
   #true]
  [(boundary? (dynamic τ _))
   #true]
  [(boundary? (dynamic _))
   #true]
  [(boundary? _)
   #false])

(define-metafunction LK
  error? : A -> boolean
  [(error? TE)
   #true]
  [(error? BE)
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
         E-App-1.1
         (where (λ (x : τ) e) v_0)
         (where K #{type->tag τ})
         (where v_+ #{do-check K v_1})
         (where e_subst (substitute e x v_+)))
    (--> (v_0 v_1)
         (Type-Error v_0 "procedure?")
         E-App-2
         (where #false #{procedure? v_0}))
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
         E-App-0.0
         (where (λ (x : τ) e) v_0)
         (where v_+ v_1)
         (where e_subst (substitute e x v_+)))
    (--> (v_0 v_1)
         (dynamic e_subst)
         E-App-1
         (where (λ (x) e) v_0)
         (where e_subst (substitute e x v_1)))
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
         E-fst
         (where (× v_0 v_1) v))
    (--> (snd v)
         v_1
         E-snd
         (where (× v_0 v_1) v))
    (--> (check K v)
         #{do-check K v}
         E-check)))

(module+ test
  (test-case "dyn-step"
    (check-true (stuck? dyn-step (term (check Int 5))))
  )

  (test-case "sta-step"
    (check-equal?
      (car (apply-reduction-relation sta-step (term (check Int 5))))
      5)
  )
)

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
         (where #false #{boundary? e})
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

;; -----------------------------------------------------------------------------

(define-metafunction LK
  theorem:tagged-safety : e MAYBE-τ -> any
  [(theorem:tagged-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term #{tagged-completion/dyn# e}) #f is-error? assert-well-dyn dyn-boundary-step))]
  [(theorem:tagged-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (let ([K (term #{type->tag τ})])
          (safe-step* (term #{tagged-completion/typed# e τ}) K is-error? assert-well-typed sta-boundary-step)))])

(define (assert-well-dyn t dont-care)
  (unless (judgment-holds (well-dyn/tagged () ,t))
    (raise-arguments-error 'current-runtime-invariant "expected well-dyn" "term" t)))

(define (assert-well-typed t ty)
  (unless (judgment-holds (well-typed/tagged () ,t ,ty))
    (raise-arguments-error 'current-runtime-invariant "expected well-typed"
      "term" t
      "type" ty)))

(define (is-error? t)
  (or (redex-match? LK TE t)
      (redex-match? LK BE t)))

;; -----------------------------------------------------------------------------

(define-metafunction LK
  tagged-completion/dyn# : e -> e
  [(tagged-completion/dyn# e)
   e_+
   (judgment-holds (tagged-completion/dyn () e e_+))])

(define-metafunction LK
  tagged-completion/typed# : e τ -> e
  [(tagged-completion/typed# e τ)
   e_+
   (judgment-holds (tagged-completion/typed () e τ e_+))])

(define-metafunction LK
  tagged-erasure# : any -> any
  [(tagged-erasure# (check K e))
   #{tagged-erasure# e}]
  [(tagged-erasure# (any ...))
   (#{tagged-erasure# any} ...)]
  [(tagged-erasure# any)
   any])

(module+ test
  (test-case "tagged-erasure"
    (check-equal?
      (term #{tagged-erasure# (+ 2 2)})
      (term (+ 2 2)))
    (check LK=?
      (term #{tagged-erasure# (check Int ((λ (x : Int) x) (× 0 0)))})
      (term ((λ (x : Int) x) (× 0 0))))
  )
)

;; NOTE:
;; - using type environment in completion
;; - because calling type checker in completion
;; - because need type annotations on certain parts
;; Alternative: add syntax for type-annotated terms, read type annotations
;;  instead of calling type checker
(define-judgment-form LK
  #:mode (tagged-completion/dyn I I O)
  #:contract (tagged-completion/dyn Γ e e)
  [
   --- C-Int
   (tagged-completion/dyn Γ integer integer)]
  [
   (tagged-completion/dyn Γ e_0 e_0c)
   (tagged-completion/dyn Γ e_1 e_1c)
   --- C-Pair
   (tagged-completion/dyn Γ (× e_0 e_1) (× e_0c e_1c))]
  [
   (where Γ_x (x Γ))
   (tagged-completion/dyn Γ_x e e_c)
   --- C-Fun-0
   (tagged-completion/dyn Γ (λ (x) e) (λ (x) e_c))]
  [
   ;; No need to check Γ, already know term is closed,
   ;;  and its safe for dyn contexts to reference typed variables
   --- C-Var
   (tagged-completion/dyn Γ x x)]
  [
   (tagged-completion/dyn Γ e_0 e_0c)
   (tagged-completion/dyn Γ e_1 e_1c)
   --- C-App
   (tagged-completion/dyn Γ (e_0 e_1) (e_0c e_1c))]
  [
   (tagged-completion/dyn Γ e_0 e_0c)
   (tagged-completion/dyn Γ e_1 e_1c)
   --- C-Binop
   (tagged-completion/dyn Γ (BINOP e_0 e_1) (BINOP e_0c e_1c))]
  [
   (tagged-completion/dyn Γ e e_c)
   --- C-Unop
   (tagged-completion/dyn Γ (UNOP e) (UNOP e_c))]
  [
   (tagged-completion/typed Γ e τ e_c)
   --- C-Static
   (tagged-completion/dyn Γ (static τ e) (static τ e_c))])

(define-judgment-form LK
  #:mode (tagged-completion/typed I I I O)
  #:contract (tagged-completion/typed Γ e τ e)
  [
   --- K-Int
   (tagged-completion/typed Γ integer _ integer)]
  [
   (infer-type Γ (× e_0 e_1) (× τ_0 τ_1))
   (tagged-completion/typed Γ e_0 τ_0 e_0c)
   (tagged-completion/typed Γ e_1 τ_1 e_1c)
   --- K-Pair
   (tagged-completion/typed Γ (× e_0 e_1) _ (× e_0c e_1c))]
  [
   (where Γ_x ((x : τ) Γ))
   (infer-type Γ_x e τ_cod)
   (tagged-completion/typed Γ_x e τ_cod e_c)
   --- K-Fun-1
   (tagged-completion/typed Γ (λ (x : τ) e) _ (λ (x : τ) e_c))]
  [
   ;; Doesn't matter if `x` or `x : τ` are in `Γ`
   --- K-Var
   (tagged-completion/typed Γ x _ x)]
  [
   (infer-type Γ e_0 (→ τ_dom τ_cod))
   (tagged-completion/typed Γ e_0 (→ τ_dom τ_cod) e_0c)
   (tagged-completion/typed Γ e_1 τ_dom e_1c)
   ;; assert that τ_cod <: τ ??? should always hold because well-typed
   (where K #{type->tag τ})
   --- K-App
   (tagged-completion/typed Γ (e_0 e_1) τ (check K (e_0c e_1c)))]
  [
   (tagged-completion/typed Γ e_0 Nat e_0c)
   (tagged-completion/typed Γ e_1 Nat e_1c)
   --- K-Binop-0
   (tagged-completion/typed Γ (BINOP e_0 e_1) Nat (BINOP e_0c e_1c))]
  [
   (where #false #{sub-tag# #{type->tag τ} Nat})
   (tagged-completion/typed Γ e_0 Int e_0c)
   (tagged-completion/typed Γ e_1 Int e_1c)
   --- K-Binop-1
   (tagged-completion/typed Γ (BINOP e_0 e_1) τ (BINOP e_0c e_1c))]
  [
   (infer-type Γ e (× τ_0 τ_1))
   (tagged-completion/typed Γ e (× τ_0 τ_1) e_c)
   (where K #{type->tag τ})
   --- K-fst
   (tagged-completion/typed Γ (fst e) τ (check K (fst e_c)))]
  [
   (infer-type Γ e (× τ_0 τ_1))
   (tagged-completion/typed Γ e (× τ_0 τ_1) e_c)
   (where K #{type->tag τ})
   --- K-snd
   (tagged-completion/typed Γ (snd e) τ (check K (snd e_c)))]
  [
   (tagged-completion/dyn Γ e e_c)
   ---
   (tagged-completion/typed Γ (dynamic τ e) _ (dynamic τ e_c))])

(module+ test
  (test-case "tagged-completion/typed"
    (check-true (redex-match? LK e
      (term (fst (dynamic (× (× Int Int) Int) (× 0 3))))))
    (check-equal?
      (term #{tagged-completion/typed# (fst (dynamic (× (× Int Int) Int) (× 0 3))) (× Int Int)})
      (term (check Pair (fst (dynamic (× (× Int Int) Int) (× 0 3))))))
    ;(check LK=?
    ;  (term #{tagged-completion/typed# ((λ (x : Int) (× x x)) (fst (dynamic (× (× Int Int) Int) (× 0 3)))) (× Int Int)})
    ;  (term (check Pair ((λ (x : Int) (× x x)) (check Int (fst (dynamic (× (× Int Int) Int) (× 0 3))))))))
  )
)

;; intentionally undefined for:
;; - (dynamic ....)
;; - (check ....)
(define-judgment-form LK
  #:mode (well-dyn/tagged I I)
  #:contract (well-dyn/tagged Γ e)
  [
   --- D-Int
   (well-dyn/tagged Γ integer)]
  [
   (well-dyn/tagged Γ e_0)
   (well-dyn/tagged Γ e_1)
   --- D-Pair
   (well-dyn/tagged Γ (× e_0 e_1))]
  [
   (where Γ_x (x Γ))
   (well-dyn/tagged Γ_x e)
   --- D-Fun-0
   (well-dyn/tagged Γ (λ (x) e))]
  [
   (where Γ_x ((x : τ) Γ))
   (well-typed/tagged Γ_x e Any)
   --- D-Fun-1
   (well-dyn/tagged Γ (λ (x : τ) e))]
  [
   (where #true #{type-env-contains Γ x})
   --- D-Var-0
   (well-dyn/tagged Γ x)]
  [
   (where _ #{type-env-ref Γ x})
   ;; fine because Dyn context cannot "mis-use" typed variable,
   ;;  worst case, `x` is a function and Dyn passes a bad value to a typed
   ;;  context. But tag checks mean that all typed functions are total.
   --- D-Var-1
   (well-dyn/tagged Γ x)]
  [
   (well-dyn/tagged Γ e_0)
   (well-dyn/tagged Γ e_1)
   --- D-App
   (well-dyn/tagged Γ (e_0 e_1))]
  [
   (well-dyn/tagged Γ e_0)
   (well-dyn/tagged Γ e_1)
   --- D-Binop
   (well-dyn/tagged Γ (BINOP e_0 e_1))]
  [
   (well-dyn/tagged Γ e)
   --- D-Unop
   (well-dyn/tagged Γ (UNOP e))]
  [
   (where K #{type->tag τ})
   (well-typed/tagged Γ e K)
   --- D-Static-0
   (well-dyn/tagged Γ (static τ e))]
  [
   (well-typed/tagged Γ e Any)
   ---
   (well-dyn/tagged Γ (static e))])

(define-judgment-form LK
  #:mode (sub-tag I I)
  #:contract (sub-tag K K)
  [
   --- S-Any
   (sub-tag K Any)]
  [
   --- S-Nat
   (sub-tag Nat Int)]
  [
   --- S-Refl
   (sub-tag K K)])

(define-metafunction LK
  sub-tag# : K K -> boolean
  [(sub-tag# K_0 K_1)
   #true
   (judgment-holds (sub-tag K_0 K_1))]
  [(sub-tag# _ _)
   #false])

(define-metafunction LK
  tag-join : K K -> MAYBE-K
  [(tag-join K_0 K_1)
   K_1
   (judgment-holds (sub-tag K_0 K_1))]
  [(tag-join K_0 K_1)
   K_0
   (judgment-holds (sub-tag K_1 K_0))]
  [(tag-join _ _)
   #false])

(module+ test
  (test-case "sub-tag"
    (check-true (judgment-holds (sub-tag Nat Int)))
    (check-true (judgment-holds (sub-tag Fun Fun)))
    (check-true (judgment-holds (sub-tag Fun Any)))

    (check-false (judgment-holds (sub-tag Int Nat)))
    (check-false (judgment-holds (sub-tag Any Pair)))))

(define-judgment-form LK
  #:mode (well-typed/tagged I I I)
  #:contract (well-typed/tagged Γ e K)
  [
   (infer-tag Γ e K_actual)
   (sub-tag K_actual K)
   ---
   (well-typed/tagged Γ e K)])

(define-judgment-form LK
  #:mode (infer-tag I I O)
  #:contract (infer-tag Γ e K)
  [
   --- I-Nat
   (infer-tag Γ natural Nat)]
  [
   (where #true #{negative? integer})
   --- I-Int
   (infer-tag Γ integer Int)]
  [
   (well-typed/tagged Γ e_0 Any)
   (well-typed/tagged Γ e_1 Any)
   --- I-Pair
   (infer-tag Γ (× e_0 e_1) Pair)]
  [
   (where Γ_x (x Γ))
   (well-dyn/tagged Γ_x e)
   --- I-Fun-0
   (infer-tag Γ (λ (x) e) Fun)]
  [
   (where Γ_x ((x : τ) Γ))
   (well-typed/tagged Γ_x e Any)
   --- I-Fun-1
   (infer-tag Γ (λ (x : τ) e) Fun)]
  [
   (where #true #{type-env-contains Γ x})
   --- I-Var-0
   (infer-tag Γ x Any)]
  [
   (where τ #{type-env-ref Γ x})
   (where K #{type->tag τ})
   --- I-Var-1
   (infer-tag Γ x K)]
  [
   (well-typed/tagged Γ e_0 Fun)
   (well-typed/tagged Γ e_1 Any)
   --- I-App
   (infer-tag Γ (e_0 e_1) Any)]
  [
   (infer-tag Γ e_0 K_0)
   (infer-tag Γ e_1 K_1)
   (sub-tag K_0 Int)
   (sub-tag K_1 Int)
   (where K #{tag-join K_0 K_1})
   --- I-+
   (infer-tag Γ (+ e_0 e_1) K)]
  [
   (infer-tag Γ e_0 K_0)
   (infer-tag Γ e_1 K_1)
   (sub-tag K_0 Int)
   (sub-tag K_1 Int)
   (where K #{tag-join K_0 K_1})
   --- I-/
   (infer-tag Γ (/ e_0 e_1) K)]
  [
   (well-typed/tagged Γ e Pair)
   --- I-fst
   (infer-tag Γ (fst e) Any)]
  [
   (well-typed/tagged Γ e Pair)
   --- I-snd
   (infer-tag Γ (snd e) Any)]
  [
   (well-dyn/tagged Γ e)
   (where K #{type->tag τ})
   --- I-Dyn-0
   (infer-tag Γ (dynamic τ e) K)]
  [
   (well-dyn/tagged Γ e)
   --- I-Dyn-1
   (infer-tag Γ (dynamic e) Any)]
  [
   (well-typed/tagged Γ e Any)
   --- I-Check
   (infer-tag Γ (check K e) K)])

(define-metafunction LK
  infer-tag# : Γ e -> K
  [(infer-tag# Γ e)
   K
   (judgment-holds (infer-tag Γ e K))])

(module+ test
  (test-case "well-dyn"
    (check-false (judgment-holds
      (well-dyn/tagged ()
        (static (→ (→ Nat (→ Int Nat)) Int)
          ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
           (λ (C : Int) C))))))
  )

  (test-case "well-typed"
    (check-true (judgment-holds
      (well-typed/tagged ()
        (dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
        Fun)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        (λ (C : Int) C)
        Fun)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
         (λ (C : Int) C))
        Any)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
         (λ (C : Int) C))
        Any)))
    (check-false (judgment-holds
      (well-typed/tagged ()
        ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
         (λ (C : Int) C))
        Fun)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        (check Fun
          ((dynamic (→ (→ Nat Int) (→ (→ Nat (→ Nat Int)) Nat)) (λ (bs) bs))
           (λ (C : Int) C)))
        Fun)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        (λ (C : Int) C)
        Fun)))
    (check-true (judgment-holds
      (well-typed/tagged ()
        (dynamic (× (→ (→ Nat Int) Nat) (→ Int Nat)) 3)
        Pair)))
  )
)
;; -----------------------------------------------------------------------------

(module+ test

  (define (safe? t ty)
    (parameterize ((error-print-width 9999))
      (with-handlers ([exn:fail:contract? (λ (e) (exn-message e))])
        (and (term #{theorem:tagged-safety ,t ,ty}) #true))))

  (test-case "tagged-safety"
    (check-true (safe? (term
      (+ (snd (fst (fst (dynamic (× (× (× Int Int) Int) (→ Int (× Int Nat))) 3))))
         (dynamic Int 0)))
      (term Int)))
    (check-true (safe? (term
      (static (→ (→ Int (→ Int Int)) (→ Nat (→ (→ Int Nat) Int)))
        ((fst (snd (snd (snd (snd (fst (snd (snd (fst (snd (fst (dynamic (× (× (→ Int Nat) (× (× Int (× (→ Nat (× Int Int)) (× (× Nat (× Nat (× Nat (× Nat (× (→ (× Int Nat) (→ (→ Nat (→ Nat Int)) (→ Int (→ (→ Nat Nat) Nat)))) (× Nat (→ Nat Nat))))))) Nat))) Int)) (× (× Int Nat) (× Nat Nat))) 1)))))))))))) (× (/ (snd (fst (fst (dynamic (× (× (× (× (→ Int Int) (→ Nat Nat)) Nat) Nat) (× (× Nat Nat) (× Nat Int))) 0)))) (snd (fst (snd (snd (snd (fst (dynamic (× (× Nat (× Int (× Nat (× (× (× (→ Int Nat) (→ Int Int)) Int) (× Nat (× Nat Nat)))))) Nat) 2)))))))) 0))))
      #f))
    (check-true (safe? (term
      (+ ((λ (aH : Int) (fst (dynamic (× Nat (× (→ Int Int) (× Int Nat))) 0)))
          (+ (snd (fst (fst (dynamic (× (× (× Int Int) Int) (→ Int (× Int Nat))) 3))))
             (dynamic Int 0)))
         ((fst (fst (dynamic (× (× (→ (× (× Nat (→ Nat Nat)) (× Int (× Nat Nat))) Int) (→ Nat (→ Int Int))) (× Nat (× Nat Int))) 1))) (dynamic (× (× Nat (→ Nat Nat)) (× Int (× Nat Nat))) (snd 1)))))
      (term Int)))
    (check-true (safe? (term
      ((λ (yp : (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat)) (fst (snd (fst yp))))
       (dynamic (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat) (× 0 3))))
      (term Int)))
    (check-true (safe? (term
      ((λ (yp : (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat)) (fst (snd (fst yp))))
       (dynamic (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat) 0)))
      (term Int)))
    (check-true (safe? (term
      (fst (dynamic (× (× Int Int) Int) (× 0 3))))
      (term (× Int Int))))
    (check-true (safe? (term
      ((λ (yp : (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat)) (fst (snd (fst yp))))
       (fst (dynamic (× (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat) Int) (× 0 3)))))
      (term Int)))
    (check-true (safe? (term
      (/ ((λ (MS : (× (× (× Int Nat) Nat) (→ Nat Int))) (fst (fst (fst MS)))) (snd (dynamic (× (→ (× Nat Nat) (× Int Nat)) (× (× (× Int Nat) Nat) (→ Int Nat))) (× 2 0)))) ((λ (v : (× Int Nat)) (snd (dynamic (× (× Nat (× Nat Nat)) Int) 1))) (fst (× (× 4 0) (snd (snd (fst (snd (snd (fst (dynamic (× (× (× (× Nat Int) Nat) (× (→ Int Int) (× (× (→ Int (× Int Int)) (× (→ (→ Int Nat) (→ Int Nat)) Int)) Nat))) Nat) 2))))))))))))
      (term Int)))
    (check-true (safe? (term
      (+ ((λ (yp : (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat)) (fst (snd (fst yp)))) (fst (dynamic (× (× (× (× (× Int Int) (× Nat Int)) (× Nat Int)) Nat) (→ (× Int Nat) Nat)) (× 0 3))))
         ((dynamic (→ (→ (× Nat Int) (× Nat Int)) Nat) (λ (z) z)) (λ (G : (× Nat Int)) G))))
      (term Int)))
    (check-true (safe? (term
      (static (× Int (→ (× (→ Nat Int) (× Nat Nat)) Nat)) (× ((λ (p : Int) 1) 1) ((snd (dynamic (× Nat (→ Int (→ (× (→ Nat Int) (× Nat Nat)) Nat))) 1)) 0))))
      #f))
  )

(parameterize ((error-print-width 99999))
  (test-case "tagged-safety:auto"
    (check-true
      (redex-check LK #:satisfying (well-dyn () e)
        (term (theorem:tagged-safety e #f))
        #:attempts 1000
        #:print? #f))
        )
  (test-case "tagged-ety:auto"
    (check-true
      (redex-check LK #:satisfying (well-typed () e τ)
        (term (theorem:tagged-safety e τ))
        #:attempts 1000
        #:print? #f)))
)
)

