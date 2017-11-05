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
;;   actually is not a problem
;; - completion correctness,
;;   * only adds checks
;;   * "similar" behavior ...

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
  (K ::= Int Nat Pair Fun Any)
  (MAYBE-K ::= #f K)
  (E ::= .... (check K E)))

(define (LK=? t0 t1)
  (alpha-equivalent? LK t0 t1))

;; TODO update semantics to use Any

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

;; -----------------------------------------------------------------------------

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

(define-metafunction LK
  theorem:tagged-safety : e MAYBE-τ -> any
  [(theorem:tagged-safety e #f)
   ,(or (not (judgment-holds (well-dyn () e)))
        (safe-step* (term #{tagged-completion/dyn# e}) #f is-error? assert-well-dyn dyn-boundary-step))]
  [(theorem:tagged-safety e τ)
   ,(or (not (judgment-holds (well-typed () e τ)))
        (let ([K (term #{type->tag τ})])
          (safe-step* (term #{tagged-completion/typed# e ,K}) K is-error? assert-well-typed sta-boundary-step)))])

;; -----------------------------------------------------------------------------

(define-metafunction LK
  tagged-completion/dyn# : e -> e
  [(tagged-completion/dyn# e)
   e_+
   (judgment-holds (tagged-completion/dyn e e_+))])

(define-metafunction LK
  tagged-completion/typed# : e τ -> e
  [(tagged-completion/typed# e τ)
   e_+
   (judgment-holds (tagged-completion/typed e τ e_+))])

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

(define-judgment-form LK
  #:mode (tagged-completion/dyn I O)
  #:contract (tagged-completion/dyn e e)
  [
   --- C-Int
   (tagged-completion/dyn integer integer)]
  [
   (tagged-completion/dyn e_0 e_0c)
   (tagged-completion/dyn e_1 e_1c)
   --- C-Pair
   (tagged-completion/dyn (× e_0 e_1) (× e_0c e_1c))]
  [
   (tagged-completion/dyn e e_c)
   --- C-Fun-0
   (tagged-completion/dyn (λ (x) e) (λ (x) e_c))]
  [
   (tagged-completion/typed e Any e_c)
   --- C-Fun-1
   (tagged-completion/dyn (λ (x : τ) e) (λ (x : τ) e_c))]
  [
   --- C-Var
   (tagged-completion/dyn x x)]
  [
   (tagged-completion/dyn e_0 e_0c)
   (tagged-completion/dyn e_1 e_1c)
   --- C-App
   (tagged-completion/dyn (e_0 e_1) (e_0c e_1c))]
  [
   (tagged-completion/dyn e_0 e_0c)
   (tagged-completion/dyn e_1 e_1c)
   --- C-Binop
   (tagged-completion/dyn (BINOP e_0 e_1) (BINOP e_0c e_1c))]
  [
   (tagged-completion/dyn e e_c)
   --- C-Unop
   (tagged-completion/dyn (UNOP e) (UNOP e_c))]
  [
   (where K #{type->tag τ})
   (tagged-completion/typed e K e_c)
   --- C-Static
   (tagged-completion/dyn (static τ e) (static τ e_c))])

(define-judgment-form LK
  #:mode (tagged-completion/typed I I O)
  #:contract (tagged-completion/typed e K e)
  [
   --- K-Int
   (tagged-completion/typed integer K integer)]
  [
   (tagged-completion/typed e_0 Any e_0c)
   (tagged-completion/typed e_1 Any e_1c)
   --- K-Pair
   (tagged-completion/typed (× e_0 e_1) K (× e_0c e_1c))]
  [
   (tagged-completion/dyn e e_c)
   --- K-Fun-0
   (tagged-completion/typed (λ (x) e) K (λ (x) e_c))]
  [
   (tagged-completion/typed e Any e_c)
   --- K-Fun-1
   (tagged-completion/typed (λ (x : τ) e) K (λ (x : τ) e_c))]
  [
   --- K-Var
   (tagged-completion/typed x K x)]
  [
   (tagged-completion/typed e_0 Fun e_0c)
   (tagged-completion/typed e_1 Any e_1c)
   --- K-App
   (tagged-completion/typed (e_0 e_1) K (check K (e_0c e_1c)))]
  [
   ;; If expecting a Nat, need to check arguments as Nats (or just check result)
   (where K_sub #{tag-join K Nat})
   (tagged-completion/typed e_0 K_sub e_0c)
   (tagged-completion/typed e_1 K_sub e_1c)
   --- K-Binop-0
   (tagged-completion/typed (BINOP e_0 e_1) K (BINOP e_0c e_1c))]
  [
   (tagged-completion/typed e Pair e_c)
   --- K-fst
   (tagged-completion/typed (fst e) K (check K (fst e_c)))]
  [
   (tagged-completion/typed e Pair e_c)
   --- K-snd
   (tagged-completion/typed (snd e) K (check K (snd e_c)))]
  [
   (tagged-completion/dyn e e_c)
   ---
   (tagged-completion/typed (dynamic τ e) K (dynamic τ e_c))]
  [
   (tagged-completion/typed e Any e_c)
   ---
   (tagged-completion/typed (check K e) _ (check K e_c))])

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
  (test-case "tagged-safety"
  )

  #;(test-case "tagged-safety:auto"
    (check-true
      (redex-check LK #:satisfying (well-dyn () e)
        (term (theorem:tagged-safety e #f))
        #:attempts 1000
        #:print? #f))
    (check-true
      (redex-check LK #:satisfying (well-typed () e τ)
        (term (theorem:tagged-safety e τ))
        #:attempts 1000
        #:print? #f)))
)
