#lang mf-apply racket/base

;; Simple model of Typed Racket.

;; Soundness (from SNAPL 2017):
;;   If `⊢ e : τ` then either
;;   - `e` reduces to `v` and `⊢ v : τ`
;;   - `e` diverges
;;   - `e` raises a runtime error (bad value given to partial primitive)
;;   - `e` raises a boundary error `b` that points to a _specific location_
;;     where an untyped value entered typed code.

;; Lemmas
;;   - `∀ e . ⊢T e : τ => τ != TST`
;;   - `∀ (mon L_ctx τ_ctx (L_v v)) . ⊢L_v v : τ_ctx`
;;     - need stronger statement: `v` well-tagged according to `L_ctx`
;;   - completions
;;     - minimal-completion actually minimal (not easy)
;;     - any completion is well-typed (easy)

;; Awkwardnesses
;; - E is a "term context", also need a "program context",
;;   but don't have it so there's extra congruence rules e.g. PreMon-Error
;; - matthias wants set!
;;   tests first? I'm not exactly sure what this means. No strong updates right?

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs
  (only-in racket/string string-split))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; -----------------------------------------------------------------------------

(define-language++ μTR #:alpha-equivalent? α=?
  (e ::= v x (e e) (let (x τ P) e) (if e e e) (and e e)
         (cons e e) (car e) (cdr e)
         (+ e e) (= e e)
         (dyn-check tag e)
         (pre-mon L τ P srcloc))
  (v ::= integer boolean Λ (cons v v) (mon L τ (L v) srcloc))
  (Λ ::= (λ (x τ) e))
  (P ::= (L e))
  (τ ::= (U τk ...) τk TST)
  (τk ::= Int Bool (Pair τ τ) (→ τ τ))
  (L ::= R T)
  (Γ ::= ((x τ) ...))
  (primop ::= car cdr + =)
  (tag ::= Int Bool Pair →)
  (E ::= hole
         (E e) (v E)
         (cons E e) (cons v E)
         (car E) (cdr E)
         (+ E e) (+ v E)
         (= E e) (= v E)
         (if E e e)
         (and E e)
         (dyn-check tag E))
  (RuntimeError ::= (DynError tag v P) (BoundaryError L τ P srcloc))
  (srcloc ::= (dom srcloc) (cod srcloc) (car srcloc) (cdr srcloc) (π srcloc) (x τ))
  (A ::= P RuntimeError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (let (x τ P) e #:refers-to x)
  (λ (x τ) e #:refers-to x))

(module+ test
  (*term-equal?* α=?)

  (test-case "define-language"
    (check-pred e? (term 2))
    (check-pred e? (term (+ 1 1)))
    (check-pred e? (term (= x 1)))
    (check-pred e? (term (if (= x 1) 1 #false)))
    (check-pred e? (term (if #true 2 3)))
    (check-pred τ? (term (→ Int Int)))
    (check-pred τ? (term TST))
    (check-pred P? (term (R (if (= x 1) 1 #false))))
    (check-pred P? (term (R (λ (x TST) (if (= x 1) 1 #false)))))
    (check-pred P? (term (R (if 1 2 3))))
    (check-pred P? (term (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1)))))
    (check-pred e? (term (if 1 2 3)))
    (check-pred v? (term (mon T (→ Int Int) (R (λ (x TST) x)) (foo (→ Int Int)))))
    (check-pred P? (term (T (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #f))) ((car ff) 4)))))
  )
)

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-typed I)
  #:contract (well-typed P)
  [
   (infer-type () P τ)
   ---
   (well-typed P)])

(define-judgment-form μTR
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (T e) τ_actual)
   (subtype τ_actual τ)
   ---
   (check-type Γ (T e) τ)])

(define-judgment-form μTR
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P τ)
  [
   --- R-I-Int
   (infer-type Γ (R integer) TST)]
  [
   --- T-I-Int
   (infer-type Γ (T integer) Int)]
  [
   --- R-I-Bool
   (infer-type Γ (R boolean) TST)]
  [
   --- T-I-Bool
   (infer-type Γ (T boolean) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (cons e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   ---
   (infer-type Γ (T (cons e_0 e_1)) (Pair τ_0 τ_1))]
  [
   (infer-type Γ (R e) τ_e)
   ---
   (infer-type Γ (R (car e)) TST)]
  [
   (infer-type Γ (T e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (T (car e)) τ_0)]
  [
   (infer-type Γ (R e) τ)
   ---
   (infer-type Γ (R (cdr e)) TST)]
  [
   (infer-type Γ (T e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (T (cdr e)) τ_1)]
  [
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e) τ_cod)
   --- R-I-λ
   (infer-type Γ (R (λ (x TST) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (T e) τ_cod)
   --- T-I-λ
   (infer-type Γ (T (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
  (side-condition ,(debug "inferring ~a~n" (term (e_0 e_1))))
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
  (side-condition ,(debug "inferring ~a success~n" (term (e_0 e_1)) (term (τ_0 τ_1))))
   --- R-I-App
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   --- T-I-App
   (infer-type Γ (T (e_0 e_1)) τ_cod)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (R x) TST)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (T x) τ)]
  [
   ;; NOTE: the `let`-annotation is bad for R but good for T
   ;; - T components need to be protected from R contexts via their types
   ;; - it's easier to ask for annotation on let
   ;;   than to reconstruct the type from the T-component at runtime
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e_body) τ_body)
   --- R-I-Let
   (infer-type Γ (R (let (x τ P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (T e_body) τ_body)
   --- T-I-Let
   (infer-type Γ (T (let (x τ P) e_body)) τ_body)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (+ e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (+ e_0 e_1)) Int)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (= e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (= e_0 e_1)) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   (infer-type Γ (R e_2) τ_2)
   ---
   (infer-type Γ (R (if e_0 e_1 e_2)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (infer-type Γ (T e_2) τ_2)
   (where τ_3 #{make-union τ_1 τ_2})
   ---
   (infer-type Γ (T (if e_0 e_1 e_2)) τ_3)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (and e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where τ_2 #{make-union τ_0 τ_1})
   ---
   (infer-type Γ (T (and e_0 e_1)) τ_2)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (mon R τ P srcloc)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (mon T τ P srcloc)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (pre-mon R τ P srcloc)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (pre-mon T τ P srcloc)) τ)]
  [
   (side-condition ,(raise-user-error 'infer-type "dyn-check not allowed in source terms ~a" (term (L (dyn-check tag e)))))
   ---
   (infer-type Γ (L (dyn-check tag e)) TST)]
)

(define-metafunction μTR
  check-type# : P τ -> boolean
  [(check-type# P τ)
   #true
   (judgment-holds (check-type () P τ))]
  [(check-type# P τ)
   #false])

(define-metafunction μTR
  infer-type# : P -> τ
  [(infer-type# P)
   τ
   (judgment-holds (infer-type () P τ))]
  [(infer-type# P)
   ,(raise-user-error 'infer-type# "failed to infer type for term ~a" (term P))])

(module+ test

  (test-case "check-type#"
    (check-true (term #{check-type# (R (if 1 2 3)) TST})))

  (test-case "infer-type#"
    (check-mf-apply*
     ((infer-type# (T (if (and #true #true) (+ 1 1) (+ 2 2))))
      Int)
     ((infer-type# (R (let (f TST (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (T (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)))

  (test-case "well-typed"
    (check-judgment-holds*
     (well-typed (T (λ (x Int) 2)))
     (infer-type () (T (λ (x Int) 3)) (→ Int Int))
     (check-type () (T (λ (x Int) 3)) (→ Int Int))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (src (→ Int Int))) 7)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (check-type () (T 1) Int)
     (check-type () (T 1) (U Int (Pair Int Int)))
     (well-typed (T (if 1 2 (cons 2 3))))
     (check-type () (T (and 1 #true)) (U Bool Int))
     (well-typed (T (if (λ (x Int) x) 1 0)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (well-typed (T (let (h (→ Bool Bool)
                         (R (let (g (→ Int Int)
                                    (T (let (f (→ Int Int)
                                               (R (λ (x TST) x)))
                                         f)))
                              g)))
                   (h #true))))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (src (→ Int Int))) 7)))
     (well-typed (R (car (λ (x TST) x))))
     (well-typed (R (car 3)))
     (well-typed (R (car (cons 1 2))))
     (well-typed (T (car (cons 1 2))))
     (well-typed (T (λ (x Int) (+ x 1))))
     (well-typed (R (let (f (→ Int Int) (T (λ (x Int) (+ x 1)))) (f 3))))
    )

    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (R (dyn-check Int 3))))))
    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (T (dyn-check → (λ (x Int) 3)))))))

  )

  (test-case "not-well-typed"
    (check-not-judgment-holds*
      (well-typed (T (car 1)))
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- evalution

(define -->μTR
  (reduction-relation μTR
    #:domain A
;; -- MON
;; the "outermost" language for these doesn't really matter,
;; because `let-beta` will insert pre-mons from any language into the current E,
;; so just worry about the 2 languages inside the `mon` or `pre-mon` form
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx P srcloc)))
     (L (in-hole E (pre-mon L_ctx τ_ctx P_step srcloc)))
     PreMon-Step
     (where (P_step) ,(apply-reduction-relation -->μTR (term P)))]
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx P _)))
     RuntimeError
     PreMon-Error
     (where (RuntimeError) ,(apply-reduction-relation -->μTR (term P)))]
    [-->
     (L (in-hole E (pre-mon R τ_ctx (T v) srcloc)))
     (L (in-hole E v_+))
     PreMon-T->R
     (where v_+ ,(if (judgment-holds (flat T τ_ctx))
                   (term v)
                   (term (mon R τ_ctx (T v) srcloc))))]
    [-->
     (L (in-hole E (pre-mon L τ (L v) srcloc)))
     (L (in-hole E v))
     PreMon-NoBoundary]
    [-->
     (L (in-hole E (pre-mon T τ_ctx (R v) srcloc)))
     (L (in-hole E v_+))
     PreMon-R->T-MaybeOk
     (where v_+ #{dynamic-typecheck T τ_ctx (R v) srcloc})]
    [-->
     (L (in-hole E (pre-mon T τ_ctx (R v) srcloc)))
     RuntimeError
     PreMon-R->T-Error
     (where RuntimeError #{dynamic-typecheck T τ_ctx (R v) srcloc})]
;; -- APP
    [-->
     (L (in-hole E ((λ (x τ) e) v_1)))
     (L (in-hole E (substitute e x v_1)))
     App-Beta]
    [-->
     (L (in-hole E ((mon L_ctx τ_ctx (L_λ v) srcloc) v_1)))
     (L (in-hole E e_cod))
     App-Mon
     (where (→ τ_dom τ_cod) τ_ctx)
     (where P_subst (L_λ (v (pre-mon L_λ τ_dom (L_ctx v_1) (dom srcloc)))))
     (where e_cod (pre-mon L_ctx τ_cod P_subst (cod srcloc)))]
;; -- LET
    [-->
     (L (in-hole E (let (x τ P) e_body)))
     (L (in-hole E (let (x τ P_step) e_body)))
     Let-Step
     (where (P_step) ,(apply-reduction-relation -->μTR (term P)))]
    [-->
     (L (in-hole E (let (x τ (L_v v)) e_body)))
     ;; -- function annotation ignored at runtime
     (L (in-hole E ((λ (x TST) e_body) (pre-mon L τ (L_v v) (#{xerox x} τ)))))
     Let-Beta]
;; -- control flow
    [-->
     (L (in-hole E (and v_0 e_1)))
     (L (in-hole E e_2))
     And
     (where e_2 ,(if (eq? #false (term v_0)) (term #false) (term e_1)))]
    [-->
     (L (in-hole E (if v e_1 e_2)))
     (L (in-hole E e_1))
     If-True
     (side-condition (not (eq? #false (term v))))]
    [-->
     (L (in-hole E (if #false e_1 e_2)))
     (L (in-hole E e_2))
     If-False]
;; -- primop
    [-->
     (L (in-hole E (primop v ...)))
     (L (in-hole E #{apply-op primop v ...}))
     Primop]
;; -- dyn-check
    [-->
     (L (in-hole E (dyn-check tag v)))
     (L (in-hole E v))
     DynCheck-Ok
     (judgment-holds (well-tagged v tag))]
    [-->
     (L (in-hole E (dyn-check tag v)))
     (DynError tag v (L (in-hole E (dyn-check tag v))))
     DynCheck-Error
     (side-condition (not (judgment-holds (well-tagged v tag))))]))

(define -->μTR*
  (make--->* -->μTR))

(define-metafunction μTR
  eval : P  -> any
  [(eval P)
   #{eval* P #false}])

(define-metafunction μTR
  eval* : P boolean -> any
  [(eval* P boolean_keeptrace)
   any
   (judgment-holds (well-typed P))
   (where P_c #{minimal-completion# P})
   (where any ,(if (term boolean_keeptrace)
                 (apply-reduction-relation* -->μTR (term P_c) #:all? #t)
                 (-->μTR* (term P_c))))]
  [(eval* P _)
   ,(raise-user-error 'eval "trouble eval'ing ~a" (term P))
   (judgment-holds (well-typed P))]
  [(eval* P _)
   ,(raise-user-error 'eval "typechecking failed ~a" (term P))])

(module+ test
  (test-case "eval:R:I"
    ;; simplest terms, R language
    (check-mf-apply*
     ((eval (R (if 1 2 3)))
      (R 2))
     ((eval (R (if #false 2 3)))
      (R 3))
     ((eval (R (if #true 2 3)))
      (R 2))
     ((eval (R (and 1 2)))
      (R 2))
     ((eval (R (and #true 3)))
      (R 3))
     ((eval (R (and #true #false)))
      (R #false))
     ((eval (R (and #false #true)))
      (R #false))
     ((eval (R (and #true #true)))
      (R #true))
     ((eval (R (= 1 1)))
      (R #true))
     ((eval (R (= 1 2)))
      (R #false))
     ((eval (R (= #true 2)))
      (DynError Int #true (R (= (dyn-check Int #true) (dyn-check Int 2)))))
     ((eval (R (= 3 (= 1 1))))
      (DynError Int #true (R (= 3 (dyn-check Int #true)))))
     ((eval (R (+ 2 2)))
      (R 4))
     ((eval (R (+ #true 2)))
      (DynError Int #true (R (+ (dyn-check Int #true) (dyn-check Int 2)))))
     ((eval (R (+ 2 #true)))
      (DynError Int #true (R (+ 2 (dyn-check Int #true)))))
     ((eval (R (cons 1 2)))
      (R (cons 1 2)))
     ((eval (R (+ 1 (car (cons (+ 1 1) (+ 2 2))))))
      (R 3))
     ((eval (R (+ 1 (cdr (cons (+ 1 1) (+ 2 2))))))
      (R 5))
     ((eval (R ((car (cons (λ (x TST) (+ x 1)) 4)) 8)))
      (R 9))
    )
  )

  (test-case "eval:R:II"
    (check-mf-apply*
      ((eval (R (let (n1 TST (R #false)) n1)))
       (R #false))
      ((eval (R (let (n1 TST (R (+ 2 2))) (+ n1 n1))))
       (R 8))
      ((eval (R ((λ (x TST) (+ x 1)) 1)))
       (R 2))
      ((eval (R (1 1)))
       (DynError → 1 (R ((dyn-check → 1) 1))))
      ((eval (R (pre-mon R Int (T 6) (boundary Int))))
       (R 6))
      ((eval (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (boundary (→ Int Int))) 7)))
       (R 2))
    )
  )

  (test-case "eval:simple:T"
    (check-mf-apply*
     [(eval (T 4))
      (T 4)]
     ((eval (T (if (and #true (= 4 2)) (+ 1 1) (+ 2 2))))
      (T 4))
     [(eval (T #true))
      (T #true)]
     [(eval (T (+ 2 2)))
      (T 4)]
     [(eval (T ((λ (x Int) x) 1)))
      (T 1)]
     [(eval (T ((λ (x Int) (+ x 1)) 1)))
      (T 2)]
     [(eval (T (if ((λ (x Bool) x) #true) 1 0)))
      (T 1)]
     [(eval (T (if #false (+ 6 6) 0)))
      (T 0)]
     [(eval (T (let (x Int (T 1))
                 (let (y Int (T 2))
                   (+ x y)))))
      (T 3)]
     [(eval (T (let (negate (→ Bool Bool) (T (λ (x Bool) (if x #false #true))))
                 (let (b Bool (T #false))
                   (negate (negate b))))))
      (T #false)]
     [(eval (T (let (x Int (T 4))
                 (let (add-x (→ Int Int) (T (λ (y Int) (+ y x))))
                   (let (x Int (T 5))
                     (add-x x))))))
      (T 9)]
     [(eval (T (cons (+ 2 2) (+ 1 1))))
      (T (cons 4 2))]
     [(eval (T (+ 2 (cdr (cons #false 4)))))
      (T 6)]
    )
  )

  (test-case "eval:simple:T:fail"
    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (T ((λ (x Int) (+ x 1)) #false))})))

    (check-exn #rx"typechecking failed"
      (λ () (term (eval (T (let (x Bool (T (+ 2 5))) x)))))))

  (test-case "apply-R-in-T"
    (check-mf-apply*
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x 1))))
                 (f 3))))
      (T 4)]
     [(eval (T (let (f (→ Int Bool) (R (λ (x TST) (if (= 0 x) #false #true))))
                 (f 3))))
      (T #true)]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) #false))) (f 1))))
      (BoundaryError T Int (R #false) (cod (f (→ Int Int))))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError Int #false (R (+ 3 (dyn-check Int #false))))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError Int #true (R (+ (dyn-check Int #true) (dyn-check Int #false))))]
    )
  )

  (test-case "apply-T-in-R"
    (check-mf-apply*
     [(eval (R (let (f (→ Int Int) (T (λ (x Int) (+ x 1)))) (f 3))))
      (R 4)]
     [(eval (R (let (f (→ Int Bool) (T (λ (x Int) (if (= 0 x) #false #true)))) (f 3))))
      (R #true)]
     [(eval (R (let (f (→ Int Int) (T (λ (x Int) (+ x 4)))) (f #true))))
      (BoundaryError T Int (R #true) (dom (f (→ Int Int))))]
    )

    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (R (let (f (→ Int Int) (T (λ (x Int) #false))) (f 1)))})))
  )

  (test-case "eval:R:III"
    (check-mf-apply*
     ((eval (R (pre-mon R (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b2 (→ Int Int)))))
      (R (mon R (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b2 (→ Int Int)))))
    )
  )

  (test-case "double-wrap"
    (check-mf-apply*
     ((eval (T (let (h (→ Bool Bool)
                       (R (let (g (→ Int Int)
                                  (T (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h #true))))
      (BoundaryError T Int (R #true) (dom (g (→ Int Int)))))
     ((eval (T (let (h (→ Int Int)
                       (R (let (g (→ Int Int)
                                  (T (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h 5))))
      (T 5))))

  (test-case "more-R-in-T"
    (check-mf-apply*
     ((eval (T (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #false)))
                 ((car ff) 4))))
      (T 8))
     ((eval (T (let (ff (Pair (→ Bool Bool) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      (T #false))
     ((eval (T (let (ff (Pair (→ Bool Int) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      (BoundaryError T Int (R #false) (cod (car (ff (Pair (→ Bool Int) Bool))))))
     ((eval (T (let (ff (→ Int (U Bool Int)) (R (λ (x TST) (if (= x 0) #false x))))
                 (let (gg (→ (U Bool Int) Int) (R (λ (x TST) 900)))
                   (+ (gg (ff 0))
                      (gg (ff 1)))))))
      (T 1800))
    )
  )

  (test-case "well-typed-programs-run-faster"
    (define (check-shorter-trace t1 t2)
      (define-values [trace1 trace2]
          (values (term #{eval* ,t1 #true}) (term #{eval* ,t2 #true})))
      (check < (length trace1) (length trace2)))

    (check-shorter-trace (term (T (+ 2 2))) (term (R (+ 2 2))))
  )
)

;; =============================================================================
;; === less interesting from here on
;; =============================================================================

;; -----------------------------------------------------------------------------
;; --- type helpers

(define-judgment-form μTR
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   (side-condition ,(α=? (term #{type-normalize τ_0}) (term #{type-normalize τ_1})))
   --- Refl
   (type= τ_0 τ_1)])

(define-metafunction μTR
  type-normalize : τ -> τ
  [(type-normalize τk)
   τk]
  [(type-normalize TST)
   TST]
  [(type-normalize (U τk ...))
   ,(let ((kk (sort/deduplicate (term (τk ...)) symbol<? #:key simple-type->constructor)))
      (cond
       [(null? kk)
        (term (U))]
       [(null? (cdr kk))
        (car kk)]
       [else
        (cons (term U) kk)]))])

(define (simple-type->constructor t)
  (unless (τk? t)
    (raise-argument-error 'simple-type->constructor "simple type" t))
  (cond
   [(symbol? t)
    t]
   [(pair? t)
    (car t)]
   [else
    (raise-user-error 'simple-type->constructor "undefined for type ~a" t)]))

(define (sort/deduplicate t* <? #:key get-key)
  (let loop ([t* (sort t* <? #:key get-key)])
    (cond
     [(or (null? t*) (null? (cdr t*)))
      t*]
     [(equal? (car t*) (cadr t*)) ;; TODO not great (but also not horrible)
      (loop (cdr t*))]
     [else
      (cons (car t*) (loop (cdr t*)))])))

(define-judgment-form μTR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [
   --- Refl
   (subtype τ τ)]
  [
   (subtype τ_dom1 τ_dom0)
   (subtype τ_cod0 τ_cod1)
   --- Arrow
   (subtype (→ τ_dom0 τ_cod0) (→ τ_dom1 τ_cod1))]
  [
   (subtype τ_lhs τ_rhs)
   --- U-Member
   (subtype τ_lhs (U τ_0 ... τ_rhs τ_1 ...))]
  [
   --- U-Empty
   (subtype (U) (U τ ...))]
  [
   (subtype τ_lhs τ_rhs)
   (subtype (U τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))
   ---
   (subtype (U τ_lhs τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))])

(define-metafunction μTR
  make-union : τ τ -> τ
  [(make-union TST τ)
   ,(raise-argument-error 'make-union "cannot make union with TST" 0 (term TST) (term τ))]
  [(make-union τ TST)
   ,(raise-argument-error 'make-union "cannot make union with TST" 1 (term τ) (term TST))]
  [(make-union τk_0 τ)
   (make-union (U τk_0) τ)]
  [(make-union τ τk_1)
   (make-union τ (U τk_1))]
  [(make-union (U τ_0 ...) (U τ_1 ...))
   #{type-normalize (U τ_0 ... τ_1 ...)}])

(define-judgment-form μTR
  #:mode (well-tagged I I)
  #:contract (well-tagged v tag)
  [
   ---
   (well-tagged integer Int)]
  [
   ---
   (well-tagged boolean Bool)]
  [
   ---
   (well-tagged Λ →)]
  [
   ---
   (well-tagged (cons _ _) Pair)]
  [
   (tag= #{tag-only τ} tag)
   ---
   (well-tagged (mon _ τ _ _) tag)])

(define-judgment-form μTR
  #:mode (tag= I I)
  #:contract (tag= tag tag)
  [
   ---
   (tag= tag tag)])

(module+ test

  (test-case "simple-type->constructor"
    (check-apply* simple-type->constructor
     ((term Int)
      ==> 'Int)
     ((term Bool)
      ==> 'Bool)
     ((term (Pair Int Int))
      ==> 'Pair)
     ((term (→ Int Int))
      ==> '→)))

  (test-case "type-normalize"
    (check-mf-apply*
     ((type-normalize (U Int Int))
      Int)
     ((type-normalize (U Int Bool))
      (U Bool Int))
     ((type-normalize (U Int Int (Pair Int Int) (Pair Bool Int)))
      (U Int (Pair Int Int) (Pair Bool Int)))
     ((type-normalize (U (Pair Int Int) (Pair Int Int) Int))
      (U Int (Pair Int Int)))))

  (test-case "well-tagged"
    (check-judgment-holds*
     (well-tagged 4 Int)
     (well-tagged #true Bool)
     (well-tagged (λ (x TST) 4) →)
     (well-tagged (cons 1 1) Pair)
     (well-tagged (mon T (→ (Pair Int Int) Int) (R (λ (x TST) (+ 2 (car x)))) (x Int)) →)
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- environment helpers

(define-metafunction μTR
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction μTR
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

;; -----------------------------------------------------------------------------
;; --- flat types

;; `(flat L τ)` iff `τ` is strictly positive and `L` fully-checks values with type `τ`
(define-judgment-form μTR
  #:mode (flat I I)
  #:contract (flat L τ)
  [
   ---
   (flat L TST)]
  [
   ---
   (flat T Int)]
  [
   ---
   (flat T Bool)]
  [
   (flat T τ_0)
   (flat T τ_1)
   ---
   (flat T (Pair τ_0 τ_1))])

(module+ test
  (test-case "flat"
    (check-true (judgment-holds (flat T Int)))
    (check-false (judgment-holds (flat R Int)))
    (check-false (judgment-holds (flat T (→ Bool Bool))))

    (check-true (judgment-holds (flat T (Pair Int Int))))
    (check-false (judgment-holds (flat T (Pair Int (Pair (→ Int Int) Int)))))
  )
)

;; -----------------------------------------------------------------------------
;; --- dynamic-typecheck

(define-metafunction μTR
  dynamic-typecheck : L τ P srcloc -> any ;; value or BoundaryError
  [(dynamic-typecheck R τ P srcloc)
   ,(raise-user-error 'dynamic-typecheck "language R has no dynamic typechecker ~a ~a" (term e) (term τ))]
;; --- Int
  [(dynamic-typecheck T Int (L integer) srcloc)
   integer]
  [(dynamic-typecheck T Int (L v) srcloc)
   (BoundaryError T Int (L v) srcloc)]
;; --- Bool
  [(dynamic-typecheck T Bool (L boolean) srcloc)
   boolean]
  [(dynamic-typecheck T Bool (L v) srcloc)
   (BoundaryError T Bool (L v) srcloc)]
;; --- Pair
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc)
   RuntimeError
   (where RuntimeError #{dynamic-typecheck T τ_0 (L v_0) (car srcloc)})]
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc)
   RuntimeError
   (where RuntimeError #{dynamic-typecheck T τ_1 (L v_1) (cdr srcloc)})]
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc)
   (cons v_0+ v_1+)
   (where v_0+ #{dynamic-typecheck T τ_0 (L v_0) (car srcloc)})
   (where v_1+ #{dynamic-typecheck T τ_1 (L v_1) (cdr srcloc)})]
;; --- U
  [(dynamic-typecheck T (U τk ...) (L v) srcloc)
   ,(let loop ([tk* (term (τk ...))])
      (if (null? tk*)
        (term (BoundaryError T (U τk ...) (L v) srcloc))
        (let ([x (term #{dynamic-typecheck T ,(car tk*) (L v) (π srcloc)})])
          (if (RuntimeError? x)
            (loop (cdr tk*))
            x))))]
;; --- →
  [(dynamic-typecheck T (→ τ_dom τ_cod) (L Λ) srcloc)
   (mon T (→ τ_dom τ_cod) (L Λ) srcloc)]
  [(dynamic-typecheck T τ (L (mon L_mon τ_mon P_mon srcloc_mon)) srcloc)
   RuntimeError
   (where TST τ_mon)
   (where RuntimeError #{dynamic-typecheck T τ P_mon srcloc})]
  [(dynamic-typecheck T τ P srcloc)
   (mon T τ P srcloc)
   ;; τ must be non-flat, because that's the only type we keep mon's for
   (where (L (mon L_mon τ_mon P_mon srcloc_mon)) P)
   (judgment-holds (tag= #{tag-only τ_mon} #{tag-only τ}))]
  [(dynamic-typecheck T (→ τ_dom τ_cod) P srcloc)
   (BoundaryError T (→ τ_dom τ_cod) P srcloc)]
;; --- TST
  [(dynamic-typecheck T TST (L v) srcloc)
   v
   (side-condition (printf "WARNING: T expects value ~a to have TST~n" (term v)))])

(define-judgment-form μTR
  #:mode (proc? I)
  #:contract (proc? v)
  [
   ---
   (proc? (λ (x τ) e))]
  [
   (proc? v_1) ;; since mon always check constructor, could just check τ_0
   ---
   (proc? (mon L_0 τ_0 (L_1 v_1) srcloc))])

(define-judgment-form μTR
  #:mode (cons? I)
  #:contract (cons? v)
  [
   ---
   (cons? (cons e_0 e_1))]
  [
   (cons? v_1)
   ---
   (cons? (mon L_0 τ_0 (L_1 v_1) srcloc))])

(define-metafunction μTR
  tag-only : τ -> tag
  [(tag-only Int)
   Int]
  [(tag-only Bool)
   Bool]
  [(tag-only (Pair τ_0 τ_1))
   Pair]
  [(tag-only (→ τ_dom τ_cod))
   →]
  [(tag-only TST)
   TST])

;; Add runtime checks to ensure safety
(define-judgment-form μTR
  #:mode (minimal-completion I O)
  #:contract (minimal-completion P P)
  [
   ---
   (minimal-completion (L integer) (L integer))]
  [
   ---
   (minimal-completion (L boolean) (L boolean))]
  [
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (λ (x τ) e)) (L (λ (x τ) e_c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   ---
   (minimal-completion (L (cons e_0 e_1)) (L (cons e_0c e_1c)))]
  [
   ---
   (minimal-completion (L x) (L x))]
  [
   (minimal-completion P_m P_mc)
   ---
   (minimal-completion (L (mon L_m τ_m P_m srcloc)) (L (mon L_m τ_m P_mc srcloc)))]
  [
   (minimal-completion P P_c)
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (let (x τ P) e)) (L (let (x τ P_c) e_c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   (minimal-completion (L e_2) (L e_2c))
   ---
   (minimal-completion (L (if e_0 e_1 e_2)) (L (if e_0c e_1c e_2c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   ---
   (minimal-completion (L (and e_0 e_1)) (L (and e_0c e_1c)))]
  [
   (side-condition ,(raise-user-error 'minimal-completion "dyn-check not allowed in source programs ~a" (term (L (dyn-check tag e)))))
   ---
   (minimal-completion (L (dyn-check tag e)) (L (dyn-check tag e)))]
  [
   (minimal-completion P P_c)
   ---
   (minimal-completion (L (pre-mon L_m τ P srcloc)) (L (pre-mon L_m τ P_c srcloc)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-App
   (minimal-completion (R (e_0 e_1)) (R ((dyn-check → e_0c) e_1c)))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-App
   (minimal-completion (T (e_0 e_1)) (T (e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Car
   (minimal-completion (R (car e_0)) (R (car (dyn-check Pair e_0c))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   --- T-Car
   (minimal-completion (T (car e_0)) (T (car e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Cdr
   (minimal-completion (R (cdr e_0)) (R (cdr (dyn-check Pair e_0c))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   --- T-Cdr
   (minimal-completion (T (cdr e_0)) (T (cdr e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-+
   (minimal-completion (R (+ e_0 e_1)) (R (+ (dyn-check Int e_0c) (dyn-check Int e_1c))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-+
   (minimal-completion (T (+ e_0 e_1)) (T (+ e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-=
   (minimal-completion (R (= e_0 e_1)) (R (= (dyn-check Int e_0c) (dyn-check Int e_1c))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-=
   (minimal-completion (T (= e_0 e_1)) (T (= e_0c e_1c)))])

(define-metafunction μTR
  minimal-completion# : P -> P
  [(minimal-completion# P)
   P_+
   (judgment-holds (minimal-completion P P_+))])

(define-metafunction μTR
  xerox : x -> x
  [(xerox x)
   ,(string->symbol (car (string-split (symbol->string (term x)) "«")))])

(define-metafunction μTR
  apply-op : primop v ... -> v
  [(apply-op car (cons v_0 _))
   v_0]
  [(apply-op cdr (cons _ v_1))
   v_1]
  [(apply-op + v_0 v_1)
   ,(+ (term v_0) (term v_1))]
  [(apply-op = v_0 v_1)
   ,(= (term v_0) (term v_1))])

(module+ test
  (test-case "dynamic-typecheck"
    (check-mf-apply*
     ((dynamic-typecheck T Int (R 4) (x Int))
      4)
     ((dynamic-typecheck T (→ Int Int) (R (λ (x Int) 3)) (f (→ Int Int)))
      (mon T (→ Int Int) (R (λ (x Int) 3)) (f (→ Int Int))))
     ((dynamic-typecheck T (→ Bool Bool) (T (λ (x Bool) #false)) (f (→ Bool Bool)))
      (mon T (→ Bool Bool) (T (λ (x Bool) #false)) (f (→ Bool Bool))))
     ((dynamic-typecheck T (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b3 (→ Int Int)))
      (mon T (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b3 (→ Int Int))))
     ((dynamic-typecheck T (Pair Int Int) (R (cons 1 1)) (x (Pair Int Int)))
      (cons 1 1))
     ((dynamic-typecheck T (Pair Int Bool) (R (cons 2 #false)) (x (Pair Int Bool)))
      (cons 2 #false))
     ((dynamic-typecheck T (Pair (→ Bool Bool) Bool) (R (cons (λ (x TST) x) #true)) (x (Pair (→ Bool Bool) Bool)))
      (cons (mon T (→ Bool Bool) (R (λ (x TST) x)) (car (x (Pair (→ Bool Bool) Bool)))) #true))
     ((dynamic-typecheck T (Pair Int Int) (R (cons 1 #false)) (x (Pair Int Int)))
      (BoundaryError T Int (R #false) (cdr (x (Pair Int Int)))))
     ((dynamic-typecheck T Bool (R 4) (x Bool))
      (BoundaryError T Bool (R 4) (x Bool)))
     ((dynamic-typecheck T (U Bool Int) (R 3) (x (U Bool Int)))
      3)
     ((dynamic-typecheck T (U Bool Int) (R #false) (x (U Bool Int)))
      #false)
     ((dynamic-typecheck T (U (→ Int Int) Int) (R 3) (x (U (→ Int Int) Int)))
      3)
     ((dynamic-typecheck T (U (→ Int Int) Int) (R (λ (x TST) 3)) (x (U (→ Int Int) Int)))
      (mon T (→ Int Int) (R (λ (x TST) 3)) (π (x (U (→ Int Int) Int)))))
    )
  )

  (test-case "minimal-completion"
    (check-mf-apply*
     ((minimal-completion# (R 1))
      (R 1))
     ((minimal-completion# (T 1))
      (T 1))
     ((minimal-completion# (R #true))
      (R #true))
     ((minimal-completion# (T #true))
      (T #true))
     ((minimal-completion# (R (λ (x TST) 4)))
      (R (λ (x TST) 4)))
     ((minimal-completion# (T (λ (x TST) 4)))
      (T (λ (x TST) 4)))
     ((minimal-completion# (R (cons 1 1)))
      (R (cons 1 1)))
     ((minimal-completion# (T (cons 1 1)))
      (T (cons 1 1)))
     ((minimal-completion# (R free-vars))
      (R free-vars))
     ((minimal-completion# (T freedom))
      (T freedom))
     ((minimal-completion# (R (mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
      (R (mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
     ((minimal-completion# (T (mon T (→ Int Int) (R (λ (x TST) (+ x 1))) (f (→ Int Int)))))
      (T (mon T (→ Int Int) (R (λ (x TST) (+ (dyn-check Int x) (dyn-check Int 1)))) (f (→ Int Int)))))
     ((minimal-completion# (R (pre-mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
      (R (pre-mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
     ((minimal-completion# (T (pre-mon T (→ Int Int) (R (λ (x TST) (+ x 1))) (f (→ Int Int)))))
      (T (pre-mon T (→ Int Int) (R (λ (x TST) (+ (dyn-check Int x) (dyn-check Int 1)))) (f (→ Int Int)))))
     ((minimal-completion# (R (let (x Int (T (+ 2 2))) (+ x x))))
      (R (let (x Int (T (+ 2 2))) (+ (dyn-check Int x) (dyn-check Int x)))))
     ((minimal-completion# (T (let (x Int (R (+ 2 2))) (+ x x))))
      (T (let (x Int (R (+ (dyn-check Int 2) (dyn-check Int 2)))) (+ x x))))
     ((minimal-completion# (R (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (R (if (+ (dyn-check Int 1) (dyn-check Int 1)) (+ (dyn-check Int 1) (dyn-check Int 1)) (+ (dyn-check Int 1) (dyn-check Int 1)))))
     ((minimal-completion# (T (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (T (if (+ 1 1) (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (and (+ 1 1) (+ 1 1))))
      (R (and (+ (dyn-check Int 1) (dyn-check Int 1)) (+ (dyn-check Int 1) (dyn-check Int 1)))))
     ((minimal-completion# (T (and (+ 1 1) (+ 1 1))))
      (T (and (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (let (n1 TST (R #false)) n1)))
      (R (let (n1 TST (R #false)) n1)))
     ((minimal-completion# (R (= #true 2)))
      (R (= (dyn-check Int #true) (dyn-check Int 2))))
     ((minimal-completion# (R (f x)))
      (R ((dyn-check → f) x)))
     ((minimal-completion# (T (f x)))
      (T (f x)))
     ((minimal-completion# (R (car 1)))
      (R (car (dyn-check Pair 1))))
     ((minimal-completion# (T (car 1)))
      (T (car 1)))
     ((minimal-completion# (R (cdr 1)))
      (R (cdr (dyn-check Pair 1))))
     ((minimal-completion# (T (cdr 1)))
      (T (cdr 1)))
     ((minimal-completion# (R (+ 1 1)))
      (R (+ (dyn-check Int 1) (dyn-check Int 1))))
     ((minimal-completion# (T (+ 1 1)))
      (T (+ 1 1)))
     ((minimal-completion# (R (= 1 1)))
      (R (= (dyn-check Int 1) (dyn-check Int 1))))
     ((minimal-completion# (T (= 1 1)))
      (T (= 1 1)))
    )
  )

  (test-case "xerox"
    (check-mf-apply*
     ((xerox x)
      x)
     ((xerox xx«2)
      xx)
     ((xerox some-variable-name)
      some-variable-name)
    )
  )

  (test-case "apply-op"
    (check-mf-apply*
     ((apply-op car (cons 1 2))
      1)
     ((apply-op cdr (cons 1 2))
      2)
     ((apply-op + 1 2)
      3)
     ((apply-op = 1 2)
      #false)
    )
  )
)
