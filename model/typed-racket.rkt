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
  (e ::= v (e e) x (let (x τ P) e) (cons e e) (car e) (cdr e) (+ e e) (= e e) (if e e e) (and e e) (pre-mon L τ P srcloc))
  (v ::= integer boolean Λ (cons v v) (mon L τ (L v) srcloc))
  (Λ ::= (λ (x τ) e))
  (P ::= (L e))
  (τ ::= (U τk ...) τk TST)
  (τk ::= Int Bool (Pair τ τ) (→ τ τ))
  (L ::= R T)
  (Γ ::= ((x τ) ...))
  (E ::= hole
         (E e) (v E)
         (cons E e) (cons v E)
         (car E) (cdr E)
         (+ E e) (+ v E)
         (= E e) (= v E)
         (if E e e)
         (and E e) (and v E))
  (RuntimeError ::= (DynError P) (BoundaryError L τ P srcloc))
  (srcloc ::= (dom srcloc) (cod srcloc) (car srcloc) (cdr srcloc) (x τ))
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
   ---
   (infer-type Γ (R integer) TST)]
  [
   ---
   (infer-type Γ (T integer) Int)]
  [
   ---
   (infer-type Γ (R boolean) TST)]
  [
   ---
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
   ---
   (infer-type Γ (R (λ (x TST) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (T e) τ_cod)
   ---
   (infer-type Γ (T (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   ---
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
   (infer-type Γ P _)
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e_body) τ_body)
   ---
   (infer-type Γ (R (let (x TST P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (T e_body) τ_body)
   ---
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
                         (R (let (g TST
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
    )

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
     PreMon-FinerContext-MaybeOk
     (where v_+ #{dynamic-typecheck T τ_ctx (R v) srcloc})]
    [-->
     (L (in-hole E (pre-mon T τ_ctx (R v) srcloc)))
     RuntimeError
     PreMon-FinerContext-NotOk
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
    [-->
     (R (in-hole E (v_0 v_1)))
     (DynError (R (v_0 v_1)))
     App-Error
     (side-condition (not (judgment-holds (proc? v_0))))]
;; -- LET
    [-->
     (L (in-hole E (let (x τ P) e_body)))
     (L (in-hole E (let (x τ P_step) e_body)))
     Let-Step
     (where (P_step) ,(apply-reduction-relation -->μTR (term P)))]
    [-->
     (L (in-hole E (let (x τ (L_v v)) e_body)))
     (L (in-hole E ((λ (x τ) e_body) (pre-mon L τ (L_v v) (#{xerox x} τ)))))
     Let-Beta]
;; -- Primop, If, etc
    [-->
     (L (in-hole E (car (cons v_0 v_1))))
     (L (in-hole E v_0))
     Car]
    [-->
     (R (in-hole E (car v)))
     (DynError (R (car v)))
     Car-Error
     (side-condition (not (judgment-holds (cons? v))))]
    [-->
     (L (in-hole E (cdr (cons v_0 v_1))))
     (L (in-hole E v_1))
     Cdr]
    [-->
     (R (in-hole E (cdr v)))
     (DynError (R (cdr v)))
     Cdr-Error
     (side-condition (not (judgment-holds (cons? v))))]
    [-->
     (L (in-hole E (+ integer_0 integer_1)))
     (L (in-hole E ,(+ (term integer_0) (term integer_1))))
     +]
    [-->
     (R (in-hole E (+ v_0 v_1)))
     (DynError (R (+ v_0 v_1)))
     +-Error
     (side-condition (or (not (integer? (term v_0))) (not (integer? (term v_1)))))]
    [-->
     (L (in-hole E (= integer_0 integer_1)))
     (L (in-hole E ,(= (term integer_0) (term integer_1))))
     =]
    [-->
     (R (in-hole E (= v_0 v_1)))
     (DynError (R (= v_0 v_1)))
     =-Error
     (side-condition (or (not (integer? (term v_0))) (not (integer? (term v_1)))))]
    [-->
     (L (in-hole E (and boolean_0 boolean_1)))
     (L (in-hole E ,(and (term boolean_0) (term boolean_1))))
     And]
    [-->
     (R (in-hole E (and v_0 v_1)))
     (DynError (R (and v_0 v_1)))
     And-Error
     (side-condition (or (not (boolean? (term v_0))) (not (boolean? (term v_1)))))]
    [-->
     (L (in-hole E (if v e_1 e_2)))
     (L (in-hole E e_1))
     If-True
     (side-condition (not (eq? #false (term v))))]
    [-->
     (L (in-hole E (if #false e_1 e_2)))
     (L (in-hole E e_2))
     If-False]))

(define-metafunction μTR
  xerox : x -> x
  [(xerox x)
   ,(string->symbol (car (string-split (symbol->string (term x)) "«")))])

(define -->μTR*
  (make--->* -->μTR))

(define-metafunction μTR
  eval : P -> A
  [(eval P)
   A
   (judgment-holds (well-typed P))
   (where A ,(-->μTR* (term P)))]
  [(eval P)
   ,(raise-user-error 'eval "trouble eval'ing ~a" (term P))
   (judgment-holds (well-typed P))]
  [(eval P)
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
      (DynError (R (and 1 2))))
     ((eval (R (and #true 3)))
      (DynError (R (and #true 3))))
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
      (DynError (R (= #true 2))))
     ((eval (R (= 3 (= 1 1))))
      (DynError (R (= 3 #true))))
     ((eval (R (+ 2 2)))
      (R 4))
     ((eval (R (+ #true 2)))
      (DynError (R (+ #true 2))))
     ((eval (R (+ 2 #true)))
      (DynError (R (+ 2 #true))))
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
       (DynError (R (1 1))))
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
      (DynError (R (+ 3 #false)))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError (R (+ #true #false)))]
    )
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
                       (R (let (g TST
                                  (T (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h #true))))
      (BoundaryError T Int (R #true) (cod (f (→ Int Int)))))
     ((eval (T (let (h (→ Int Int)
                       (R (let (g TST
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
    )
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
 ;; value or BoundaryError
(define-metafunction μTR
  dynamic-typecheck : L τ P srcloc -> any
  [(dynamic-typecheck R τ P srcloc)
   ,(raise-user-error 'dynamic-typecheck "language R has no dynamic typechecker ~a ~a" (term e) (term τ))]
  [(dynamic-typecheck T Int (L integer) srcloc)
   integer]
  [(dynamic-typecheck T Int (L v) srcloc)
   (BoundaryError T Int (L v) srcloc)]
  [(dynamic-typecheck T Bool (L boolean) srcloc)
   boolean]
  [(dynamic-typecheck T Bool (L v) srcloc)
   (BoundaryError T Bool (L v) srcloc)]
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
  [(dynamic-typecheck T (→ τ_dom τ_cod) (L Λ) srcloc)
   (mon T (→ τ_dom τ_cod) (L Λ) srcloc)]
  [(dynamic-typecheck T τ (L (mon L_mon τ_mon P_mon srcloc_mon)) srcloc)
   RuntimeError
   (where TST τ_mon)
   (where RuntimeError #{dynamic-typecheck T τ P_mon srcloc})]
  [(dynamic-typecheck T τ (L (mon L_mon τ_mon P_mon srcloc_mon)) srcloc)
   v ;; TODO remove this case, TST should not be a chaperone
   (where TST τ_mon)
   (where v #{dynamic-typecheck T τ P_mon srcloc})]
  [(dynamic-typecheck T τ P srcloc)
   (mon T τ P srcloc)
   ;; τ must be non-flat, because that's the only type we keep mon's for
   (where (L (mon L_mon τ_mon P_mon srcloc_mon)) P)
   (judgment-holds (type= #{tag-only τ_mon} #{tag-only τ}))]
  [(dynamic-typecheck T TST (L v) srcloc)
   v
   (side-condition (printf "WARNING: T expects value ~a to have TST~n" (term v)))])

;; TODO
;; (dynamic-typecheck T (→ Int Int) (R (mon R TST (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b2 TST))) (b3 TST))

(define-judgment-form μTR
  #:mode (proc? I)
  #:contract (proc? v)
  [
   ---
   (proc? (λ (x τ) e))]
  [
   ;; TODO should only check type? Depends on L?
   (proc? v_1)
   ---
   (proc? (mon L_0 τ_0 (L_1 v_1) srcloc))])

(define-judgment-form μTR
  #:mode (cons? I)
  #:contract (cons? v)
  [
   ---
   (cons? (cons e_0 e_1))]
  [
   (cons? v_1) ;; TODO should only check type? Depends on L?
   ---
   (cons? (mon L_0 τ_0 (L_1 v_1) srcloc))])

(define-metafunction μTR
  tag-only : τ -> τ
  [(tag-only Int)
   Int]
  [(tag-only Bool)
   Bool]
  [(tag-only (Pair τ_0 τ_1))
   (Pair TST TST)]
  [(tag-only (→ τ_dom τ_cod))
   (→ TST TST)]
  [(tag-only TST)
   TST])

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
    )
  )
)

