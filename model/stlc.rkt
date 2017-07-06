#lang mf-apply racket/base

;; Workspace for a type sound RST, based on simply-typed λ calculus

;; Status 2017-07-06 : ON HOLD.
;;  Set this model down, start a new one with just SR

;; (((SHORT TERM
;; - decide names, state lemmas
;; - formal lemmas + proofs
;; - simplify
;; - polymorphism)))

;; TODO
;; - substitution lemma (anything hard here?)
;; - mon, need to remember more things????
;; - mon, why/how not nested???
;; - lemma `∀L . ⊢L mon(t,e,L+) : t`
;; - (L E) ... the hole in E should always have context L
;;   - pre-mon cannot contain boundaries?

;; - (check-type (T e) τ)
;;   implies (check-type (S e) τ)
;;   implies (check-type (R e) τ)
;; - 

;; NEXT
;; - less ad-hoc about R dynamic checks
;;   - should be explicit, check integer args, function in app position
;; - can infer-type not care about language?
;;   - maybe, just change type= and its just 1 set of rules?
;; - Pair values
;; - polymorphism
;; - containers
;; - union types, recursive types

;; =============================================================================

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse))
)

;; =============================================================================

;; Simple [Racket Shallow Typed] language
(define-language++ RST #:alpha-equivalent? α=?
  (e ::= v (e e) x (let (x τ P) e) (+ e e) (= e e) (if e e e) (and e e) (pre-mon L τ P))
  (v ::= integer boolean Λ (mon L τ (L v)))
  (Λ ::= (λ (x τ) e))
  (P ::= (L e))
  (τ ::= Int Bool (Pair τ τ) (→ τ τ) TST)
  (L ::= R S T)
  (L\R ::= S T)
  (Γ ::= ((x τ) ...))
  (E ::= hole
         (E e) (v E)
         (+ E e) (+ v E)
         (= E e) (= v E)
         (if E e e)
         (and E e) (and v E)
         ;; --- following 2 handled explicitly ... I guess need "context/lang"?
         ;; (let (x τ (L E)) e) ;; ???
         ;; (pre-mon L τ P) ;; ???
         )
  (RuntimeError ::= (DynError P) (BoundaryError L τ P))
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
    (check-pred L\R? (term S))
    (check-pred L\R? (term T))
    (check-false (L\R? (term R)))
  )

)

;; -----------------------------------------------------------------------------
;; --- type checking / inference

(define-judgment-form RST
  #:mode (well-typed I)
  #:contract (well-typed P)
  [
   (infer-type () P τ)
   ---
   (well-typed P)])

(define-judgment-form RST
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (S e) τ_actual)
   (type= #{tag-only τ} #{tag-only τ_actual})
   ---
   (check-type Γ (S e) τ)]
  [
   (infer-type Γ (T e) τ)
   ---
   (check-type Γ (T e) τ)])

(define-judgment-form RST
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P τ)
  [
   ---
   (infer-type Γ (R integer) TST)]
  [
   ---
   (infer-type Γ (L\R integer) Int)]
  [
   ---
   (infer-type Γ (R boolean) TST)]
  [
   ---
   (infer-type Γ (L\R boolean) Bool)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (R e) τ_cod)
   ---
   (infer-type Γ (R (λ (x τ_dom) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (L\R e) τ_cod)
   ---
   (infer-type Γ (L\R (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (L\R e_0) τ_0)
   (infer-type Γ (L\R e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   ---
   (infer-type Γ (L\R (e_0 e_1)) τ_cod)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (R x) TST)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (L\R x) τ)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (R e_body) τ_body)
   ---
   (infer-type Γ (R (let (x τ P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (L\R e_body) τ_body)
   ---
   (infer-type Γ (L\R (let (x τ P) e_body)) τ_body)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (+ e_0 e_1)) TST)]
  [
   (infer-type Γ (L\R e_0) τ_0)
   (infer-type Γ (L\R e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (L\R (+ e_0 e_1)) Int)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (= e_0 e_1)) TST)]
  [
   (infer-type Γ (L\R e_0) τ_0)
   (infer-type Γ (L\R e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (L\R (= e_0 e_1)) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   (infer-type Γ (R e_2) τ_2)
   ---
   (infer-type Γ (R (if e_0 e_1 e_2)) TST)]
  [
   (infer-type Γ (L\R e_0) τ_0)
   (type= τ_0 Bool)
   (infer-type Γ (L\R e_1) τ_1)
   (infer-type Γ (L\R e_2) τ_2)
   (type= τ_1 τ_2)
   ---
   (infer-type Γ (L\R (if e_0 e_1 e_2)) τ_2)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (and e_0 e_1)) TST)]
  [
   (infer-type Γ (L\R e_0) τ_0)
   (infer-type Γ (L\R e_1) τ_1)
   (type= τ_0 Bool)
   (type= τ_1 Bool)
   ---
   (infer-type Γ (L\R (and e_0 e_1)) Bool)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (mon R τ P)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (L\R (mon L\R τ P)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (pre-mon R τ P)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (L\R (pre-mon L\R τ P)) τ)]
)

(define-metafunction RST
  check-type# : P τ -> boolean
  [(check-type# P τ)
   #true
   (judgment-holds (check-type () P τ))]
  [(check-type# P τ)
   #false])

(define-metafunction RST
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
     ((infer-type# (S (if (and #true #true) (+ 1 1) (+ 2 2))))
      Int)
     ((infer-type# (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (S (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)
     ((infer-type# (T (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)))

  (test-case "well-typed"
    (check-judgment-holds*
     (well-typed (T (λ (x Int) 2)))
     (infer-type () (T (λ (x Int) 3)) (→ Int Int))
     (check-type () (T (λ (x Int) 3)) (→ Int Int))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2))) 7)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (check-type () (T 1) Int)
     (infer-type () (S 1) Int)
     (check-type () (S 1) Int)
     (well-typed (S (let (x Int (S 1)) x)))
     (well-typed (S (let (x Int (S 1)) (let (y Int (S 2)) y))))
     (well-typed (S (let (x Int (S 1)) (let (y Int (S 2)) (+ x y)))))
    )

    (check-false (judgment-holds (well-typed (T (if (λ (x Int) x) 1 0)))))
  )
)

;; -----------------------------------------------------------------------------
;; --- "granularity"

;; L > L
(define-judgment-form RST
  #:mode (coarser-than I I)
  #:contract (coarser-than L L)
  [
   ---
   (coarser-than R S)]
  [
   ---
   (coarser-than S T)]
  [
   --- Trans
   (coarser-than R T)])

;; L < L
(define-judgment-form RST
  #:mode (finer-than I I)
  #:contract (finer-than L L)
  [
   ---
   (finer-than S R)]
  [
   ---
   (finer-than T S)]
  [
   --- Trans
   (finer-than T R)])

(module+ test
  (test-case "coarser/finer"
    (check-true (judgment-holds (coarser-than R T)))
    (check-true (judgment-holds (coarser-than R S)))
    (check-true (judgment-holds (coarser-than S T)))

    (check-false (judgment-holds (finer-than R T)))
    (check-false (judgment-holds (finer-than R S)))
    (check-false (judgment-holds (finer-than S T)))

    (check-true (judgment-holds (finer-than T R)))
    (check-true (judgment-holds (finer-than S R)))
    (check-true (judgment-holds (finer-than T S)))

    (check-false (judgment-holds (coarser-than T R)))
    (check-false (judgment-holds (coarser-than S R)))
    (check-false (judgment-holds (coarser-than T S)))

    (check-false (judgment-holds (finer-than R R)))
    (check-false (judgment-holds (finer-than S S)))
    (check-false (judgment-holds (finer-than T T)))))

;; -----------------------------------------------------------------------------
;; --- flat types

;; `(flat L τ)` iff `τ` is strictly positive and `L` fully-checks values with type `τ`
(define-judgment-form RST
  #:mode (flat I I)
  #:contract (flat L τ)
  [
   ---
   (flat L\R Int)]
  [
   ---
   (flat L\R Bool)]
  [
   (flat T τ_0)
   (flat T τ_1)
   ---
   (flat T (Pair τ_0 τ_1))])

(module+ test
  (test-case "flat"
    (check-true (judgment-holds (flat T Int)))
    (check-true (judgment-holds (flat S Int)))
    (check-false (judgment-holds (flat R Int)))

    (check-true (judgment-holds (flat T (Pair Int Int))))
    (check-false (judgment-holds (flat S (Pair Int Int))))
    (check-false (judgment-holds (flat T (Pair Int (Pair (→ Int Int) Int)))))
  )
)

;; -----------------------------------------------------------------------------
;; --- dynamic-typecheck

;; Only called when τ is from "finer" language than P
(define-judgment-form RST
  #:mode (dynamic-typecheck I I)
  #:contract (dynamic-typecheck (L v) τ)
  [
   (side-condition ,(raise-user-error 'dynamic-typecheck "language R has no dynamic typechecker ~a ~a" (term e) (term τ)))
   --- R
   (dynamic-typecheck (R v) τ)]
  [
   ---
   (dynamic-typecheck (L\R integer) Int)]
  [
   ---
   (dynamic-typecheck (L\R boolean) Bool)]
  [
   ---
   (dynamic-typecheck (L\R (λ (x _) e)) (→ τ_dom τ_cod))]
  [
   ;; OK because same type
   ---
   (dynamic-typecheck (L\R (mon L_0 τ P)) τ)])

(module+ test
  (test-case "dynamic-typecheck"
    (check-true (judgment-holds (dynamic-typecheck (S 4) Int)))
    (check-false (judgment-holds (dynamic-typecheck (S 4) Bool)))

    (check-true (judgment-holds (dynamic-typecheck (S (λ (x Int) 3)) (→ Int Int))))
    (check-true (judgment-holds (dynamic-typecheck (T (λ (x Int) 3)) (→ Int Int))))
    (check-true (judgment-holds (dynamic-typecheck (S (λ (x Bool) #false)) (→ Bool Bool))))
    (check-true (judgment-holds (dynamic-typecheck (T (λ (x Bool) #false)) (→ Bool Bool))))
  )
)

;; -----------------------------------------------------------------------------
;; --- evalution

(define -->RST
  (reduction-relation RST
    #:domain A
;; -- MON
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx P)))
     (L (in-hole E (pre-mon L_ctx τ_ctx P_step)))
     PreMon-Step
     (where (P_step) ,(apply-reduction-relation -->RST (term P)))]
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx P)))
     RuntimeError
     PreMon-Error
     (where (RuntimeError) ,(apply-reduction-relation -->RST (term P)))]
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
     (L (in-hole E v_+))
     PreMon-CoarserContext
     (judgment-holds (coarser-than L_ctx L_v))
     (where v_+ ,(if (judgment-holds (flat L_v τ_ctx))
                   (term v) ;; Assumes `⊢ v : τ_ctx`
                   (term (mon L_ctx τ_ctx (L_v v)))))]
    [-->
     (L (in-hole E (pre-mon L τ (L v))))
     (L (in-hole E v))
     PreMon-NoBoundary]
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
     (L (in-hole E v_+))
     PreMon-FinerContext-M
     (judgment-holds (finer-than L_ctx L_v))
     (judgment-holds (dynamic-typecheck (L_ctx v) τ_ctx))
     (where v_+ ,(if (judgment-holds (flat L_ctx τ_ctx))
                   (term v)
                   (term (mon L_ctx τ_ctx (L_v v)))))]
    [-->
     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
     (BoundaryError L_ctx τ_ctx (L_v v))
     PreMon-FinerContext-N
     (judgment-holds (finer-than L_ctx L_v))
     (side-condition (not (judgment-holds (dynamic-typecheck (L_ctx v) τ_ctx))))]
;; -- APP
    [-->
     (L (in-hole E ((λ (x τ) e) v_1)))
     (L (in-hole E (substitute e x v_1)))
     App-Beta]
    [-->
     (L (in-hole E ((mon L_ctx (→ τ_dom τ_cod) (L_λ v)) v_1)))
     (L (in-hole E (pre-mon L_ctx τ_cod (L_λ (v (pre-mon L_λ τ_dom (L_ctx v_1)))))))
     App-Mon]
    [-->
     (R (in-hole E (v_0 v_1)))
     (DynError (R (v_0 v_1)))
     App-Error
     (side-condition (not (judgment-holds (proc? v_0))))]
;; -- LET
    [-->
     (L (in-hole E (let (x τ P) e_body)))
     (L (in-hole E (let (x τ P_step) e_body)))
     Let
     (where (P_step) ,(apply-reduction-relation -->RST (term P)))]
    [-->
     (L (in-hole E (let (x τ (L_v v)) e_body)))
     (L (in-hole E ((λ (x τ) e_body) (pre-mon L τ (L_v v)))))
     Let-Beta]
;; -- Primop, If, etc
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
     (L (in-hole E (if #true e_1 e_2)))
     (L (in-hole E e_1))
     If-True]
    [-->
     (L (in-hole E (if #false e_1 e_2)))
     (L (in-hole E e_2))
     If-False]
    [-->
     (R (in-hole E (if v_0 e_1 e_2)))
     (DynError (R (if v_0 e_1 e_2)))
     If-Error
     (side-condition (not (boolean? (term v_0))))]
))

(define -->RST*
  (make--->* -->RST))

(define-metafunction RST
  eval : P -> A
  [(eval P)
   A
   (judgment-holds (well-typed P))
   (where A ,(-->RST* (term P)))]
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
      (DynError (R (if 1 2 3))))
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
    )
  )

  (test-case "eval:R:II"
    (check-mf-apply*
      ((eval (R (let (n1 Bool (R #false)) n1)))
       (R #false))
      ((eval (R (let (n1 Int (R (+ 2 2))) (+ n1 n1))))
       (R 8))
      ((eval (R ((λ (x TST) (+ x 1)) 1)))
       (R 2))
      ((eval (R (1 1)))
       (DynError (R (1 1))))
      ((eval (R ((mon R (→ Int Int) (T (λ (x Int) 2))) 7)))
       (R 2))
    )
  )

  (test-case "eval:S:I"
    (check-mf-apply*
     ((eval (S (if (and #true #true) (+ 1 1) (+ 2 2))))
      (S 2))
     [(eval (S #true))
      (S #true)]
     [(eval (S (+ 2 2)))
      (S 4)]
     [(eval (S ((λ (x Int) x) 1)))
      (S 1)]
     [(eval (S ((λ (x Int) (+ x 1)) 1)))
      (S 2)]
     [(eval (S (if #false (+ 6 6) 0)))
      (S 0)]
     [(eval (S (let (x Int (S 1))
                 (let (y Int (S 2))
                   (+ x y)))))
      (S 3)]
     [(eval (S (let (negate (→ Bool Bool) (S (λ (x Bool) (if x #false #true))))
                 (let (b Bool (S #false))
                   (negate (negate b))))))
      (S #false)]
     [(eval (S (let (x Int (S 4))
                 (let (add-x (→ Int Int) (S (λ (y Int) (+ y x))))
                   (let (x Int (S 5))
                     (add-x x))))))
      (S 9)]
    )
  )

  (test-case "eval:simple:S:fail"
    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (S ((λ (x Int) (+ x 1)) #false))})))

    (check-exn #rx"typechecking failed"
      (λ () (term (eval (S (let (x Bool (S (+ 2 5))) x))))))
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
      (BoundaryError T Int (R #false))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError (R (+ 3 #false)))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError (R (+ #true #false)))]
    )
  )

  #;(test-case "apply-R-in-S"
    (check-mf-apply*
     [(eval (S (let ((f R (:: (λ (x) (+ x 1)) (→ Integer Integer))))
                 (f 3))))
      4]
     [(eval (S (let ((f R (:: (λ (x) (box x)) (→ Integer (Boxof Integer)))))
                 (f 3))))
      (box 3)]
     [(eval (S (let ((f R (:: (λ (x) (box #f)) (→ Integer (Boxof Integer)))))
                 (f 3))))
      (box #f)] ;; tag sound!
    )

    (check-exn #rx"expected Integer given #f"
      (λ () (term (eval (S (let ((f R (:: (λ (x) #false) (→ Integer Integer)))) (f 3)))))))

    (check-exn #rx"expected address for integer"
      (λ () (term (eval (S (let ((f R (:: (λ (x) (+ #true #false)) (→ Integer Integer)))) (f 3)))))))
  )

  #;(test-case "double-wrap"
    (check-exn #rx"T expected \\(→ Boolean Boolean\\) given \\(CLOSURE"
      (λ () (term
        (eval (T (let ((h R (:: (let ((g T (:: (let ((f R (:: (λ (x) x)
                                                              (→ Integer Integer))))
                                                 f)
                                               (→ Integer Integer)))) g)
                                (→ Boolean Boolean))))
                   (h #true))))))))


)

;; -----------------------------------------------------------------------------
;; --- type helpers

(define-metafunction RST
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

(define-metafunction RST
  coerce-→ : τ -> τ
  [(coerce-→ TST)
   (→ TST TST)]
  [(coerce-→ (→ τ_dom τ_cod))
   (→ τ_dom τ_cod)]
  [(coerce-→ τ)
   ,(raise-argument-error 'coerce-→ "cannot coerce ~a" (term τ))])

(define-judgment-form RST
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   --- Refl
   (type= τ τ)])

(module+ test
  (test-case "tag-only"
    (check-mf-apply*
     ((tag-only Int)
      Int)
     ((tag-only (→ Int Bool))
      (→ TST TST))
     ((tag-only (Pair (→ Int Int) Bool))
      (Pair TST TST))))

  (test-case "coerce-→"
    (check-mf-apply*
     ((coerce-→ (→ Int Bool))
      (→ Int Bool))
     ((coerce-→ TST)
      (→ TST TST))))
)

;; -----------------------------------------------------------------------------
;; --- environment helpers

(define-metafunction RST
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction RST
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

;; -----------------------------------------------------------------------------
;; --- eval helpers

(define-judgment-form RST
  #:mode (proc? I)
  #:contract (proc? v)
  [
   ---
   (proc? (λ (x τ) e))]
  [
   ;; TODO should only check type? Depends on L?
   (proc? v_1)
   ---
   (proc? (mon L_0 τ_0 (L_1 v_1)))])

