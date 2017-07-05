#lang mf-apply racket/base

;; Workspace for a type sound RST, based on simply-typed λ calculus

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
(define-language RST
  (e ::= v (e e) x (let (x τ P) e) (+ e e) (= e e) (if e e e) (and e e) (pre-mon L τ P))
  (v ::= integer boolean (λ (x τ) e) (mon L τ (L v)))
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
         (and E e)
         ;; --- following 2 handled explicitly ... I guess need "context/lang"?
         ;; (let (x τ (L E)) e) ;; ???
         ;; (pre-mon L τ P) ;; ???
         )
  (RuntimeError ::= (AppError P) (BoundaryError L τ P))
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (λ (x τ) e #:refers-to x))

(define (α=? e0 e1)
  (alpha-equivalent? RST e0 e1))

(module+ test
  (*term-equal?* α=?)

  (define-syntax (define-predicate* stx)
    (syntax-parse stx
     [(_ [x*:id ...])
      #:with (x?* ...) (for/list ([x (in-list (syntax-e #'(x* ...)))]) (format-id stx "~a?" (syntax-e x)))
      (syntax/loc stx (begin (define x?* (redex-match? RST x*)) ...))]))

  (define-predicate* [e v τ Γ P])

  (test-case "define-language"
    (check-pred e? (term 2))
    (check-pred e? (term (+ 1 1)))
    (check-pred e? (term (= x 1)))
    (check-pred e? (term (if (= x 1) 1 #false)))
    (check-pred τ? (term (→ Int Int)))
    (check-pred τ? (term TST))
    (check-pred P? (term (R (if (= x 1) 1 #false))))
    (check-pred P? (term (R (λ (x TST) (if (= x 1) 1 #false)))))
    (check-pred P? (term (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))))

)

;; -----------------------------------------------------------------------------
;; --- check-type

(define-judgment-form RST
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (S e) #{tag-only τ})
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
   (infer-type Γ (L\R boolean) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (R e) τ_cod)
   ---
   (infer-type Γ (R (λ (x τ_dom) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (R e) τ_cod)
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

  (test-case "infer-type#"
    (check-mf-apply*
     ((infer-type# (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (S (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)
     ((infer-type# (T (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)))
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

;(define -->RST
;  (reduction-relation RST
;    #:domain P
;;; -- MON
;    [-->
;     (L (in-hole E (pre-mon L_ctx τ_ctx P)))
;     (L (in-hole E (pre-mon L_ctx τ_ctx P_step)))
;     PreMon-Step
;     (where (P_step) ,(apply-reduction-relation -->RST (term P)))]
;    [-->
;     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
;     (L (in-hole E v_+))
;     PreMon-CoarserContext
;     (judgment-holds (coarser-than L_ctx L_v))
;     (where v_+ ,(if (judgment-holds (flat L_v τ_ctx))
;                   (term v) ;; Assumes `⊢ v : τ_ctx`
;                   (term (mon L_ctx τ_ctx (L_v v)))))]
;    [-->
;     (L (in-hole E (pre-mon L τ (L v))))
;     (L (in-hole E v))
;     PreMon-NoBoundary]
;    [-->
;     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
;     (L (in-hole E v_+))
;     PreMon-FinerContext-M
;     (judgment-holds (finer-than L_ctx L_v))
;     (judgment-holds (dynamic-typecheck (L_v v) τ))
;     (where v_+ ,(if (judgment-holds (flat L_v τ_ctx))
;                   (term v)
;                   (term (mon L_ctx τ_ctx (L_v v)))))]
;    [-->
;     (L (in-hole E (pre-mon L_ctx τ_ctx (L_v v))))
;     (L (BoundaryError L_ctx τ_ctx (L_v v)))
;     PreMon-FinerContext-N
;     (judgment-holds (finer-than L_ctx L_v))
;     (side-condition ,(not (judgment-holds (dynamic-typecheck (L_v v) τ}))))]
;;; -- APP
;    [-->
;     (L (in-hole E ((λ (x τ) e) v_1)))
;     (L (in-hole E (substitute e x v_1)))
;     App-Beta]
;    [-->
;     (L (in-hole E ((mon L_ctx (→ τ_dom τ_cod) (L_λ v)) v_1)))
;     (L (in-hole E (pre-mon L_ctx τ_cod (L_λ (v (pre-mon L_λ τ_dom (L_ctx v_1)))))))
;     App-Mon]
;    [-->
;     (R (in-hole E (v_0 v_1)))
;     (DynError (R (v_0 v_1)))
;     App-Error]
;;; -- LET
;    [-->
;     (L (in-hole E (let (x τ P) e_body)))
;     (L (in-hole E (let (x τ P_step) e_body)))
;     Let
;     (where (P_step) ,(apply-reduction-relation -->RST (term P)))]
;    [-->
;     (L (in-hole E (let (x τ (L_v v)) e_body)))
;     (L (in-hole E ((λ (x τ) e_body) (pre-mon L τ (L_v v)))))
;     Let-Beta]
;;; -- Primop, If, etc
;    [-->
;     (L (in-hole E (+ integer_0 integer_1)))
;     (L (in-hole E ,(+ (term integer_0) (term integer_1))))
;     +]
;    [-->
;     (R (in-hole E (+ v_0 v_1)))
;     (DynError (R (+ v_0 v_1)))
;     +-Error]
;    [-->
;     (L (in-hole E (= integer_0 integer_1)))
;     (L (in-hole E ,(= (term integer_0) (term integer_1))))
;     =]
;    [-->
;     (R (in-hole E (= v_0 v_1)))
;     (DynError (R (= v_0 v_1)))
;     =-Error]
;    [-->
;     (L (in-hole E (and #true e_1)))
;     (L (in-hole E e_1))
;     And-True]
;    [-->
;     (L (in-hole E (and #false e_1)))
;     (L (in-hole E #false))
;     And-False]
;    [-->
;     (R (in-hole E (and v_0 e_1)))
;     (DynError (R (and v_0 e_1)))
;     And-Error]
;    [-->
;     (L (in-hole E (if #true e_1 e_2)))
;     (L (in-hole E e_1))
;     If-True]
;    [-->
;     (L (in-hole E (if #false e_1 e_2)))
;     (L (in-hole E e_2))
;     If-False]
;    [-->
;     (R (in-hole E (if v_0 e_1 e_2)))
;     (DynError (R (if v_0 e_1 e_2)))
;     If-Error]
;))

(module+ test
)

;; simple rule for application
;; - if e0 not value then step
;; - if e1 not value then step
;; - if L_ctx = R and v0 not λ then die
;; - if L_ctx finer-than L_λ then mon(t_cod (e[x ↦ mon(t_dom v1 L_ctx)]) L_λ)
;; - if L_ctx coarser-than L_λ then e[x ↦ mon(t_dom v1 L_ctx)]
;; - else e[x ↦ v1]

;; lang(mon _ _ L) = L
;; lang(_) = L_ctx

;; typeof(mon τ _ _) = τ
;; typeof(_) = τ0 or (TST → TST)

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
;; --- examples

;; Assume type-checked,
;; ((λR f . f) (λS x . (+ x 1))) :: String->String
;; --> (mon [String->String] R ((λ f . f) (mon [Int->Int] (λS x . (+ x 1)))))
;; --> (mon [String->String] R (mon [Int->Int] (λS x . (+ x 1))))
;; --> (mon [String->String] R (λS x . (+ x 1)))
;; ??? why does/should this work ??!
