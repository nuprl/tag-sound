#lang mf-apply racket/base

;; Machine-tag-sound typed language.
;; Two theorems:
;; 1. SOUNDNESS === if Γ ⊢ e ⇓ c : τ then either:
;;   - c -->* v  and  τ ⊨ v
;;   - c diverges
;;   - c raises DivisionByZero
;;   - c raises CheckError(κ v)
;; 2. OPTIMIZATION === if e_0 ⊑ e_1 and e_1 -->* v then:
;;   - e_0 -->* v
;;   - e_0 <~ e_1
;;
;; Interpretation:
;; (1) is tag soundness, if you predict a type thats what you get
;;     though the program might end in a nondescript check error
;; (2) is "guaranteed optimization", if you add types the program will
;;     use fewer tag checks (the <~ relation is a kind of stepping simulation)

;; TODO
;; - refine +, track natural vs. int ?
;; - redundant in unbox ... wherever we need the type after a primop
;;   - should `check` return the inferred type?
;; - recursive functions work
;; - untyped function, unbound variables hack
;; - stores in reduction-relation

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs
  redex-abbrevs/unstable
  (only-in racket/string string-split))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; =============================================================================

(define-language++ TAG #:alpha-equivalent? α=?
  ;; --- e = source language
  (e ::= ve x (e e) (if e e e) (let (x τ φ e) e)
         (δ e ...))
  (ve ::= integer boolean (fun f (x) e) (fun f τ τ (x) e))
  ;; eτ = intermediate language
  ;;;; (eτ ::= vτ (x : τφ) ((eτ eτ) : τφ) ((if eτ eτ eτ) : τφ)
  ;;;;         ((let (x τ eτ) eτ) : τφ)
  ;;;;         ((binop eτ eτ) : τφ) ((unop eτ) : τφ))
  ;;;; (vτ ::= (integer : τφ) (boolean : τφ) ((fun f (x : τφ) eτ) : τφ))
  ;; --- c = target language
  (c ::= ;; completions
         v x (c c) (if c c c) (let (x c) c)
         (δ c ...) (check κ c))
  (C ::= hole (C c) (v C) (if C c c) (let (x C) c) (δ v ... C c ...) (check κ C))
  (v ::= integer boolean (fun f (x) c))
  (δ ::= δ- δ= δ+)
  (δ- ::= + / and or unbox set-box!)
  (δ= ::= int? bool? proc? box?)
  (δ+ ::= make-box)
  (δ-cod ::= RuntimeError v)
  ;; ---
  (τ ::= (U τ0 ...) τ0)
  (τ0 ::= Natural Integer Boolean (Box τ) (→ τ τ))
  (τφ ::= (U φ τφ0 ...) τφ0)
  (τφ0 ::= (Natural φ) (Integer φ) (Boolean φ) (Box φ τφ) (→ φ τφ τφ))
  (φ ::= ++ --)
  (κ ::= int bool proc box)
  (Γ ::= ((x τφ) ...))
  (RuntimeError ::= DivisonByZero)
  (CheckError ::= (Check v κ))
  (A ::= c RuntimeError CheckError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (fun f τ_dom τ_cod (x) e #:refers-to (shadow f x))
  (fun f (x) e #:refers-to (shadow f x))
  (let (x τ φ e_x) e #:refers-to x)
  (fun f (x) c #:refers-to (shadow f x))
  (let (x c_x) c #:refers-to x)
)

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (check-type I I I O)
  #:contract (check-type Γ e κ c)
  [
   (infer-type Γ e c τφ_c)
   (tag=? τφ_c κ)
   (flag++ τφ_c)
   ---
   (check-type Γ e κ c)]
  [
   (infer-type Γ e c τφ_c)
   (tag=? τφ_c κ)
   (flag-- τφ_c)
   (where c_+ (check κ c))
   ---
   (check-type Γ e κ c_+)])

(define-judgment-form TAG
  #:mode (infer-type I I O O)
  #:contract (infer-type Γ e c τφ)
  [
   ---
   (infer-type Γ integer integer (Integer ++))]
  [
   ---
   (infer-type Γ boolean boolean (Boolean ++))]
  [
   (add-φ τ_dom -- τφ_dom)
   (where Γ_x #{type-env-add Γ x τφ_dom})
   ;; TODO need to add `f` to `Γ` ... but need to decide if τ_cod is present or absent
   (infer-type Γ_x e c τφ_cod)
   ---
   (infer-type Γ (fun f τ_dom τ_cod (x) e) (fun f (x) c) (→ ++ τφ_dom τφ_cod))]
  [
   (infer-type Γ e_0 c_0 (→ φ τφ_dom τφ_cod))
   (infer-type Γ e_1 c_1 τφ_1)
   (type=? τφ_dom τφ_1)
   (where c_0+ ,(if (judgment-holds (flag++ (→ φ τφ_dom τφ_cod)))
                  (term c_0)
                  (term (check proc c_0))))
   ---
   (infer-type Γ (e_0 e_1) (c_0+ c_1) τφ_dom)]
  [
   (infer-type Γ e_0 c_0 τφ_0)
   (infer-type Γ e_1 c_1 τφ_1)
   (infer-type Γ e_2 c_2 τφ_1)
   ;; TODO τφ_12 don't need to be the same
   ;; - same type, but unify flags
   ;; - return U of the 2
   ---
   (infer-type Γ (if e_0 e_1 e_2) (if c_0 c_1 c_2) τφ_1)]
  [
   (infer-type Γ e_x c_x τφ_x)
   (type=? τ_x #{erase-φ# τφ_x})
   (where Γ_x #{type-env-add Γ x τφ_x})
   (infer-type Γ_x e c τφ)
   --- Let-τ
   (infer-type Γ (let (x τ_x ++ e_x) e) (let (x c_x) c) τφ)]
  [
   (infer-completion Γ e_x c_x)
   (add-φ τ_x -- τφ_x)
   (where Γ_x #{type-env-add Γ x τφ_x})
   (infer-type Γ_x e c τφ)
   --- Let-λ
   (infer-type Γ (let (x τ_x -- e_x) e) (let (x c_x) c) τφ)]
  ;; --- δ
  [
   (check-type Γ e_0 int c_0)
   (check-type Γ e_1 int c_1)
   ---
   (infer-type Γ (+ e_0 e_1) (+ c_0 c_1) (Integer ++))]
  [
   (check-type Γ e_0 int c_0)
   (check-type Γ e_1 int c_1)
   ---
   (infer-type Γ (/ e_0 e_1) (/ c_0 c_1) (Integer ++))]
  [
   (check-type Γ e_0 bool c_0)
   (check-type Γ e_1 bool c_1)
   ---
   (infer-type Γ (and e_0 e_1) (and c_0 c_1) (Boolean ++))]
  [
   (check-type Γ e_0 bool c_0)
   (check-type Γ e_1 bool c_1)
   ---
   (infer-type Γ (or e_0 e_1) (or c_0 c_1) (Boolean ++))]
  [
   (check-type Γ e_0 box c_0)
   (infer-type Γ e_0 _ τφ_0) ;; TODO redundant
   ---
   (infer-type Γ (unbox e_0) (unbox c_0) τφ_0)]
  [
   (check-type Γ e_0 box c_0)
   (infer-type Γ e_1 c_1 τφ_1)
   ;; TODO should types match?
   ---
   (infer-type Γ (set-box! e_0 e_1) (set-box! c_0 c_1) (Box ++ τφ_1))]
  [
   (infer-type Γ e_0 c_0 _)
   ---
   (infer-type Γ (int? e_0) (int? c_0) (Boolean ++))]
  [
   (infer-type Γ e_0 c_0 _)
   ---
   (infer-type Γ (bool? e_0) (bool? c_0) (Boolean ++))]
  [
   (infer-type Γ e_0 c_0 _)
   ---
   (infer-type Γ (box? e_0) (box? c_0) (Boolean ++))]
  [
   (infer-type Γ e_0 c_0 _)
   ---
   (infer-type Γ (proc? e_0) (proc? c_0) (Boolean ++))]
  [
   (infer-type Γ e_0 c_0 τφ_0)
   ---
   (infer-type Γ (make-box e_0) (make-box c_0) (Box ++ τφ_0))])

(define-judgment-form TAG
  #:mode (infer-completion I I O)
  #:contract (infer-completion Γ e c)
  [
   ---
   (infer-completion Γ integer integer)]
  [
   ---
   (infer-completion Γ boolean boolean)]
  [
   (infer-completion Γ e c)
   ;; TODO
   ---
   (infer-completion Γ (fun f (x) e) (fun f (x) c))]
  [
   ---
   (infer-completion Γ x x)]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check proc c_0))
   ---
   (infer-completion Γ (e_0 e_1) (c_0+ c_1))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (infer-completion Γ e_2 c_2)
   ---
   (infer-completion Γ (if e_0 e_1 e_2) (if e_0 e_1 e_2))]
  [
   (infer-type Γ e_x c_x τφ_x)
   (type=? τ_x #{erase-φ# τφ_x})
   (where Γ_x #{type-env-add Γ x τφ_x})
   (infer-completion Γ_x e c)
   --- Let-τ
   (infer-completion Γ (let (x τ_x ++ e_x) e) (let (x c_x) c))]
  [
   (infer-completion Γ e_x c_x)
   (add-φ τ_x -- τφ_x)
   (where Γ_x #{type-env-add Γ x τφ_x})
   (infer-completion Γ_x e c)
   --- Let-λ
   (infer-completion Γ (let (x τ_x -- e_x) e) (let (x c_x) c))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check int c_0))
   (where c_1+ (check int c_1))
   ---
   (infer-completion Γ (+ e_0 e_1) (+ c_0+ c_1+))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check int c_0))
   (where c_1+ (check int c_1))
   ---
   (infer-completion Γ (/ e_0 e_1) (/ c_0+ c_1+))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check bool c_0))
   (where c_1+ (check bool c_1))
   ---
   (infer-completion Γ (and e_0 e_1) (and c_0+ c_1+))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check bool c_0))
   (where c_1+ (check bool c_1))
   ---
   (infer-completion Γ (or e_0 e_1) (or c_0+ c_1+))]
  [
   (infer-completion Γ e_0 c_0)
   (where c_0+ (check box c_0))
   ---
   (infer-completion Γ (unbox e_0) (unbox c_0+))]
  [
   (infer-completion Γ e_0 c_0)
   (infer-completion Γ e_1 c_1)
   (where c_0+ (check box c_0))
   ---
   (infer-completion Γ (set-box! e_0 e_1) (set-box! c_0 c_1))]
  [
   (infer-completion Γ e_0 c_0)
   ---
   (infer-completion Γ (int? e_0) (int? c_0))]
  [
   (infer-completion Γ e_0 c_0)
   ---
   (infer-completion Γ (bool? e_0) (bool? c_0))]
  [
   (infer-completion Γ e_0 c_0)
   ---
   (infer-completion Γ (proc? e_0) (proc? c_0))]
  [
   (infer-completion Γ e_0 c_0)
   ---
   (infer-completion Γ (box? e_0) (box? c_0))])

(define -->TAG
  (reduction-relation TAG
    #:domain A
    [-->
      (in-hole C ((fun f (x) c) v))
      (in-hole C (substitute (substitute c x v) f (fun f (x) c)))
      Beta]
    [-->
      (in-hole C (if v c_0 c_1))
      (in-hole C c_0)
      If-True
      (side-condition (not (eq? #f (term v))))]
    [-->
      (in-hole C (if #false c_0 c_1))
      (in-hole C c_1)
      If-False]
    [-->
      (in-hole C (let (x v) c))
      (in-hole C (substitute c x v))
      Let]
    [-->
      (in-hole C (δ v ...))
      RuntimeError
      δ-Error
      (where RuntimeError #{apply-primop δ v ...})]
    [-->
      (in-hole C (δ v ...))
      (in-hole C v_δ)
      δ-Ok
      (where v_δ #{apply-primop δ v ...})]
    [-->
      (in-hole C (check κ v))
      CheckError
      check-Error
      (judgment-holds (not-well-tagged v κ))]
    [-->
      (in-hole C (check κ v))
      (in-hole C v)
      check-Ok
      (judgment-holds (well-tagged v κ))]))

(define -->*
  (make--->* -->TAG))

;; "term precision" ⊑
(define-judgment-form TAG
  #:mode (type-ann<=? I I)
  #:contract (type-ann<=? e e)
  [
   ---
   (type-ann<=? e_0 e_1)]
)

;; "more checks"
;; This is TOO SIMPLE ... really need a simulation & compare traces
(define-judgment-form TAG
  #:mode (checks<=? I I)
  #:contract (checks<=? c c)
  [
   ---
   (checks<=? c_0 c_1)]
)

;; -----------------------------------------------------------------------------

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (flag++ I)
  #:contract (flag++ τφ)
  [
   ---
   (flag++ (_ ++ τφ ...))])

(define-judgment-form TAG
  #:mode (flag-- I)
  #:contract (flag-- τφ)
  [
   ---
   (flag-- (_ -- τφ ...))])

(define-judgment-form TAG
  #:mode (tag-of I O)
  #:contract (tag-of τ0 κ)
  [
   ---
   (tag-of Natural int)]
  [
   ---
   (tag-of Integer int)]
  [
   ---
   (tag-of Boolean bool)]
  [
   ---
   (tag-of (Box τ) box)]
  [
   ---
   (tag-of (→ τ_0 τ_1) proc)])

(define-judgment-form TAG
  #:mode (well-tagged I I)
  #:contract (well-tagged v κ)
  [
   ---
   (well-tagged integer int)]
  [
   ---
   (well-tagged boolean bool)]
  [
   ---
   (well-tagged (fun f (x) _) proc)]
  [
   ---
   (well-tagged (box _) box)])

(define-judgment-form TAG
  #:mode (not-well-tagged I I)
  #:contract (not-well-tagged v κ)
  [
   (side-condition ,(not (judgment-holds (well-tagged v κ))))
   ---
   (not-well-tagged v κ)])

(define-metafunction TAG
  apply-primop : δ v -> δ-cod
  [(apply-primop + integer_0 integer_1)
   ,(+ (term integer_0) (term integer_1))]
  [(apply-primop / integer_0 0)
   DivisionByZero]
  [(apply-primop / integer_0 integer_1)
   ,(inexact->exact (floor (/ (term integer_0) (term integer_1))))]
  [(apply-primop and boolean_0 boolean_1)
   ,(and (term boolean_0) (term boolean_1))]
  [(apply-primop or boolean_0 boolean_1)
   ,(or (term boolean_0) (term boolean_1))]
  [(apply-primop unbox (box v))
   v]
  [(apply-primop set-box! (box _) v)
   ,(raise-user-error 'WRONG)]
  [(apply-primop int? v)
   ,(integer? (term v))]
  [(apply-primop bool? v)
   ,(boolean? (term v))]
  [(apply-primop proc? v)
   ,(procedure? (term v))]
  [(apply-primop box? v)
   ,(box? (term v))]
  [(apply-primop δ v ...)
   ,(raise-user-error 'apply-primop "UNDEFINED ~a" (term (δ v ...)))])

(define-judgment-form TAG
  #:mode (erase-φ I O)
  #:contract (erase-φ τφ τ)
  [
   ---
   (erase-φ (any φ) any)]
  [
   (erase-φ τφ_0 τ_0)
   (erase-φ τφ_1 τ_1) ...
   ---
   (erase-φ (any φ τφ_0 τφ_1 ...) (any τ_0 τ_1 ...))])

(define-metafunction TAG
  erase-φ# : τφ -> τ
  [(erase-φ# τφ)
   τ
   (judgment-holds (erase-φ τφ τ))]
  [(erase-φ# τφ)
   ,(raise-user-error 'erase-φ "failed to erase ~a" (term τφ))])

(define-judgment-form TAG
  #:mode (add-φ I I O)
  #:contract (add-φ τ φ τφ)
  [
   ---
   (add-φ Natural φ (Natural φ))]
  [
   ---
   (add-φ Integer φ (Integer φ))]
  [
   ---
   (add-φ Boolean φ (Boolean φ))]
  [
   (add-φ τ φ τφ)
   ---
   (add-φ (Box τ) φ (Box φ τφ))]
  [
   (add-φ τ_dom φ τφ_dom)
   (add-φ τ_cod φ τφ_cod)
   ---
   (add-φ (→ τ_dom τ_cod) φ (→ φ τφ_dom τφ_cod))])

(define-judgment-form TAG
  #:mode (type=? I I)
  #:contract (type=? any any)
  [
   (erase-φ τφ_0 τ_0)
   (erase-φ τφ_1 τ_1)
   (type=? τ_0 τ_1)
   ---
   (type=? τφ_0 τφ_1)]
  [
   ---
   (type=? τ τ)])

(define-judgment-form TAG
  #:mode (tag=? I I)
  #:contract (tag=? any any)
  [
   (where κ #{->tag any_0})
   (where κ #{->tag any_1})
   ---
   (tag=? any_0 any_1)])

(define-metafunction TAG
  ->tag : any -> κ
  [(->tag τφ)
   κ
   (judgment-holds (erase-φ τφ τ))
   (judgment-holds (tag-of τ κ))]
  [(->tag τ)
   κ
   (judgment-holds (tag-of τ κ))]
  [(->tag κ)
   κ])

(define-metafunction TAG
  type-env-add : Γ x τφ -> Γ
  [(type-env-add Γ x τφ)
   ,(cons (term (x τφ)) (term Γ))])

(module+ test
  (test-case "flag++"
    (check-judgment-holds*
     (flag++ (Integer ++))
     (flag++ (Boolean ++))
     (flag++ (→ ++ (Integer ++) (Boolean --)))
     (flag++ (Box ++ (Integer --)))
    )
    (check-not-judgment-holds*
     (flag++ (Integer --))
     (flag++ (→ -- (Integer --) (Integer --)))
    )
  )

  (test-case "flag--"
    (check-judgment-holds*
     (flag-- (Integer --))
     (flag-- (→ -- (Integer --) (Integer --)))
    )
    (check-not-judgment-holds*
     (flag-- (Integer ++))
    )
  )

  (test-case "tag=?"
    (check-judgment-holds*
     (tag=? int int)
     (tag=? Integer int)
     (tag=? int Integer)
     (tag=? int Natural)
     (tag=? int (Natural ++))
     (tag=? int (Natural --))
     (tag=? proc (→ Natural Natural))
     (tag=? proc (→ (U Boolean Natural) (Box Integer)))
    )
  )

  (test-case "erase-φ"
    (check-judgment-holds*
     (erase-φ (Integer ++) Integer)
     (erase-φ (→ ++ (Integer ++) (Box -- (Integer --))) (→ Integer (Box Integer)))
    )
  )
)

