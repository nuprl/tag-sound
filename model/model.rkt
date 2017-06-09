#lang mf-apply racket/base

;; The point of this model is to study contract insertion & boundaries.
;; I think the cross-boundary soudnenss is going to work fine,
;;  with R < S < T
;;  and interesting types
;; but the model is here to find out, before diving into the weeds of:
;; - TR contract generation
;; - TR type-driven rewriting
;; - actual boundaries
;; (keep a TODO list of Racket things!)

;; Key points:
;; - S, T use same type checker
;;   - cool to see how, despite same typechecker, S is less trustworthy

;; Questions
;; - need "the racket type" ?
;; - how to polymorphic functions? should not be hard but please get right
;;   also application thereof
;; - why are let rules so similar?

;; ---

;; - evaluate with context-aware CEK machine
;; - prove "soundness" for closed programs
;; - prove absence of certain errors in certain contexts

;; After CEK machine is good,
;;  note that its not practical do implement this way,
;;  you really have a "colorbind" CEK machine
;;  that you compile the other languages to.
;; No problemo, define translations and show machine equivalence.
;; Should be easy right ha ha ha.

;; PROPERTIES
;; - type soundness for closed T programs
;; - tag soundness for closed S programs
;; - safety for closed R programs
;; - bounds on where certain errors can occur
;;   T can error for bad R or bad S (eventually find witness of bad input)
;;   S can error for bad R or bad S (ditto, but based on tag checks so maybe different? yes different)
;;   R can error anywhere, might just be wrong like `(+ 1 "two")`
;; - simulation between interpreted code and colorbind-compiled code

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit-abbrevs rackunit
           (for-syntax racket/base racket/syntax syntax/parse syntax/srcloc))

  (define-syntax (check-mf-apply* stx)
    (syntax-parse stx
     [(_ (~optional (~seq #:is-equal? ?eq:expr) #:defaults ([?eq #'#f])) [?e0 ?e1] ...)
      (quasisyntax/loc stx
        (let ([eq (or ?eq equal?)])
          #,@(for/list ([kv (in-list (syntax-e #'((?e0 ?e1) ...)))])
               (define e0 (car (syntax-e kv)))
               (define e1 (cadr (syntax-e kv)))
               (quasisyntax/loc e0
                 (with-check-info* (list (make-check-location '#,(build-source-location-list e0)))
                   (λ () (check eq (term #,e0) (term #,e1))))))))]))
)

;; =============================================================================

(define-language RST
  (e ::= x integer (λ (x) e) (unbox e) (set-box! e e) (+ e e) (e e) (box e) (if e e e) (let ((L x e)) e) (letrec ((L x e)) e) (:: e σ))
  (v ::= integer (λ (x) e) (box v))
  (c ::= (CLOSURE e γ))
  (σ ::= (∀ (α) σ) τ)
  (τ ::= (U k τ) (μ (α) τ) α k)
  (k ::= Integer (→ τ τ) (Boxof τ))
  (P ::= (L e))
  (L ::= R S T)
  (γ ::= ((L x v) ...))
  (Γ ::= ((L x σ) ...))
  (x* ::= (x ...))
  (α* ::= (α ...))
  (x α ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (∀ (α) σ #:refers-to α)
  (μ (α) τ #:refers-to α)
  (λ (x) e #:refers-to x)
  (let ((x e_0)) e #:refers-to x)
  (letrec ((x e_0 #:refers-to x)) e #:refers-to x)
)

(define (α=? e0 e1)
  (alpha-equivalent? RST e0 e1))

(module+ test
  (define-syntax (define-predicate* stx)
    (syntax-parse stx
     [(_ [x*:id ...])
      #:with (x?* ...) (for/list ([x (in-list (syntax-e #'(x* ...)))]) (format-id stx "~a?" (syntax-e x)))
      (syntax/loc stx (begin (define x?* (redex-match? RST x*)) ...))]))

  (define-predicate* [e v c σ τ k L γ Γ])

  (test-case "e"
    (check-pred e? (term x))
    (check-pred e? (term 4))
    (check-pred e? (term (:: 4 Integer)))
    (check-pred e? (term (:: 4 (Boxof Integer))))
    (check-pred e? (term (let ((R x 4)) (+ x 1)))))

  (test-case "τ"
    (check-pred τ? (term Integer)))

  (test-case "σ"
    (check-pred σ? (term Integer)))

  (test-case "Γ"
    (check-pred Γ? (term ((T x Integer))))
    (check-pred Γ? (term ((S x Integer))))
    (check-pred Γ? (term ((R x Integer)))))
)

;; -----------------------------------------------------------------------------
;; --- grammar
;; TODO
;; - type have discriminative unions
;; - check σ in the right places?
;; - well-formed type variables
;; - closed

(define-judgment-form RST
  #:mode (well-formed I I)
  #:contract (well-formed L e)
  [
   (closed e)
   ---
   (well-formed R e)]
  [
   (closed e)
   (well-formed-T e)
   ---
   (well-formed S e)]
  [
   (closed e)
   (well-formed-T e)
   ---
   (well-formed T e)])

(define-judgment-form RST
  #:mode (well-formed-T I)
  #:contract (well-formed-T e)
  [
   --- Var
   (well-formed-T x)]
  [
   --- Integer
   (well-formed-T integer)]
  [
   (well-formed-T e)
   (well-formed-type τ)
   --- Lambda
   (well-formed-T (:: (λ (x) e) τ))]
  [
   (well-formed-T e)
   --- Unbox
   (well-formed-T (unbox e))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- Set
   (well-formed-T (set-box! e_0 e_1))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- +
   (well-formed-T (+ e_0 e_1))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   --- App
   (well-formed-T (e_0 e_1))]
  [
   (well-formed-T e)
   (well-formed-type τ)
   --- Box
   (well-formed-T (:: (box e) τ))]
  [
   (well-formed-T e_0)
   (well-formed-T e_1)
   (well-formed-T e_2)
   --- If
   (well-formed-T (if e_0 e_1 e_2))]
  [
   (well-formed L e_0)
   (well-formed-T e_1)
   --- Let
   (well-formed-T (let ((L x e_0)) e_1))]
  [
   (well-formed L e_0)
   (well-formed-T e_1)
   --- Letrec
   (well-formed-T (letrec ((L x e_0)) e_1))])

(define-judgment-form RST
  #:mode (well-formed-type I)
  #:contract (well-formed-type σ)
  [
   ;; TODO
   ;; - no f
   ---
   (well-formed-type σ)])

(define-judgment-form RST
  #:mode (closed I)
  #:contract (closed any)
  [
   (free-variables any ())
   ---
   (closed any)])

(define-judgment-form RST
  #:mode (free-variables I O)
  #:contract (free-variables any x*)
  [
   ;; TODO
   ---
   (free-variables any ())])

;; -----------------------------------------------------------------------------
;; --- utils

(define-metafunction RST
  type-normalize : τ -> τ
  [(type-normalize τ)
   ;; placeholder implementation
   τ])

(define-metafunction RST
  τ=? : τ τ -> boolean
  [(τ=? τ_0 τ_1)
   ,(α=? (term τ_0+) (term τ_1+))
   (where τ_0+ (type-normalize τ_0))
   (where τ_1+ (type-normalize τ_1))])

;; (type-equal? τ τ)
(define-judgment-form RST
  #:mode (type-equal? I I)
  #:contract (type-equal? τ τ)
  [
   (side-condition (τ=? τ_0 τ_1))
   ---
   (type-equal? τ_0 τ_1)])

(define-metafunction RST
  unionize : τ τ -> τ
  [(unionize τ_0 τ_1)
   τ_0])

;; (type-env-set Γ L x e)
;; If term `e` from language `L` is type-annotated with τ, bind `(x τ)` in `Γ`
;; else return `Γ`
(define-metafunction RST
  type-env-set : Γ L x e -> Γ
  [(type-env-set Γ L x (:: e σ))
   ,(cons (term (L x σ)) (term Γ))]
  [(type-env-set Γ L x e)
   Γ])

(define-metafunction RST
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([lxσ (in-list (term Γ))]
                #:when (eq? (term x) (cadr lxσ)))
      (caddr lxσ))])

(module+ test
  ;; TODO
  (test-case "τ=?"

  )

  (test-case "normalize"
  )

  (test-case "unionize"
  )

  (test-case "type-env-set"
    (check-mf-apply*
     [(type-env-set () T x (:: 4 Integer))
      ((T x Integer))]
     [(type-env-set () R x (:: 4 Integer))
      ((R x Integer))]
     [(type-env-set () R x (:: 4 (Boxof Integer)))
      ((R x (Boxof Integer)))]
    )
  )

  (test-case "type-env-ref"
    (check-mf-apply*
     [(type-env-ref () x)
      #f]
     [(type-env-ref ((R x Integer)) x)
      Integer]
     [(type-env-ref ((R x (Boxof Integer))) x)
      (Boxof Integer)]
     [(type-env-ref ((S x Integer)) x)
      Integer]
     [(type-env-ref ((R x Integer) (R y Integer)) y)
      Integer]
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- type checking

(define-judgment-form RST
  #:mode (well-typed I I)
  #:contract (well-typed Γ P)
  [
   (R-typed Γ e)
   ---
   (well-typed Γ (R e))]
  [
   (T-typed Γ e σ)
   ---
   (well-typed Γ (S e))]
  [
   (T-typed Γ e σ)
   ---
   (well-typed Γ (T e))])

;; (R-typed Γ e)
;; recur through `e` and ensure that all typed components are well-typed
(define-judgment-form RST
  #:mode (R-typed I I)
  #:contract (R-typed Γ e)
  [
   --- Var
   (R-typed Γ x)]
  [
   --- Integer
   (R-typed Γ integer)]
  [
   (R-typed Γ e)
   --- Lambda
   (R-typed Γ (λ (x) e))]
  [
   (R-typed Γ e)
   --- Unbox
   (R-typed Γ (unbox e))]
  [
   (R-typed Γ e_0)
   (R-typed Γ e_1)
   --- Set-Box
   (R-typed Γ (set-box! e_0 e_1))]
  [
   (R-typed Γ e_0)
   (R-typed Γ e_1)
   --- +
   (R-typed Γ (+ e_0 e_1))]
  [
   (R-typed Γ e_0)
   (R-typed Γ e_1)
   --- App
   (R-typed Γ (e_0 e_1))]
  [
   (R-typed Γ e_0)
   --- Box
   (R-typed Γ (box e_0))]
  [
   (R-typed Γ e_0)
   (R-typed Γ e_1)
   (R-typed Γ e_2)
   --- If
   (R-typed Γ (if e_0 e_1 e_2))]
  [
   (well-typed Γ (L e_0))
   (where Γ_x #{type-env-set Γ L x e_0})
   (R-typed Γ_x e_1)
   --- Let
   (R-typed Γ (let ((L x e_0)) e_1))]
  [
   (where Γ_x #{type-env-set Γ L x e_0})
   (well-typed Γ_x (L e_0))
   (R-typed Γ_x e_1)
   --- Letrec
   (R-typed Γ (letrec ((L x e_0)) e_1))]
  [
   (R-typed Γ e)
   --- Ann
   (R-typed Γ (:: e σ))]
)

(define-judgment-form RST
  #:mode (T-typed I I O)
  #:contract (T-typed Γ e σ)
  [
   (where σ #{type-env-ref Γ x})
   --- Var
   (T-typed Γ x σ)]
  [
   --- Integer
   (T-typed Γ integer Integer)]
  [
   (where Γ_x #{type-env-set Γ T x τ_0}) ;; TODO sometimes use S ?
   (T-typed Γ_x e τ_2)
   (type-equal? τ_1 τ_2)
   --- Lambda
   (T-typed Γ (:: (λ (x) e) (→ τ_0 τ_1)) (→ τ_0 τ_1))]
  [
   (side-condition ,(raise-user-error 'T-typed "found un-annotated function, please wrap all (λ (x) e) as (:: (λ (x) e) τ) in ~a" (term (λ (x) e))))
   --- LambdaError
   (T-typed Γ (λ (x) e) Integer)]
  [
   (T-typed Γ e (Boxof τ))
   --- Unbox
   (T-typed Γ (unbox e) τ)]
  [
   (T-typed Γ e_0 (Boxof τ_0))
   (T-typed Γ e_1 τ_1)
   (type-equal? τ_0 τ_1)
   --- SetBox
   (T-typed Γ (set-box! e_0 e_1) (Boxof τ_0))]
  [
   (T-typed Γ e_0 τ_0)
   (T-typed Γ e_1 τ_1)
   (type-equal? τ_0 Integer)
   (type-equal? τ_1 Integer)
   --- +
   (T-typed Γ (+ e_0 e_1) Integer)]
  [
   (T-typed Γ e_0 (→ τ_dom τ_cod))
   (T-typed Γ e_1 τ_1)
   (type-equal? τ_1 τ_dom)
   --- App
   (T-typed Γ (e_0 e_1) τ_cod)]
  [
   (T-typed Γ e_0 τ_0)
   (T-typed Γ e_1 τ_1)
   (T-typed Γ e_2 τ_2)
   (where τ #{unionize τ_1 τ_2})
   --- If
   (T-typed Γ (if e_0 e_1 e_2) τ)]
  [
   (well-typed Γ (L e_0))
   (where Γ_x #{type-env-set Γ L x e_0})
   (T-typed Γ_x e_1 τ_1)
   --- Let
   (T-typed Γ (let ((L x e_0)) e_1) τ_1)]
  [
   (where Γ_x #{type-env-set Γ L x e_0})
   (well-typed Γ_x (L e_0))
   (T-typed Γ_x e_1 τ_1)
   --- Letrec
   (T-typed Γ (letrec ((L x e_0)) e_1) τ_1)]
  [
   (T-typed Γ e τ_e)
   (type-equal? τ_e τ)
   --- Ann
   (T-typed Γ (:: e τ) τ)]
)

;; uhm what abouy environemnts?
(define-metafunction RST
  typecheck : P -> boolean
  [(typecheck P)
   (judgment-holds (well-typed () P))])

;; -----------------------------------------------------------------------------
;; --- evaluation


;; -----------------------------------------------------------------------------
;; --- (colorblind) compiler
;; - translate R S T terms all to R
;; - but the S T terms have proper checks,
;; - via contracts and type-directed defense

