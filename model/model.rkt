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
;; - arity of primops

;; ---

;; - evaluate with context-aware CESK machine
;; - prove "soundness" for closed programs
;; - prove absence of certain errors in certain contexts

;; After CESK machine is good,
;;  note that its not practical do implement this way,
;;  you really have a "colorbind" CEK machine
;;  that you compile the other languages to.
;; - IN OTHER WORDS no types at runtime
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

(define-language RST
;; terms, programs, languages, typing
  (e ::= x integer (λ (x) e) (unbox e) (set-box! e e) (box e) (aop e e) (e e) (if e e e) (let ((L x e)) e) (letrec ((L x e)) e) (:: e σ))
  (op ::= set-box! box aop)
  (aop ::= + = - *)
  (L ::= R S T)
  (σ ::= (∀ (α) σ) τ)
  (τ ::= (U k τ) (μ (α) τ) α k)
  (k ::= Integer (→ τ τ) (Boxof τ))
  (Γ ::= ((x L σ) ...))
  (P ::= (L e))
;; values, machine states
  (v ::= integer c (box v))
  (c ::= (CLOSURE e Γ ρ)) ;; WARNING Γ and ρ must have same domain
  (Σ ::= (STATE P Γ ρ Store Kont)) ;; WARNING Γ and ρ have same domain
  (ρ ::= ((x addr) ...)) ;; runtime environment
  (Store ::= ((addr L v τ) ...))
  (K ::= HALT (IF e e) (LET L x e)
         (APP (addr ...) (e ...)) (OP op (addr ...) (e ...))
         (CHECK τ) (TAG τ))
  (Kont ::= (K ...))
;; sequences, variables, misc
  (Σ* ::= (Σ ...))
  (k* ::= (k ...))
  (x* ::= (x ...))
  (α* ::= (α ...))
  (x α addr ::= variable-not-otherwise-mentioned)
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
  (*term-equal?* α=?)

  (define-syntax (define-predicate* stx)
    (syntax-parse stx
     [(_ [x*:id ...])
      #:with (x?* ...) (for/list ([x (in-list (syntax-e #'(x* ...)))]) (format-id stx "~a?" (syntax-e x)))
      (syntax/loc stx (begin (define x?* (redex-match? RST x*)) ...))]))

  (define-predicate* [e v c σ τ k L ρ Γ Σ])

  (test-case "e"
    (check-pred e? (term x))
    (check-pred e? (term 4))
    (check-pred e? (term (:: 4 Integer)))
    (check-pred e? (term (:: 4 (Boxof Integer))))
    (check-pred e? (term (let ((R x 4)) (+ x 1))))
    (check-pred e? (term (:: (λ (x) 3) (→ (→ Integer Integer) Integer)))))

  (test-case "τ"
    (check-pred τ? (term Integer))
    (check-pred τ? (term (→ (→ Integer Integer) Integer))))

  (test-case "σ"
    (check-pred σ? (term Integer)))

  (test-case "Γ"
    (check-pred Γ? (term ((x T Integer))))
    (check-pred Γ? (term ((x S Integer))))
    (check-pred Γ? (term ((x R Integer)))))
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
   --- aop
   (well-formed-T (aop e_0 e_1))]
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

;; TODO
;; - remove unused α
(define-metafunction RST
  type-normalize : τ -> τ
  [(type-normalize (U k τ))
   #{union-add k τ_+}
   (where τ_+ #{type-normalize τ})]
  [(type-normalize τ)
   ;; placeholder implementation
   τ])

(define-metafunction RST
  τ=? : τ τ -> boolean
  [(τ=? τ_0 τ_1)
   (τ=?-aux (type-normalize τ_0) (type-normalize τ_1))])

;; Decide if normalized types are equal
(define-metafunction RST
  τ=?-aux : τ τ -> boolean
  [(τ=?-aux (μ (α) τ_0) τ_1)
   (τ=?-aux #{unfold-rec (μ (α) τ_0)} τ_1)
   (judgment-holds (tag-equal? τ_0 τ_1))]
  [(τ=?-aux τ_0 (μ (α) τ_1))
   (τ=?-aux τ_0 #{unfold-rec (μ (α) τ_1)})
   (judgment-holds (tag-equal? τ_0 τ_1))]
  [(τ=?-aux τ_0 τ_1)
   ,(α=? (term τ_0) (term τ_1))])

(define-metafunction RST
  unfold-rec : (μ (α) τ) -> τ
  [(unfold-rec (μ (α) τ))
   (substitute τ α (μ (α) τ))])

(define-judgment-form RST
  #:mode (tag-equal? I I)
  #:contract (tag-equal? τ τ)
  [
   ---
   (tag-equal? Integer Integer)]
  [
   ---
   (tag-equal? (Boxof τ_0) (Boxof τ_1))]
  [
   ---
   (tag-equal? (→ τ_0 τ_1) (→ τ_2 τ_3))]
  [
   (tag-equal? k_0 k_1)
   (tag-equal? τ_0 τ_1)
   ---
   (tag-equal? (U k_0 τ_0) (U k_1 τ_1))]
  [
   (tag-equal? τ_0 τ_1)
   ---
   (tag-equal? (μ (α_0) τ_0) (μ (α_1) τ_1))])

;; (type-equal? τ τ)
(define-judgment-form RST
  #:mode (type-equal? I I)
  #:contract (type-equal? τ τ)
  [
   (side-condition (τ=? τ_0 τ_1))
   ---
   (type-equal? τ_0 τ_1)])

(define-judgment-form RST
  #:mode (subtype? I I)
  #:contract (subtype? τ τ)
  [
   (type-equal? τ_0 τ_1)
   --- Id
   (subtype? τ_0 τ_1)])

(define-metafunction RST
  unionize : τ τ -> τ
  [(unionize k_0 k_1)
   (unionize-k k_0 k_1)]
  [(unionize α_0 α_1)
   (U α_pre α_post)
   (where (α_pre α_post) (sort-α (α_0 α_1)))]
  [(unionize (U k_0 τ_0) τ_1)
   (unionize τ_0 #{union-add k_0 τ_1})]
  [(unionize k (μ (α) τ))
   (μ (α) #{unionize k τ})] ;; TODO freshen? I think binding-forms takes care of it
  [(unionize (μ (α) τ) k)
   (μ (α) #{unionize k τ})]
  [(unionize τ k)
   (U k τ)]
  [(unionize k τ)
   (U k τ)])

(define-metafunction RST
  union-add : k τ -> τ
  [(union-add k_0 (U k_0 τ_1))
   (U k_0 τ_1)]
  [(union-add k_0 (U k_1 τ_1))
   (U k_0 (U k_1 τ_1))
   (side-condition (term (k<=? k_0 k_1)))]
  [(union-add k_0 (U k_1 τ_1))
   (U k_1 #{union-add k_0 τ_1})]
  [(union-add k_0 k_1)
   (unionize-k k_0 k_1)]
  [(union-add k_0 τ)
   (U k_0 τ)])

(define-metafunction RST
  unionize-k : k k -> τ
  [(unionize-k Integer Integer)
   Integer]
  [(unionize-k (→ τ_0 τ_1) (→ τ_2 τ_3))
   ,(raise-user-error 'unionize "cannot union arrow types ~a" (term ((→ τ_0 τ_1) (→ τ_2 τ_3))))]
  [(unionize-k (Boxof τ_0) (Boxof τ_1))
   ,(raise-user-error 'unionize "cannot union box types ~a" (term ((Boxof τ_0) (Boxof τ_1))))]
  [(unionize-k k_0 k_1)
   (U k_pre k_post)
   (where (k_pre k_post) (sort-k (k_0 k_1)))])

(define-metafunction RST
  sort-α : α* -> α*
  [(sort-α α*)
   ,(sort (term α*) symbol<?)])

(define-metafunction RST
  sort-k : (k k) -> (k k)
  [(sort-k (k_0 k_1))
   (k_0 k_1)
   (side-condition (term (k<=? k_0 k_1)))]
  [(sort-k (k_0 k_1))
   (k_1 k_0)])

(define-metafunction RST
  k<=? : k k -> boolean
  [(k<=? k_0 k_1)
   ,(symbol<? (term #{constructor-of k_0}) (term #{constructor-of k_1}))])

(define-metafunction RST
  constructor-of : k -> any
  [(constructor-of Integer)
   Integer]
  [(constructor-of (→ τ_0 τ_1))
   →]
  [(constructor-of (Boxof τ))
   Boxof])

(define-judgment-form RST
  #:mode (un-annotated I)
  #:contract (un-annotated e)
  [
   (side-condition ,(not (judgment-holds (annotated e))))
   ---
   (un-annotated e)])

(define-judgment-form RST
  #:mode (annotated I)
  #:contract (annotated e)
  [
   ---
   (annotated (:: e τ))])

;; (type-env-set Γ L x e)
;; If term `e` from language `L` is type-annotated with τ, bind `(x τ)` in `Γ`
;; else return `Γ`
(define-metafunction RST
  type-env-set : Γ L x e -> Γ
  [(type-env-set Γ L x (:: e σ))
   ,(cons (term (x L σ)) (term Γ))]
  [(type-env-set Γ L x e)
   Γ])

(define-metafunction RST
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(let ([xlσ (assoc (term x) (term Γ))])
      (and xlσ (caddr xlσ)))])

(define-metafunction RST
  runtime-env-ref : ρ x -> any
  [(runtime-env-ref ρ x)
   ,(let ([kv (assoc (term x) (term ρ))])
      (and kv (cadr kv)))])

(define-metafunction RST
  store-ref : Store addr -> any
  [(store-ref Store addr)
   ,(let ([kv (assoc (term x) (term ρ))])
      (and kv (cdr kv)))])

(module+ test
  (test-case "τ=?"
    (check-mf-apply*
     [(τ=? Integer Integer)
      #true]
     [(τ=? Integer (Boxof Integer))
      #false]
     [(τ=? (→ Integer Integer) (→ Integer Integer))
      #true]
     [(τ=? (U Integer (Boxof Integer)) (U (Boxof Integer) Integer))
      #true]
     [(τ=? (U (Boxof (μ (α1) (U (Boxof α1) Integer))) Integer)
           (μ (α0) (U (Boxof α0) Integer)))
      #true]
    )
  )

  (test-case "normalize"
    (check-mf-apply*
     [(type-normalize Integer)
      Integer]
    )
  )

  (test-case "unionize"
    (check-mf-apply*
     [(unionize Integer Integer)
      Integer]
     [(unionize (Boxof Integer) Integer)
      (U (Boxof Integer) Integer)]
     [(unionize Integer (Boxof Integer))
      (U (Boxof Integer) Integer)]
     [(unionize (U Integer (→ Integer Integer)) (U (Boxof Integer) Integer))
      (U (→ Integer Integer) (U (Boxof Integer) Integer))]
    )
  )

  (test-case "type-env-set"
    (check-mf-apply*
     [(type-env-set () T x (:: 4 Integer))
      ((x T Integer))]
     [(type-env-set () R x (:: 4 Integer))
      ((x R Integer))]
     [(type-env-set () R x (:: 4 (Boxof Integer)))
      ((x R (Boxof Integer)))]
    )
  )

  (test-case "type-env-ref"
    (check-mf-apply*
     [(type-env-ref () x)
      #f]
     [(type-env-ref ((x R Integer)) x)
      Integer]
     [(type-env-ref ((x R (Boxof Integer))) x)
      (Boxof Integer)]
     [(type-env-ref ((x S Integer)) x)
      Integer]
     [(type-env-ref ((x R Integer) (y R Integer)) y)
      Integer]
    )
  )

  (test-case "runtime-env-ref"
    (check-mf-apply*
     [(runtime-env-ref () x)
      #false]
     [(runtime-env-ref ((x y)) x)
      y]
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
   --- aop
   (R-typed Γ (aop e_0 e_1))]
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
   (where #f #{type-env-ref Γ x})
   (side-condition ,(raise-user-error 'T-typed "unbound variable ~a in type environment ~a (may need to annotate a let/letrec)" (term x) (term Γ)))
   --- VarError
   (T-typed Γ x Integer)]
  [
   --- Integer
   (T-typed Γ integer Integer)]
  [
   (where Γ_x #{type-env-set Γ T x (:: x τ_0)}) ;; TODO sometimes use S ?
   (T-typed Γ_x e τ_2)
   (subtype? τ_2 τ_1)
   --- Lambda
   (T-typed Γ (:: (λ (x) e) (→ τ_0 τ_1)) (→ τ_0 τ_1))]
  [
   (side-condition ,(raise-user-error 'T-typed "found un-annotated function in ~a" (term (λ (x) e))))
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
   --- aop
   (T-typed Γ (aop e_0 e_1) Integer)]
  [
   (T-typed Γ e_0 (→ τ_dom τ_cod))
   (T-typed Γ e_1 τ_1)
   (type-equal? τ_1 τ_dom)
   --- App
   (T-typed Γ (e_0 e_1) τ_cod)]
  [
   (T-typed Γ e_0 τ_0)
   (subtype? τ_0 τ)
   --- Box
   (T-typed Γ (:: (box e_0) (Boxof τ)) (Boxof τ))]
  [
   (side-condition ,(raise-user-error 'T-typed "un-annotated box in ~a" (term (box e))))
   --- BoxError
   (T-typed Γ (box e) Integer)]
  [
   (T-typed Γ e_0 τ_0)
   (T-typed Γ e_1 τ_1)
   (T-typed Γ e_2 τ_2)
   (where τ #{unionize τ_1 τ_2})
   --- If
   (T-typed Γ (if e_0 e_1 e_2) τ)]
  [
   (well-typed Γ (L (:: e_0 τ_0)))
   (where Γ_x #{type-env-set Γ L x (:: e_0 τ_0)})
   (T-typed Γ_x e_1 τ_1)
   --- Let
   (T-typed Γ (let ((L x (:: e_0 τ_0))) e_1) τ_1)]
  [
   (un-annotated e_0)
   (side-condition ,(raise-user-error 'T-typed "un-annotated let expression ~a" (term (let ((L x e_0)) e_1))))
   --- LetError
   (T-typed Γ (let ((L x e_0)) e_1) Integer)]
  [
   (where Γ_x #{type-env-set Γ L x (:: e_0 τ_0)})
   (well-typed Γ_x (L (:: e_0 τ_0)))
   (T-typed Γ_x e_1 τ_1)
   --- Letrec
   (T-typed Γ (letrec ((L x (:: e_0 τ_0))) e_1) τ_1)]
  [
   (un-annotated e_0)
   (side-condition ,(raise-user-error 'T-typed "un-annotated letrec expression ~a" (term (letrec ((L x e_0)) e_1))))
   --- LetRecError
   (T-typed Γ (letrec ((L x e_0)) e_1) Integer)]
  [
   (side-condition ,(not (and (pair? (term e)) (memq (car (term e)) '(box λ)))))
   (T-typed Γ e τ_e)
   (type-equal? τ_e τ)
   --- Ann
   (T-typed Γ (:: e τ) τ)]
)

(define-metafunction RST
  T-typecheck : e -> σ
  [(T-typecheck e)
   τ
   (judgment-holds (T-typed () e τ))]
  [(T-typecheck e)
   ,(raise-user-error 'T-typecheck "failed to type ~a" (term e))])

(define-metafunction RST
  typecheck : P -> boolean
  [(typecheck P)
   #true
   (judgment-holds (well-typed () P))]
  [(typecheck P)
   #false])

(module+ test
  (test-case "typecheck R-only"
    (check-mf-apply*
     [(typecheck (R 4))
      #true]
     [(typecheck (R (λ (x) 3)))
      #true]
     [(typecheck (R (+ 1 2)))
      #true]
     [(typecheck (R (+ 1 (box 3))))
      #true]
     [(typecheck (R (if 1 2 3)))
      #true]
     [(typecheck (R (box (λ (x) (+ 2 2)))))
      #true]
     [(typecheck (R (set-box! (box 2) (+ 1 1))))
      #true]
     [(typecheck (R ((λ (x) (set-box! x 0)) (box 42))))
      #true]
     [(typecheck (R ((λ (x) (set-box! 0 x)) (box 42))))
      #true]
     [(typecheck (R (let ((R x 4)) x)))
      #true]
     [(typecheck (R (let ((R x 4)) (x x))))
      #true]
     [(typecheck (R (letrec ((R x 4)) x)))
      #true]
     [(typecheck (R (letrec ((R x (box 3))) (+ x x))))
      #true]
    )
  )

  (test-case "typecheck S-only"
    (check-mf-apply*
     [(typecheck (S 4))
      #true]
     [(typecheck (S (:: (λ (x) 3) (→ (→ Integer Integer) Integer))))
      #true]
     [(typecheck (S (+ 1 2)))
      #true]
     [(typecheck (S (+ 1 (:: (box 3) (Boxof Integer)))))
      #false]
     [(typecheck (S (if 1 2 3)))
      #true]
     [(typecheck (S (:: (box (:: (λ (x) (+ 2 2)) (→ Integer Integer))) (Boxof (→ Integer Integer)))))
      #true]
     [(typecheck (S (set-box! (:: (box 2) (Boxof Integer)) (+ 1 1))))
      #true]
     [(typecheck (S (set-box! (:: (box 2) (Boxof Integer)) (:: (box 1) (Boxof Integer)))))
      #false]
     [(typecheck (S ((:: (λ (x) (set-box! x 0)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #true]
     [(typecheck (S ((:: (λ (x) (set-box! 0 x)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #false]
     [(typecheck (S (let ((S x (:: 4 Integer))) x)))
      #true]
     [(typecheck (S (let ((S x (:: 4 Integer))) (x x))))
      #false]
     [(typecheck (S (letrec ((S x (:: 4 Integer))) x)))
      #true]
     [(typecheck (S (letrec ((S x (:: (box 3) (Boxof Integer)))) x)))
      #true]
     [(typecheck (S (letrec ((S x (:: (box 3) (Boxof Integer)))) (+ x x))))
      #false]
    )
  )

  (test-case "typecheck T-only"
    (check-mf-apply*
     [(typecheck (T 4))
      #true]
     [(typecheck (T (:: (λ (x) 3) (→ Integer Integer))))
      #true]
     [(typecheck (T (+ 1 2)))
      #true]
     [(typecheck (T (+ 1 (:: (box 3) (Boxof Integer)))))
      #false]
     [(typecheck (T (if 1 2 3)))
      #true]
     [(typecheck (T (:: (box (:: (λ (x) (+ 2 2)) (→ Integer Integer))) (Boxof (→ Integer Integer)))))
      #true]
     [(typecheck (T (:: (box 2) Integer)))
      #false]
     [(typecheck (T (set-box! (:: (box 2) (Boxof Integer)) (+ 1 1))))
      #true]
     [(typecheck (T ((:: (λ (x) (set-box! x 0)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #true]
     [(typecheck (T ((:: (λ (x) (set-box! 0 x)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #false]
     [(typecheck (T (let ((T x (:: 4 Integer))) x)))
      #true]
     [(typecheck (T (let ((T x (:: 4 Integer))) (x x))))
      #false]
     [(typecheck (T (letrec ((T x (:: 4 Integer))) x)))
      #true]
     [(typecheck (T (letrec ((T x (:: (box 3) (Boxof Integer)))) x)))
      #true]
     [(typecheck (T (letrec ((T x (:: (box 3) (Boxof Integer)))) (+ x x))))
      #false]
    )
  )

  (test-case "missing-annotation"
    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (S (box 3)))))))

    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (S (λ (x) 3)))))))

    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (T (let ((R f (λ (x) (+ x 1)))) f)))))))
  )

  (test-case "typecheck T"
    (check-mf-apply*
     [(typecheck (T (:: (λ (x) x) (→ (U (Boxof Integer) Integer) (U (Boxof Integer) Integer)))))
      #true]
     [(typecheck (T (:: (λ (x) (if (= x 0) x (:: (box x) (Boxof Integer)))) (→ Integer (U (Boxof Integer) Integer)))))
      #true]
     [(typecheck (T (:: (λ (x) (+ x 1)) (→ (U (Boxof Integer) Integer) Integer))))
      #false]
     [(typecheck (T (letrec ((T fact (:: (λ (n) (if (= n 1) 1 (* n (fact (- n 1))))) (→ Integer Integer)))) (fact 4))))
      #true]
     [(typecheck (T (letrec ((T fact (:: (λ (n) (if (= n 1) (:: (box 1) (Boxof Integer)) (* n (fact (- n 1))))) (→ Integer Integer)))) (fact 4))))
      #false]
     [(typecheck (T
       (letrec ((T deep (:: (λ (x) (if (= 0 x) x (:: (box (deep (- x 1)))
                                                     (Boxof (μ (α1) (U (Boxof α1) Integer))))))
                            (→ Integer (μ (α0) (U (Boxof α0) Integer))))))
         (deep 3))))
      #true]
    )
  )

  (test-case "T-typecheck"
    (check-mf-apply*
     [(T-typecheck
       (letrec ((T deep (:: (λ (x) (if (= 0 x) x (:: (box (deep (- x 1)))
                                                     (Boxof (μ (α1) (U (Boxof α1) Integer))))))
                            (→ Integer (μ (α0) (U (Boxof α0) Integer))))))
         (deep 3)))
      (μ (α2) (U (Boxof α2) Integer))]))

  (test-case "mixed-lang I"

    (check-mf-apply*
     [(typecheck (T (let ((R f (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f 1))))
      #true]
     [(typecheck (T (let ((R f (:: (λ (x) (+ x 1)) (→ (Boxof Integer) (Boxof Integer))))) (f (:: (box 1) (Boxof Integer))))))
      #true]
     [(typecheck (S (let ((R f (:: (λ (x) (+ x 1)) (→ (Boxof Integer) (Boxof Integer))))) (f (:: (box 1) (Boxof Integer))))))
      #true]
     [(typecheck (R (let ((S f (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f 55))))
      #true]
     [(typecheck (R (let ((T f (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f (box 4)))))
      #true]
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- (discriminating,colorful,eidetic) evaluation

(define -->RST
  (reduction-relation RST
    #:domain Σ
    [-->
      Σ
      Σ
      (judgment-holds (final? Σ))]
))

(define -->RST*
  (make--->* -->RST))

(define-metafunction RST
  eval : P -> v
  [(eval P)
   (-->RST* #{init P})
   (side-condition
     (if (term #{typecheck P})
       #true
       (raise-user-error 'eval "typechecking failed" (term P))))])

(define-metafunction RST
  init : P -> Σ
  [(init (L e))
   (STATE (L e) () () () (HALT))])

(define-judgment-form RST
  #:mode (final? I)
  #:contract (final? Σ)
  [
   (address? #{state->expression Σ} Σ)
   (where HALT #{state->kont Σ})
   ---
   (final? Σ)])

(define-judgment-form RST
  #:mode (variable? I I)
  #:contract (variable? e Σ)
  [
   (where ρ #{state->runtime-env Σ})
   (side-condition ,(and (term #{runtime-env-ref ρ x}) #true))
   ---
   (variable? x Σ)])

(define-judgment-form RST
  #:mode (address? I I)
  #:contract (address? e Σ)
  [
   (where Store #{state->store Σ})
   (side-condition ,(and (term #{store-ref Store addr}) #true))
   ---
   (address? addr Σ)])

(define-metafunction RST
  state->program : Σ -> P
  [(state->program (STATE P Γ ρ Store Kont))
   P])

(define-metafunction RST
  state->language : Σ -> L
  [(state->language (STATE P Γ ρ Store Kont))
   #{program->language P}])

(define-metafunction RST
  state->expression : Σ -> e
  [(state->expression (STATE P Γ ρ Store Kont))
   #{program->expression P}])

(define-metafunction RST
  state->type-env : Σ -> Γ
  [(state->type-env (STATE P Γ ρ Store Kont))
   Γ])

(define-metafunction RST
  state->runtime-env : Σ -> ρ
  [(state->runtime-env (STATE P Γ ρ Store Kont))
   ρ])

(define-metafunction RST
  state->store : Σ -> Store
  [(state->store (STATE P Γ ρ Store Kont))
   Store])

(define-metafunction RST
  state->kont : Σ -> Kont
  [(state->kont (STATE P Γ ρ Store Kont))
   Kont])

(define-metafunction RST
  program->language : P -> L
  [(program->language (L e))
   L])

(define-metafunction RST
  program->expression : P -> e
  [(program->expression (L e))
   e])

;; -----------------------------------------------------------------------------
;; --- (colorblind) compiler
;; - translate R S T terms all to R
;; - but the S T terms have proper checks,
;; - via contracts and type-directed defense

