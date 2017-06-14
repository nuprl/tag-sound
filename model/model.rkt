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
;; - how to polymorphic functions? should not be hard but please get right
;;   also application thereof
;; - arity of primops

;; TODO
;; - more careful about UNDEF
;; - type have discriminative unions
;; - check σ in the right places?
;; - well-formed type variables
;; - closed
;; - remove unused α in `type-normalize`
;; - tautology-checking function

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
  (e ::= x boolean integer (λ (x) e) (unbox e) (set-box! e e) (box e) (aop e e) (e e) (if e e e) (let ((x L e)) e) (letrec ((x L e)) e) (:: e σ))
  (op ::= unbox set-box! aop)
  (aop ::= + = - *)
  (L ::= R S T)
  (L\T ::= R S)
  (L\R ::= S T)
  (?τ ::= σ TST)
  (σ ::= (∀ (α) σ) τ)
  (τ ::= (U k τ) (μ (α) τ) α k)
  (k ::= Boolean Integer (→ τ τ) (Boxof τ))
  (Γ ::= ((x L ?τ) ...))
  (P ::= (L e))
;; values, machine states
  (v ::= boolean integer c (box v))
  (?v ::= v UNDEF) ;; for letrec
  (c ::= (CLOSURE e Γ ρ)) ;; WARNING Γ and ρ must have same domain
  (Σ ::= (STATE L e Γ ρ Store Kont)) ;; WARNING Γ and ρ have same domain
  ;; TODO am currently not touching Γ, see what happens
  (ρ ::= ((x addr) ...)) ;; runtime environment
  (Store ::= ((addr L ?v ?τ) ...))
  (K ::= HALT (IF e e) (LET L x ?τ e) (LETREC L x ?τ e)
         (BOX ?τ) (APP addr* (e ...)) (OP op (addr ...) (e ...))
         (CHECK-TYPE τ) (CHECK-TAG τ))
  (Kont ::= (K ...))
;; sequences, variables, misc
  (Σ* ::= (Σ ...))
  (k* ::= (k ...))
  (addr* ::= (addr ...))
  (x* ::= (x ...))
  (α* ::= (α ...))
  (x α addr ::= variable-not-otherwise-mentioned)
#:binding-forms
  (∀ (α) σ #:refers-to α)
  (μ (α) τ #:refers-to α)
  (λ (x) e #:refers-to x)
  (let ((x L e_0)) e #:refers-to x)
  (letrec ((x L e_0 #:refers-to x)) e #:refers-to x)
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
    (check-pred e? (term 0))
    (check-pred e? (term -61))
    (check-pred e? (term #true))
    (check-pred e? (term #false))
    (check-pred e? (term (:: 4 Integer)))
    (check-pred e? (term (:: 4 (Boxof Integer))))
    (check-pred e? (term (let ((x R 4)) (+ x 1))))
    (check-pred e? (term (:: (λ (x) 3) (→ (→ Integer Integer) Integer)))))

  (test-case "τ"
    (check-pred τ? (term Integer))
    (check-pred τ? (term Boolean))
    (check-pred τ? (term (Boxof Boolean)))
    (check-pred τ? (term (Boxof (→ Integer Integer))))
    (check-pred τ? (term (→ (→ Integer Integer) Integer))))

  (test-case "σ"
    (check-pred σ? (term Integer)))

  (test-case "Γ"
    (check-pred Γ? (term ((x T Integer))))
    (check-pred Γ? (term ((x S Integer))))
    (check-pred Γ? (term ((x R Integer))))
    (check-pred Γ? (term ((x R TST)))))
)

;; -----------------------------------------------------------------------------
;; --- grammar

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
   --- Boolean
   (well-formed-T boolean)]
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
   (well-formed-T (let ((x L e_0)) e_1))]
  [
   (well-formed L e_0)
   (well-formed-T e_1)
   --- Letrec
   (well-formed-T (letrec ((x L e_0)) e_1))])

(define-judgment-form RST
  #:mode (well-formed-type I)
  #:contract (well-formed-type σ)
  [
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
   (tag-equal? Boolean Boolean)]
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
  [(unionize-k Boolean Boolean)
   Boolean]
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

;; aka, the "floor" relation in vss-popl-2017
(define-metafunction RST
  constructor-of : k -> any
  [(constructor-of Boolean)
   Boolean]
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
  type-env-set : Γ L x any -> Γ
  [(type-env-set Γ L x (:: e σ))
   ,(cons (term (x L σ)) (term Γ))]
  [(type-env-set Γ L x ?τ)
   ,(cons (term (x L ?τ)) (term Γ))]
  [(type-env-set Γ R x e)
   ,(cons (term (x R TST)) (term Γ))])

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
  runtime-env-set : ρ x addr -> ρ
  [(runtime-env-set ρ x addr)
   ,(cons (term (x addr)) (term ρ))])

(define-metafunction RST
  store-ref : Store addr -> any
  [(store-ref Store addr)
   ,(let ([kv (assoc (term x) (term ρ))])
      (and kv (cdr kv)))])

(define-metafunction RST
  store-ref-language : Store addr -> L
  [(store-ref-language Store addr)
   L
   (where (L v ?τ) #{store-ref Store addr})])

(define-metafunction RST
  store-ref-value : Store addr -> v
  [(store-ref-value Store addr)
   v
   (where (L ?v ?τ) #{store-ref Store addr})])

(define-metafunction RST
  store-ref-integer : Store addr -> integer
  [(store-ref-integer Store addr)
   ,(if (integer? (term ?v))
      (term ?v)
      (raise-argument-error 'store-ref-integer "non-integer value ~a at address ~a in store ~a" (term ?v) (term addr) (term Store)))
   (where (L ?v ?τ) #{store-ref Store addr})])

(define-metafunction RST
  store-ref-type : Store addr -> ?τ
  [(store-ref-type Store addr)
   ?τ
   (where (L v ?τ) #{store-ref Store addr})])

(define-metafunction RST
  store-set : Store L addr v ?τ -> Store
  [(store-set Store L addr v ?τ -> Store)
   ,(cons (term (addr L v ?τ)) (term Store))])

(define-metafunction RST
  store-update-type : Store addr ?τ -> Store
  [(store-update-type Store addr ?τ_new)
   ((addr_0 L_0 ?v_0 ?τ_0) ... (addr L ?v ?τ_new) (addr_2 L_2 ?v_2 ?τ_2) ...)
   (where ((addr_0 L_0 ?v_0 ?τ_0) ... (addr L ?v ?τ_old) (addr_2 L_2 ?v_2 ?τ_2) ...) Store)]
  [(store-update-type Store addr ?τ)
   ,(raise-user-error 'store-update-type "address ~a unbound in store ~a" (term addr) (term Store))])

(define-metafunction RST
  store-update : Store addr any -> Store
  [(store-update Store addr #f)
   ,(raise-argument-error 'store-update "store-entry?" 2 (term Store) (term addr) #f)]
  [(store-update Store addr (L_new ?v_new ?τ_new))
   ((addr_0 L_0 ?v_0 ?τ_0) ... (addr L_new ?v_new ?τ_new) (addr_2 L_2 ?v_2 ?τ_2) ...)
   (where ((addr_0 L_0 ?v_0 ?τ_0) ... (addr L_1 ?v_1 ?τ_1) (addr_2 L_2 ?v_2 ?τ_2) ...) Store)]
  [(store-update Store addr (L_new ?v_new ?τ_new))
   ,(raise-user-error 'store-update "address ~a unbound in store ~a" (term addr) (term Store))])

(define-metafunction RST
  kont-add : Kont K -> Kont
  [(kont-add Kont K)
   ,(cons (term K) (term Kont))])

(define-metafunction RST
  kont-pop : Kont -> (K Kont)
  [(kont-pop Kont)
   (,(car (term Kont)) ,(cdr (term Kont)))])

(define-judgment-form RST
  #:mode (language<? I I)
  #:contract (language<? L L)
  [
   ---
   (language<? R S)]
  [
   ---
   (language<? S T)]
  [
   --- Trans
   (language<? R T)])

(module+ test
  (test-case "τ=?"
    (check-mf-apply*
     [(τ=? Boolean Boolean)
      #true]
     [(τ=? Boolean (Boxof Boolean))
      #false]
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
     [(type-normalize Boolean)
      Boolean]
     [(type-normalize Integer)
      Integer]
    )
  )

  (test-case "unionize"
    (check-mf-apply*
     [(unionize Boolean Boolean)
      Boolean]
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
     [(type-env-set () R x TST)
      ((x R TST))]
     [(type-env-set () R x Integer)
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
  #:mode (well-typed I I O)
  #:contract (well-typed Γ P ?τ)
  [
   (R-typed Γ e TST)
   ---
   (well-typed Γ (R e) TST)]
  [
   (T-typed Γ e σ)
   ---
   (well-typed Γ (S e) σ)]
  [
   (T-typed Γ e σ)
   ---
   (well-typed Γ (T e) σ)])

;; (R-typed Γ e)
;; recur through `e` and ensure that all typed components are well-typed
(define-judgment-form RST
  #:mode (R-typed I I O)
  #:contract (R-typed Γ e TST)
  [
   (where ?τ #{type-env-ref Γ x})
   --- Var
   (R-typed Γ x TST)]
  [
   --- Boolean
   (R-typed Γ boolean TST)]
  [
   --- Integer
   (R-typed Γ integer TST)]
  [
   (where Γ_x #{type-env-set Γ R x TST})
   (R-typed Γ_x e TST)
   --- Lambda
   (R-typed Γ (λ (x) e) TST)]
  [
   (R-typed Γ e TST)
   --- Unbox
   (R-typed Γ (unbox e) TST)]
  [
   (R-typed Γ e_0 TST)
   (R-typed Γ e_1 TST)
   --- Set-Box
   (R-typed Γ (set-box! e_0 e_1) TST)]
  [
   (R-typed Γ e_0 TST)
   (R-typed Γ e_1 TST)
   --- aop
   (R-typed Γ (aop e_0 e_1) TST)]
  [
   (R-typed Γ e_0 TST)
   (R-typed Γ e_1 TST)
   --- App
   (R-typed Γ (e_0 e_1) TST)]
  [
   (R-typed Γ e_0 TST)
   --- Box
   (R-typed Γ (box e_0) TST)]
  [
   (R-typed Γ e_0 TST)
   (R-typed Γ e_1 TST)
   (R-typed Γ e_2 TST)
   --- If
   (R-typed Γ (if e_0 e_1 e_2) TST)]
  [
   (well-typed Γ (L e_0) ?τ)
   (where Γ_x #{type-env-set Γ L x e_0})
   (R-typed Γ_x e_1 TST)
   --- Let
   (R-typed Γ (let ((x L e_0)) e_1) TST)]
  [
   (where Γ_x #{type-env-set Γ L x e_0})
   (well-typed Γ_x (L e_0) ?τ)
   (R-typed Γ_x e_1 TST)
   --- Letrec
   (R-typed Γ (letrec ((x L e_0)) e_1) TST)]
  [
   (R-typed Γ e TST)
   --- Ann
   (R-typed Γ (:: e σ) TST)]
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
   --- Boolean
   (T-typed Γ boolean Boolean)]
  [
   --- Integer
   (T-typed Γ integer Integer)]
  [
   (where Γ_x #{type-env-set Γ T x τ_0}) ;; TODO sometimes use S ?
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
   (well-typed Γ (L (:: e_0 τ_0)) ?τ_dontcare) ;; ?τ_dontcare might be TST, only τ_0 matters
   (where Γ_x #{type-env-set Γ L x τ_0})
   (T-typed Γ_x e_1 τ_1)
   --- Let
   (T-typed Γ (let ((x L (:: e_0 τ_0))) e_1) τ_1)]
  [
   (un-annotated e_0)
   (side-condition ,(raise-user-error 'T-typed "un-annotated let expression ~a" (term (let ((L x e_0)) e_1))))
   --- LetError
   (T-typed Γ (let ((x L e_0)) e_1) Integer)]
  [
   (where Γ_x #{type-env-set Γ L x τ_0})
   (well-typed Γ_x (L (:: e_0 τ_0)) τ_dontcare)
   (T-typed Γ_x e_1 τ_1)
   --- Letrec
   (T-typed Γ (letrec ((x L (:: e_0 τ_0))) e_1) τ_1)]
  [
   (un-annotated e_0)
   (side-condition ,(raise-user-error 'T-typed "un-annotated letrec expression ~a" (term (letrec ((L x e_0)) e_1))))
   --- LetRecError
   (T-typed Γ (letrec ((x L e_0)) e_1) Integer)]
  [
   (side-condition ,(not (and (pair? (term e)) (memq (car (term e)) '(box λ)))))
   (T-typed Γ e τ_e)
   (type-equal? τ_e τ)
   --- Ann
   (T-typed Γ (:: e τ) τ)]
)

(define-metafunction RST
  typecheck : P -> any
  [(typecheck P)
   ?τ
   (judgment-holds (well-typed () P ?τ))]
  [(typecheck P)
   #false])

(module+ test
  (test-case "typecheck R-only"
    (check-mf-apply*
     [(typecheck (R #false))
      TST]
     [(typecheck (R 4))
      TST]
     [(typecheck (R (λ (x) 3)))
      TST]
     [(typecheck (R (+ 1 2)))
      TST]
     [(typecheck (R (+ 1 (box 3))))
      TST]
     [(typecheck (R (if 1 2 3)))
      TST]
     [(typecheck (R (box (λ (x) (+ 2 2)))))
      TST]
     [(typecheck (R (set-box! (box 2) (+ 1 1))))
      TST]
     [(typecheck (R ((λ (x) (set-box! x 0)) (box 42))))
      TST]
     [(typecheck (R ((λ (x) (set-box! 0 x)) (box 42))))
      TST]
     [(typecheck (R (let ((x R 4)) x)))
      TST]
     [(typecheck (R (let ((x R 4)) (x x))))
      TST]
     [(typecheck (R (letrec ((x R 4)) x)))
      TST]
     [(typecheck (R (letrec ((x R (box 3))) (+ x x))))
      TST]
    )
  )

  (test-case "typecheck S-only"
    (check-mf-apply*
     [(typecheck (S #true))
      Boolean]
     [(typecheck (S 4))
      Integer]
     [(typecheck (S (:: (λ (x) 3) (→ (→ Integer Integer) Integer))))
      (→ (→ Integer Integer) Integer)]
     [(typecheck (S (+ 1 2)))
      Integer]
     [(typecheck (S (+ 1 (:: (box 3) (Boxof Integer)))))
      #false]
     [(typecheck (S (if 1 2 3)))
      Integer]
     [(typecheck (S (:: (box (:: (λ (x) (+ 2 2)) (→ Integer Integer))) (Boxof (→ Integer Integer)))))
      (Boxof (→ Integer Integer))]
     [(typecheck (S (set-box! (:: (box 2) (Boxof Integer)) (+ 1 1))))
      (Boxof Integer)]
     [(typecheck (S (set-box! (:: (box 2) (Boxof Integer)) (:: (box 1) (Boxof Integer)))))
      #false]
     [(typecheck (S ((:: (λ (x) (set-box! x 0)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      (Boxof Integer)]
     [(typecheck (S ((:: (λ (x) (set-box! 0 x)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #false]
     [(typecheck (S (let ((x S (:: 4 Integer))) x)))
      Integer]
     [(typecheck (S (let ((x S (:: 4 Integer))) (x x))))
      #false]
     [(typecheck (S (letrec ((x S (:: 4 Integer))) x)))
      Integer]
     [(typecheck (S (letrec ((x S (:: (box 3) (Boxof Integer)))) x)))
      (Boxof Integer)]
     [(typecheck (S (letrec ((x S (:: (box 3) (Boxof Integer)))) (+ x x))))
      #false]
    )
  )

  (test-case "typecheck T-only"
    (check-mf-apply*
     [(typecheck (T #true))
      Boolean]
     [(typecheck (T 4))
      Integer]
     [(typecheck (T (:: (λ (x) 3) (→ Integer Integer))))
      (→ Integer Integer)]
     [(typecheck (T (+ 1 2)))
      Integer]
     [(typecheck (T (+ 1 (:: (box 3) (Boxof Integer)))))
      #false]
     [(typecheck (T (if 1 2 3)))
      Integer]
     [(typecheck (T (:: (box (:: (λ (x) (+ 2 2)) (→ Integer Integer))) (Boxof (→ Integer Integer)))))
      (Boxof (→ Integer Integer))]
     [(typecheck (T (:: (box 2) Integer)))
      #false]
     [(typecheck (T (set-box! (:: (box 2) (Boxof Integer)) (+ 1 1))))
      (Boxof Integer)]
     [(typecheck (T ((:: (λ (x) (set-box! x 0)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      (Boxof Integer)]
     [(typecheck (T ((:: (λ (x) (set-box! 0 x)) (→ (Boxof Integer) (Boxof Integer))) (:: (box 42) (Boxof Integer)))))
      #false]
     [(typecheck (T (let ((x T (:: 4 Integer))) x)))
      Integer]
     [(typecheck (T (let ((x T (:: 4 Integer))) (x x))))
      #false]
     [(typecheck (T (letrec ((x T (:: 4 Integer))) x)))
      Integer]
     [(typecheck (T (letrec ((x T (:: (box 3) (Boxof Integer)))) x)))
      (Boxof Integer)]
     [(typecheck (T (letrec ((x T (:: (box 3) (Boxof Integer)))) (+ x x))))
      #false]
    )
  )

  (test-case "missing-annotation"
    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (S (box 3)))))))

    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (S (λ (x) 3)))))))

    (check-exn #rx"un-annotated"
      (λ () (convert-compile-time-error (term (typecheck (T (let ((f R (λ (x) (+ x 1)))) f)))))))
  )

  (test-case "typecheck T"
    (check-mf-apply*
     [(typecheck (T (:: (λ (x) x) (→ (U (Boxof Integer) Integer) (U (Boxof Integer) Integer)))))
      (→ (U (Boxof Integer) Integer) (U (Boxof Integer) Integer))]
     [(typecheck (T (:: (λ (x) (if (= x 0) x (:: (box x) (Boxof Integer)))) (→ Integer (U (Boxof Integer) Integer)))))
      (→ Integer (U (Boxof Integer) Integer))]
     [(typecheck (T (:: (λ (x) (+ x 1)) (→ (U (Boxof Integer) Integer) Integer))))
      #false]
     [(typecheck (T (letrec ((fact T (:: (λ (n) (if (= n 1) 1 (* n (fact (- n 1))))) (→ Integer Integer)))) (fact 4))))
      Integer]
     [(typecheck (T (letrec ((fact T (:: (λ (n) (if (= n 1) (:: (box 1) (Boxof Integer)) (* n (fact (- n 1))))) (→ Integer Integer)))) (fact 4))))
      #false]
     [(typecheck (T
       (letrec ((deep T (:: (λ (x) (if (= 0 x) x (:: (box (deep (- x 1)))
                                                     (Boxof (μ (α1) (U (Boxof α1) Integer))))))
                            (→ Integer (μ (α0) (U (Boxof α0) Integer))))))
         (deep 3))))
      (μ (α2) (U (Boxof α2) Integer))]
    )
  )

  (test-case "mixed-lang I"
    (check-mf-apply*
     [(typecheck (T (let ((f R (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f 1))))
      Integer]
     [(typecheck (T (let ((f R (:: (λ (x) (+ x 1)) (→ (Boxof Integer) (Boxof Integer))))) (f (:: (box 1) (Boxof Integer))))))
      (Boxof Integer)]
     [(typecheck (S (let ((f R (:: (λ (x) (+ x 1)) (→ (Boxof Integer) (Boxof Integer))))) (f (:: (box 1) (Boxof Integer))))))
      (Boxof Integer)]
     [(typecheck (R (let ((f S (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f 55))))
      TST]
     [(typecheck (R (let ((f T (:: (λ (x) (+ x 1)) (→ Integer Integer)))) (f (box 4)))))
      TST]
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- tag checking

(define-judgment-form RST
  #:mode (well-tagged I I)
  #:contract (well-tagged v τ)
  [
   ---
   (well-tagged boolean Boolean)]
  [
   ---
   (well-tagged integer Integer)]
  [
   ---
   (well-tagged c (→ τ_0 τ_1))]
  [
   ---
   (well-tagged (box any) (Boxof τ))])

(define-metafunction RST
  well-tagged? : v τ -> boolean
  [(well-tagged? v τ)
   #true
   (judgment-holds (well-tagged v τ))]
  [(well-tagged? v τ)
   #false])

(module+ test
  (check-mf-apply*
   [(well-tagged? 4 Integer)
    #true]
   [(well-tagged? #true Boolean)
    #true]
   [(well-tagged? #false Boolean)
    #true]
   [(well-tagged? (box 3) (Boxof Integer))
    #true]
   [(well-tagged? (box 4) (Boxof Boolean))
    #true]
   [(well-tagged? (CLOSURE 1 () ()) (→ Integer Boolean))
    #true]
   ;;
   [(well-tagged? 3 Boolean)
    #false]
   [(well-tagged? 3 (Boxof Integer))
    #false]
   [(well-tagged? #false (Boxof Integer))
    #false]
   [(well-tagged? (CLOSURE 1 () ()) Integer)
    #false]
  )
)

;; -----------------------------------------------------------------------------
;; --- (discriminating,colorful,eidetic) evaluation

;; Need to check:
;; - R/S flowing into T context
;; -- (let ((x R/S e)) T)
;;                 ^
;; -- (T R/S)
;;       ^^^
;; -- (R/S T)
;;    ^^^^^^^
;; -- (set-box T R/S)
;;               ^^^
;; -- (set! T R/S)
;;            ^^^
;; - R flowing into S
;; -- (let ((x R e)) S)
;;               ^
;; -- (S R)
;;       ^
;; -- (R S)
;;    ^^^^^
;; -- (set-box! S R)
;;                ^
;; -- (set! S R)
;;            ^

(define -->RST
  (reduction-relation RST
    #:domain Σ
;; --- kont-adding
    [-->
      (STATE R (λ (x) e) Γ ρ Store Kont)
      (STATE R addr Γ ρ Store_λ Kont)
      R-Lambda+
      (fresh addr)
      (where c (CLOSURE (λ (x) e) Γ ρ))
      (where Store_λ #{store-set Store L addr c TST})]
    [-->
      (STATE L\R (:: (λ (x) e) τ) Γ ρ Store Kont)
      (STATE L\R addr Γ ρ Store_λ Kont)
      ST-Lambda+
      (fresh addr)
      (where c (CLOSURE (λ (x) e) Γ ρ))
      (where Store_λ #{store-set Store L\R addr c τ})]
    [-->
      (STATE L boolean Γ ρ Store Kont)
      (STATE L addr Γ ρ Store_bool Kont)
      RST-Bool+
      (fresh addr)
      (where Store_bool #{store-set Store L addr boolean Boolean})]
    [-->
      (STATE L integer Γ ρ Store Kont)
      (STATE L addr Γ ρ Store_int Kont)
      RST-Int+
      (fresh addr)
      (where Store_int #{store-set Store L addr integer Integer})]
    [-->
      (STATE L (if e_0 e_1 e_2) Γ ρ Store Kont)
      (STATE L e_0 Γ ρ Store Kont_if)
      RST-If+
      (where Kont_if #{kont-add Kont (IF e_1 e_2)})]
    [-->
      (STATE L_ctx (let ((x L_0 e_0)) e_1) Γ ρ Store Kont)
      (STATE L_0 e_0 Γ ρ Store Kont_let)
      RST-Let+
      (where ?τ #{type-annotation L_ctx e_0})
      (where Kont_let #{kont-add Kont (LET L_ctx x ?τ e_1)})]
    [-->
      (STATE L_ctx (letrec ((x L_0 e_0)) e_1) Γ ρ Store Kont)
      (STATE L_0 e_0 Γ ρ_x Store_addr Kont_letrec)
      RST-LetRec+
      (fresh addr)
      (where ρ_x #{runtime-env-set ρ x addr})
      (where ?τ #{type-annotation L_ctx e_0})
      (where Store_addr #{store-set Store addr UNDEF ?τ})
      (where Kont_letrec #{kont-add Kont (LETREC L_ctx x ?τ e_1)})]
    [-->
      (STATE L (:: e τ) Γ ρ Store Kont)
      (STATE L e Γ ρ Store Kont)
      RST-Ann+]
    [-->
      (STATE L (e_0 e_1) Γ ρ Store Kont)
      (STATE L e_0 Γ ρ Store Kont_app)
      RST-App+
      (where Kont_app #{kont-add Kont (APP () (e_1))})]
    [-->
      (STATE R (box e) Γ ρ Store Kont)
      (STATE R e Γ ρ Store Kont_b)
      R-boxE+
      (where Kont_b #{kont-add Kont (BOX TST)})]
    [-->
      (STATE L\R (:: (box e) τ) Γ ρ Store Kont)
      (STATE L\R e Γ ρ Store Kont_b)
      ST-boxE+
      (where Kont_b #{kont-add Kont (BOX τ)})]
    [-->
      (STATE L (unbox e) Γ ρ Store Kont)
      (STATE L e Γ ρ Store Kont_u)
      RST-unbox+
      (where Kont_u #{kont-add Kont (OP unbox () ())})]
    [-->
      (STATE L (set-box! e_0 e_1) Γ ρ Store Kont)
      (STATE L e_0 Γ ρ Store Kont_s)
      RST-set-box!+
      (where Kont_s #{kont-add Kont (OP set-box! () (e_1))})]
    [-->
      (STATE L (aop e_0 e_1) Γ ρ Store Kont)
      (STATE L e_0 Γ ρ Store Kont_a)
      RST-aop+
      (where Kont_a #{kont-add Kont (OP aop () (e_1))})]
;; --- kont-removing
    [-->
      (STATE L x Γ ρ Store Kont)
      (STATE L addr Γ ρ Store Kont)
      RST-var-
      (judgment-holds (variable? x (STATE L x Γ ρ Store Kont)))
      (where addr #{runtime-env-ref ρ x})]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L e_next Γ ρ Store Kont_rest)
      RST-If-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((IF e_1 e_2) Kont_rest) #{kont-pop Kont})
      (where boolean_0 #{store-ref-value Store addr})
      (where e_next ,(if (term boolean_0) (term e_1) (term e_2)))]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L_ctx e Γ ρ_x Store_τ Kont_rest)
      RST-Let-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((LET L_ctx x ?τ e) Kont_rest) #{kont-pop Kont})
      (fresh addr)
      (where ρ_x #{runtime-env-set ρ x addr})
      (where Store_τ ,(if (term (judgment-holds (language<? L L_ctx)))
                        (term #{store-update-type Store addr ?τ})
                        (term Store_v)))]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L_ctx e Γ ρ Store_τ Kont_rest)
      RST-Letrec-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((LETREC L_ctx x ?τ e) Kont_rest) #{kont-pop Kont})
      (where addr_x #{runtime-env-ref ρ x})
      (where Store_v #{store-update Store addr_x #{store-ref Store addr}})
      (where Store_τ ,(if (term (judgment-holds (language<? L L_ctx)))
                        (term #{store-update-type Store addr_x ?τ})
                        (term Store_v)))]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L e_a0 Γ ρ Store Kont_rest)
      RST-App1-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((APP (addr_a ...) (e_a0 e_a1 ...)) Kont_rest) #{kont-pop Kont})
      (where Kont_next #{kont-add Kont_rest (APP (addr addr_a ...) (e_a1 ...))})]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L e_a0 Γ ρ Store Kont_rest)
      RST-Op1-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((OP op (addr_a ...) (e_a0 e_a1 ...)) Kont_rest) #{kont-pop Kont})
      (where Kont_next #{kont-add Kont_rest (OP op (addr addr_a ...) (e_a1 ...))})]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L e_c Γ_c ρ_c Store Kont_rest)
      RST-App2-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((APP (addr_a ...) ()) Kont_rest) #{kont-pop Kont})
      (where (addr_f addr_arg ...) ,(reverse (term (addr addr_a ...))))
      (where c #{store-ref Store addr_f})
      (where (e_c Γ_c ρ_c) #{apply-closure c addr_arg ...})]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L e_new Γ ρ Store_new Kont_rest)
      RST-Op2-
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((OP op (addr_a ...) ()) Kont_rest) #{kont-pop Kont})
      (where (addr_arg0 addr_arg ...) ,(reverse (term (addr addr_a ...))))
      (where (e_new Store_new) #{apply-op Store op addr_arg0 addr_arg ...})]
    [-->
      (STATE L addr Γ ρ Store Kont)
      (STATE L addr_b Γ ρ Store_b Kont)
      RST-boxV+
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      (where ((Box ?τ) Kont_rest) #{kont-pop Kont})
      (fresh addr_b)
      (where Store_b #{store-set Store L addr_b (box addr) ?τ})]
    #;[-->
      (STATE L addr Γ ρ Store Kont)
      ???
      RST-Check
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      ???]
    #;[-->
      (STATE L addr Γ ρ Store Kont)
      ???
      RST-Tag
      (judgment-holds (address? addr (STATE L addr Γ ρ Store Kont)))
      ???]
))

(define -->RST*
  ;; TODO need to check fixpoint
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
  state->language : Σ -> P
  [(state->language (STATE L e Γ ρ Store Kont))
   L])

(define-metafunction RST
  state->expression : Σ -> P
  [(state->expression (STATE L e Γ ρ Store Kont))
   e])

(define-metafunction RST
  state->type-env : Σ -> Γ
  [(state->type-env (STATE L e Γ ρ Store Kont))
   Γ])

(define-metafunction RST
  state->runtime-env : Σ -> ρ
  [(state->runtime-env (STATE L e Γ ρ Store Kont))
   ρ])

(define-metafunction RST
  state->store : Σ -> Store
  [(state->store (STATE L e Γ ρ Store Kont))
   Store])

(define-metafunction RST
  state->kont : Σ -> Kont
  [(state->kont (STATE L e Γ ρ Store Kont))
   Kont])

(define-metafunction RST
  type-annotation : L e -> ?τ
  [(type-annotation R e)
   TST]
  [(type-annotation L\R (:: e τ))
   τ]
  [(type-annotation L\R e)
   ,(raise-user-error 'type-annotation "missing type annotation (type soundness bug?) on term ~a" (term e))])

(define-metafunction RST
  apply-closure : c addr ... -> (e Γ ρ)
  [(apply-closure (CLOSURE (λ (x) e) Γ ρ) addr)
   (e Γ ρ_x)
   (where ρ_x #{runtime-env-set ρ x addr})]
  [(apply-closure (CLOSURE (λ (x) e) Γ ρ))
   ,(raise-arguments-error 'apply-closure "one address" "closure" (term (CLOSURE (λ (x) e) Γ ρ)))]
  [(apply-closure (CLOSURE e Γ ρ) addr ...)
   ,(raise-argument-error 'apply-closure "closure with simple λ inside" (term (CLOSURE (λ (x) e))))]
  [(apply-closure e addr ...)
   ,(raise-argument-error 'apply-closure "closure" (term e))])

(define-metafunction RST
  apply-op : Store op addr ... -> (e Store)
  [(apply-op Store aop addr ...)
   (v Store)
   (where v ,(do-aop (term aop) (term (#{store-ref-integer addr} ...))))]
  [(apply-op Store unbox addr_b)
   (addr Store)
   (where (box addr) #{store-ref-value Store addr_b})]
  [(apply-op Store set-box! addr_b addr_v)
   ;; TODO is final value store or address or what???
   (addr_b Store_b)
   (where (L_b ?v_b ?τ_b) #{store-ref Store addr_b})
   (where (L_v ?v_v ?τ_v) #{store-ref Store addr_v})
   (where (v_new Store_new) ,(if (term (judgment-holds (language<? L_v L_b)))
                               (term #{dynamic-typecheck L_b Store ?v_v ?τ_b})
                               (term ?v_v)))
   (where Store_b #{store-update Store_new addr_b (L_b v_new ?τ_b)})])

(define-metafunction RST
  dynamic-typecheck : L Store v τ -> (v Store)
  [(dynamic-typecheck R Store v τ)
   (v Store)]
  [(dynamic-typecheck S Store v τ)
   ,(if (term (judgment-holds (well-tagged v τ)))
      (term (v Store))
      (raise-dynamic-typecheck-error (term S) (term v) (term τ)))]
  [(dynamic-typecheck T Store v τ)
   ;; TODO really is not THAT hard, but need to think a little
   ,(raise-user-error 'not-implemented)])

(define (raise-dynamic-typecheck-error L v τ)
  (raise-user-error 'dynamic-typecheck "language ~a expected ~a received ~a" L τ v))

(define (do-aop aop int*)
  (define f
    (case aop
     [(=) (let ([compare-to (box #f)])
            (λ (acc n)
              (if (unbox compare-to)
                (and acc (= (unbox compare-to) n))
                (begin (set-box! compare-to n) #true))))]
     [(+) +]
     [(-) -]
     [(*) *]
     [else (raise-argument-error 'fold-aop "aop?" aop)]))
  (for/fold ([acc (car int*)])
            ([n2 (in-list (cdr int*))])
    (f acc n2)))

(module+ test
  (test-case "do-aop" ;; (->  aop-sym int* (or/c int bool))
  )
)

;; -----------------------------------------------------------------------------
;; --- (colorblind) compiler
;; - translate R S T terms all to R
;; - but the S T terms have proper checks,
;; - via contracts and type-directed defense

