#lang mf-apply racket/base

;; Tagged Racket
;; "you can trust the tags"
;;
;; Check any value that enters typed code from "untyped" code
;; - check imports from untyped code
;; - check input to typed functions
;; - check reads from untyped data (calling untyped function, read from box/list)
;; For now, be conservative. Anything might be untyped.
;;
;; This is dynamic typing, where every type annotation represents a boundary.

;; Soundness = tag soundness

;; TODO
;; - sound completion (let vs require)
;; - support Nat types .... see primop-type
;; - blame for dynamic checks
;; - remove unnecessary checks
;; - optimize

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
;; τ = specification language
  (τ ::= τ0 (∀ (α) τ))
  (τ0 ::= α k0 (k1 τ) (k2 τ τ))
  (k ::= k0 k1 k2)
  (k0 ::= Nat Int Bool)
  (k1 ::= Box)
  (k2 ::= Pair →)
  (K ::= k) ;; types we can check at runtime, O(1)
  (Γ ::= ((x τ) ...))
  (Σ ::= ((α τ*) ...)) ;; constraints
  (τ* ::= (τ ...))

;; v = values
  (v ::= (box x) integer boolean (cons v v))

;; e = implicitly typed source language, allows untyped terms
;;     needs explicit types for functions
;;      and embedded untyped terms
  (e ::= v Λ x (e e) (if e e e)
         (let (x e) e)
         (:: Λ τ) ;; not allowed in untyped code
         (require (x τ e) e) ;; not allowed in untyped code
         (unop e) (binop e e) (cons e e))
  (Λ ::= (fun x (x) e))
  (primop ::= unop binop)
  (unop ::= car cdr make-box unbox)
  (binop ::= + * - = set-box!)

;; t = explicitly typed intermediate language, still allows untyped (source) terms
  (t ::= (:: v τ) (:: Λt τ) (:: x τ) (:: (t t) τ) (:: (if t t t) τ)
         (:: (fun x (x) t) τ)
         (:: (let (x t) t) τ)
         (:: (require (x τ e) t) τ)
         (:: (unop t) τ)
         (:: (binop t t) τ)
         (:: (cons t t) τ))
  (Λt ::= (fun x (x) t))

;; c = type-erased, explicitly checked core language
  (c ::= v Λc x (c c) (if c c c) (let (x c) c) (unop c) (binop c c) (cons c c) (check K c))
  (Λc ::= (fun x (x) c))
  (vc ::= v Λc)
  (σ ::= ((x vc) ...))
  (E ::= hole (E c) (vc E) (if E c c) (let (x E) c) (unop E) (binop E c) (binop vc E) (cons E c) (cons vc E) (check K E))
  (RuntimeError ::= (CheckError K vc))
  (A ::= [σ c] RuntimeError)

  (x* ::= (x ...))
  (α* ::= (α ...))
  (x α ::= variable-not-otherwise-mentioned)
#:binding-forms
  (∀ (α) τ #:refers-to α)
  (let (x e) e_1 #:refers-to x)
  (require (x τ e) e_1 #:refers-to x)
  (fun x_f (x) e #:refers-to (shadow x_f x))
  (fun x_f (x) t #:refers-to (shadow x_f x))
  (fun x_f (x) c #:refers-to (shadow x_f x))
  (let (x t) t_1 #:refers-to x)
  (require (x τ_x e) t_1 #:refers-to x)
  (let (x c) c_1 #:refers-to x))

(module+ test
  (check-pred c?
    (term (check Int (factorial«46» (- n«47» 1)))))
  (check-pred c?
    (term (fun factorial«46» (n«47») (if (= n«47» 1) 1 (* n«47» (check Int (factorial«46» (- n«47» 1))))))))
  (check-pred c?
    (term (check Int ((fun factorial«46» (n«47») (if (= n«47» 1) 1 (* n«47» (check Int (factorial«46» (- n«47» 1)))))) 5))))
  (check-pred σ? (term ()))
  (check-pred A?
    (term  (()
      (check Int ((fun factorial«46» (n«47») (if (= n«47» 1) 1 (* n«47» (check Int (factorial«46» (- n«47» 1)))))) 5)))))
)

;; =============================================================================

(define-metafunction TAG
  theorem:type-soundness : e -> boolean
  [(theorem:type-soundness e)
   boolean
   (judgment-holds (well-formed e))
   (where t #{type-check# e})
   (where τ #{type-annotation t})
   (where c #{completion# t})
   (where A #{eval# c})
   (where K #{tag# τ})
   (where boolean #{value-check# A K})])

(module+ test
  (test-case "type-soundness:basic"
    (check-true (term (theorem:type-soundness
      (+ 2 2))))
    (check-true (term (theorem:type-soundness
      ((:: (fun factorial (n)
             (if (= n 1) 1 (* n (factorial (- n 1))))) (→ Int Int))
       5))))
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  type-check# : e -> t
  [(type-check# e)
   t
   (judgment-holds (type-check () e t))
   (judgment-holds (sound-elaboration e t))]
  [(type-check# e)
   ,(raise-argument-error 'type-check# "well-typed expression" (term e))])

(module+ test
  (test-case "type-check:basic"
    (check-mf-apply* #:is-equal? α=?
     [(type-check# (+ 2 2))
      (:: (+ (:: 2 Int) (:: 2 Int)) Int)]
     [(type-check# (:: (fun f (x) #true) (→ Int Bool)))
      (:: (fun f (x) (:: #true Bool)) (→ Int Bool))])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  completion# : t -> c
  [(completion# t)
   c
   (judgment-holds (completion t c))
   #;(judgment-holds (sound-completion t c))]
  [(completion# t)
   ,(raise-argument-error 'completion# "completable, type-annotated term" (term t))])

(module+ test
  (test-case "completion:basic"
    (check-mf-apply* #:is-equal? α=?
     [(completion# (:: (+ (:: 2 Int) (:: 2 Int)) Int))
      (+ 2 2)]
     [(completion# (:: (let (x (:: 2 Int)) (:: (+ (:: x Int) (:: 2 Int)) Int)) Int))
      (let (x 2) (+ x 2))]
     [(completion# (:: (let (f (:: (fun f (x) (:: x Int)) (→ Int Int))) (:: ((:: f (→ Int Int)) (:: 2 Int)) Int)) Int))
      (let (f (fun f (x) x)) (check Int (f 2)))]
     [(completion# (:: (car (:: (cons (:: 1 Int) (:: 2 Int)) (Pair Int Int))) Int))
      (check Int (car (cons 1 2)))])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  eval# : c -> A
  [(eval# c)
   A_1
   (where A_0 #{load# c})
   (where A_1 ,(eval* (term A_0)))]
  [(eval# c)
   ,(raise-argument-error 'eval# "core term" (term c))])

(define-metafunction TAG
  load# : c -> A
  [(load# c)
   [() c]])

(define-metafunction TAG
  unload# : A -> any
  [(unload# RuntimeError)
   RuntimeError]
  [(unload# [σ (box x)])
   (box vc)
   (where vc #{runtime-env-ref σ x})]
  [(unload# [σ vc])
   vc])

(module+ test
  (test-case "eval:basic"
    (check-mf-apply*
     [(unload# (eval# (+ 2 2)))
      4]
     [(unload# (eval# ((fun fact (n) (if (= n 1) 1 (* n (fact (- n 1))))) 5)))
      120])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  value-check# : A K -> boolean
  [(value-check# A K)
   #true
   (judgment-holds (value-check A K))]
  [(value-check# A K)
   #false])

(module+ test
  (test-case "value-check:basic"
    (check-mf-apply*
     [(value-check# [() 4] Int)
      #true]
     [(value-check# [() 4] Bool)
      #false]
     [(value-check# [() (fun f (x) #false)] →)
      #true]
     [(value-check# [((x 4)) (box x)] Box)
      #true]
     [(value-check# [() (cons 1 1)] Pair)
      #true])
    (void)))

;; =============================================================================
;; === type check

(define-judgment-form TAG
  #:mode (type-check I I O)
  #:contract (type-check Γ e t)
  [
   ---
   (type-check Γ integer (:: integer Int))]
  [
   ---
   (type-check Γ boolean (:: boolean Bool))]
  [
   (where (fun x_f (x) e) Λ)
   (where Γ_f #{type-env-set Γ (x_f (→ τ_0 τ_1))})
   (where Γ_x #{type-env-set Γ_f (x τ_0)})
   (type-check Γ_x e t)
   (where τ_1 #{type-annotation t})
   (where t_Λ (:: (fun x_f (x) t) (→ τ_0 τ_1)))
   ---
   (type-check Γ (:: Λ (→ τ_0 τ_1)) t_Λ)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (type-check Γ x (:: x τ))]
  [
   (type-check Γ e_0 t_0)
   (type-check Γ e_1 t_1)
   (where τ_0 #{type-annotation t_0})
   (where τ_1 #{type-annotation t_1})
   ---
   (type-check Γ (cons e_0 e_1) (:: (cons t_0 t_1) (Pair τ_0 τ_1)))]
  [
   (type-check Γ e_0 t_0)
   (type-check Γ e_1 t_1)
   (where (→ τ_dom τ_cod) #{type-annotation t_0})
   (where τ_dom #{type-annotation t_1})
   ---
   (type-check Γ (e_0 e_1) (:: (t_0 t_1) τ_cod))]
  [
   (type-check Γ e_0 t_0)
   (type-check Γ e_1 t_1)
   (type-check Γ e_2 t_2)
   (where τ #{type-annotation t_1})
   (where τ #{type-annotation t_2})
   ---
   (type-check Γ (if e_0 e_1 e_2) (:: (if t_0 t_1 t_2) τ))]
  [
   (type-check Γ e_x t_x)
   (where τ_x #{type-annotation t_x})
   (where Γ_x #{type-env-set Γ (x τ_x)})
   (type-check Γ_x e_1 t_1)
   (where τ_1 #{type-annotation t_1})
   ---
   (type-check Γ (let (x e_x) e_1) (:: (let (x t_x) t_1) τ_1))]
  [
   (where Γ_x #{type-env-set Γ (x τ_x)})
   (type-check Γ_x e t)
   (where τ #{type-annotation t})
   ---
   (type-check Γ (require (x τ_x e_x) e) (:: (require (x τ_x e_x) t) τ))]
  [
   (type-check Γ e t)
   (where τ_e #{type-annotation t})
   (where τ_p #{primop-type unop})
   (where α #{fresh-type-variable (τ_e τ_p)})
   (where (→ _ τ_cod) #{unify (∀ (α) (→ τ_e α)) τ_p})
   ---
   (type-check Γ (unop e) (:: (unop t) τ_cod))]
  [
   (type-check Γ e_0 t_0)
   (type-check Γ e_1 t_1)
   (where τ_e0 #{type-annotation t_0})
   (where τ_e1 #{type-annotation t_1})
   (where τ_p #{primop-type binop})
   (where α #{fresh-type-variable (τ_e0 τ_e1 τ_p)})
   (where (→ _ (→ _ τ_cod)) #{unify (∀ (α) (→ τ_e0 (→ τ_e1 α))) τ_p})
   ---
   (type-check Γ (binop e_0 e_1) (:: (binop t_0 t_1) τ_cod))])

(define-judgment-form TAG
  #:mode (sound-elaboration I I)
  #:contract (sound-elaboration e t)
  [
   (where any_0 #{erase-types# e})
   (where any_1 #{erase-types# t})
   (side-condition ,(α=? (term any_0) (term any_1)))
   ---
   (sound-elaboration e t)])

(define-metafunction TAG
  erase-types# : any -> any
  [(erase-types# (:: any τ))
   #{erase-types# any}]
  [(erase-types# (any ...))
   (#{erase-types# any} ...)]
  [(erase-types# any)
   any])

(define-metafunction TAG
  unify : τ τ -> τ
  [(unify τ_0 τ_1)
   #{apply-substitution Σ_+ τ_0}
   (where Σ_+ #{unifying-substitution () τ_0 τ_1})])

(define-metafunction TAG
  apply-substitution : Σ τ -> τ
  [(apply-substitution Σ τ)
   #{apply-type-environment Γ τ}
   (where Γ #{substitution-resolve Σ})])

(define-metafunction TAG
  unifying-substitution : Σ τ τ -> Σ
  [(unifying-substitution Σ α τ_1)
   #{substitution-update Σ α τ_1}]
  [(unifying-substitution Σ τ_0 α)
   #{substitution-update Σ α τ_0}]
  [(unifying-substitution Σ (k1 τ_0) (k1 τ_1))
   #{unifying-substitution Σ τ_0 τ_1}]
  [(unifying-substitution Σ (k2 τ_dom0 τ_cod1) (k2 τ_dom1 τ_cod1))
   Σ_1
   (where Σ_0 #{unifying-substitution Σ τ_dom0 τ_dom1})
   (where Σ_1 #{unifying-substitution Σ_0 τ_cod0 τ_cod1})]
  [(unifying-substitution Σ (∀ (α) τ_0) τ_1)
   #{unifying-substitution Σ_0 τ_0 τ_1}
   (where Σ_0 #{substitution-add Σ α})]
  [(unifying-substitution Σ τ_0 (∀ (α) τ_1))
   #{unifying-substitution Σ_1 τ_0 τ_1}
   (where Σ_1 #{substitution-add Σ α})]
  [(unifying-substitution Σ τ_0 τ_1)
   ,(raise-arguments-error 'unify "unifiable types" "τ0" (term τ_0) "τ1" (term τ_1))])

(define-metafunction TAG
  apply-type-environment : Γ τ -> τ
  [(apply-type-environment () τ)
   τ] ;; TODO check closed?
  [(apply-type-environment ((α_0 τ_0) (α_rest τ_rest) ...) τ)
   (apply-type-environment ((α_rest τ_rest) ...) (substitute τ α_0 τ_0))])

;; Solve a system of unification constraints
(define-metafunction TAG
  substitution-resolve : Σ -> Γ
  [(substitution-resolve Σ)
   ,(error 'dieee)])

(define-metafunction TAG
  substitution-add : Σ α -> Σ
  [(substitution-add Σ α)
   ,(cons (term (α ())) (term Σ))])

(define-metafunction TAG
  substitution-pop : Σ -> ((α τ) Σ)
  [(substitution-pop Σ)
   ,(cons (car (term Σ)) (cdr (term Σ)))])

(define-metafunction TAG
  substitution-update : Σ α τ -> Σ
  [(substitution-update Σ α τ)
   ,(let* ([success? (box #f)]
           [Σ+ (for/list ([at (in-list (term Σ))])
                 (if (equal? (car at) (term α))
                   (begin
                     (set-box! success? #true)
                     (cons (car at) (set-add (cadr at) (term τ))))
                   at))])
      (if (unbox success?)
        Σ+
        (raise-arguments-error 'substitution-update "unbound variable" "var" (term α) "Σ" (term Σ))))])


;; =============================================================================
;; === completion

(define-judgment-form TAG
  #:mode (completion I O)
  #:contract (completion t c)
  [
   ---
   (completion (:: (box x) _) (box x))]
  [
   ---
   (completion (:: integer _) integer)]
  [
   ---
   (completion (:: boolean _) boolean)]
  [
   (completion t c)
   ---
   (completion (:: (fun x_f (x) t) _) (fun x_f (x) c))]
  [
   (completion t_0 c_0)
   (completion t_1 c_1)
   ---
   (completion (:: (cons t_0 t_1) _) (cons c_0 c_1))]
  [
   ---
   (completion (:: x _) x)]
  [
   (completion t_0 c_0)
   (completion t_1 c_1)
   (where (→ τ_dom τ_cod) #{type-annotation t_0})
   (where K #{tag# τ_cod})
   ---
   (completion (:: (t_0 t_1) _) (check K (c_0 c_1)))]
  [
   (completion t_0 c_0)
   (completion t_1 c_1)
   (completion t_2 c_2)
   ---
   (completion (:: (if t_0 t_1 t_2) _) (if c_0 c_1 c_2))]
  [
   (completion t_x c_x)
   (completion t c)
   ---
   (completion (:: (let (x t_x) t) _) (let (x c_x) c))]
  [
   (completion/untyped e_x c_x)
   (completion t c)
   (where K #{tag# τ_x})
   ---
   (completion (:: (require (x τ_x e_x) t) _) (let (x (check K c_x)) c))]
  [
   (completion t c)
   (where (→ _ τ_cod) #{primop-type unop})
   (where K #{tag# τ_cod})
   (where c_check ,(if (judgment-holds (eliminator unop))
                     (term (check K (unop c)))
                     (term (unop c))))
   ---
   (completion (:: (unop t) _) c_check)]
  [
   (completion t_0 c_0)
   (completion t_1 c_1)
   ;; TODO need to check sometimes?
   ---
   (completion (:: (binop t_0 t_1) _) (binop c_0 c_1))])

(define-judgment-form TAG
  #:mode (completion/untyped I O)
  #:contract (completion/untyped e c)
  [
   ---
   (completion/untyped (box x) (box x))]
  [
   ---
   (completion/untyped integer integer)]
  [
   ---
   (completion/untyped boolean boolean)]
  [
   (where (fun x_f (x) e) Λ)
   (completion/untyped e c)
   ---
   (completion/untyped Λ (fun x_f (x) c))]
  [
   (completion/untyped e_0 c_0)
   (completion/untyped e_1 c_1)
   ---
   (completion/untyped (cons e_0 e_1) (cons c_0 c_1))]
  [
   ---
   (completion/untyped x x)]
  [
   (completion/untyped e_0 c_0)
   (completion/untyped e_1 c_1)
   (where c_check (check → c_0))
   ;; TODO need to check arguments if e_0 typed
   ---
   (completion/untyped (e_0 e_1) (c_check c_1))]
  [
   (completion/untyped e_0 c_0)
   (completion/untyped e_1 c_1)
   (completion/untyped e_2 c_2)
   ---
   (completion/untyped (if e_0 e_1 e_2) (if c_0 c_1 c_2))]
  [
   (completion/untyped e_x c_x)
   (completion/untyped e c)
   ---
   (completion/untyped (let (x e_x) e) (let (x c_x) c))]
  [
   (completion/untyped e c)
   (where (→ _ τ_cod) #{primop-type unop})
   (where K #{tag# τ_cod})
   (where c_check ,(if (judgment-holds (eliminator unop))
                     (term (check K c))
                     (term c)))
   ---
   (completion/untyped (unop e) (unop c_check))]
  [
   (completion/untyped e_0 c_0)
   (completion/untyped e_1 c_1)
   (where (→ τ_dom0 (→ τ_dom1 τ_cod)) #{primop-type binop})
   (where c_check0 (check #{tag# τ_dom0} c_0))
   (where c_check1 (check #{tag# τ_dom1} c_1)) ;; TODO don't check for set-box!
   ---
   (completion/untyped (binop e_0 e_1) (binop c_check0 c_check1))])

(define-judgment-form TAG
  #:mode (eliminator I)
  #:contract (eliminator primop)
  [
   ---
   (eliminator car)]
  [
   ---
   (eliminator cdr)]
  [
   ---
   (eliminator unbox)])

(define-judgment-form TAG
  #:mode (sound-completion I I)
  #:contract (sound-completion t c)
  [
   (where any_0 #{erase-types# t})
   (where any_1 #{erase-checks# c})
   (side-condition ,(α=? (term any_0) (term any_1)))
   (side-condition #false) ;; TODO completion is converting "require" to "let"
   ---
   (sound-completion t c)])

(define-metafunction TAG
  erase-checks# : any -> any
  [(erase-checks# (check K c))
   #{erase-checks# c}]
  [(erase-checks# (any ...))
   (#{erase-checks# any} ...)]
  [(erase-checks# any)
   any])

;; =============================================================================
;; === eval

(define -->TAG
  (reduction-relation TAG
   #:domain A
   [-->
    [σ (in-hole E (Λc vc))]
    [σ (in-hole E c_v)]
    E-Beta
    (where (fun x_f (x) c) Λc)
    (where c_f (substitute c x_f Λc))
    (where c_v (substitute c_f x vc))]
   [-->
    [σ (in-hole E (if vc c_0 c_1))]
    [σ (in-hole E c_next)]
    E-If
    (where c_next ,(if (term vc) (term c_0) (term c_1)))]
   [-->
    [σ (in-hole E (let (x vc) c))]
    [σ (in-hole E c_x)]
    E-Let
    (where c_x (substitute c x vc))]
   [-->
    [σ (in-hole E (primop vc ...))]
    #{maybe-in-hole E A}
    E-PrimOp
    (where A (apply-primop [σ (primop vc ...)]))]
   [-->
    [σ (in-hole E (check K vc))]
    #{maybe-in-hole E A}
    E-Check
    (where A #{apply-check [σ (check K vc)]})]))

(define-metafunction TAG
  maybe-in-hole : E A -> A
  [(maybe-in-hole E RuntimeError)
   Runtime-Error]
  [(maybe-in-hole E [σ c])
   [σ (in-hole E c)]])

(define eval*
  (make--->* -->TAG))

;; =============================================================================
;; === value-check

(define-judgment-form TAG
  #:mode (value-check I I)
  #:contract (value-check A K)
  [
   ---
   (value-check RuntimeError K)]
  [
   ---
   (value-check [σ (box _)] Box)]
  [
   ---
   (value-check [σ natural] Nat)]
  [
   ---
   (value-check [σ integer] Int)]
  [
   ---
   (value-check [σ Λc] →)]
  [
   ---
   (value-check [σ (cons _ _)] Pair)])

(define-metafunction TAG
  tag# : τ -> K
  [(tag# τ)
   K
   (judgment-holds (tag-of τ K))])

(define-judgment-form TAG
  #:mode (tag-of I O)
  #:contract (tag-of τ K)
  [
   ---
   (tag-of K K)]
  [
   ---
   (tag-of (Box _) Box)]
  [
   ---
   (tag-of (Pair _ _) Pair)]
  [
   ---
   (tag-of (→ _ _) →)])

;; =============================================================================
;; =============================================================================

;; =============================================================================
;; === grammar

(define-judgment-form TAG
  #:mode (well-formed I)
  #:contract (well-formed e)
  [
   (no-free-variables e)
   (enough-annotations e)
   ---
   (well-formed e)])

(module+ test
  (test-case "well-formed:basic"
    (check-judgment-holds*
     (well-formed (+ 2 2))
     (well-formed (:: (fun f (x) 2) (→ Int Int)))
     (well-formed (let (x (:: (fun f (x) 2) (→ Int Int))) x))
     (well-formed (require (x (→ Int Int) (fun f (x) 2)) x))
    )
    (check-not-judgment-holds*
     (well-formed (+ x 2))
     (well-formed (fun f (x) 2))
     (well-formed (let (x (fun f (x) 2)) x))
     (well-formed (require (x (→ Int Int) (:: (fun f (x) 2) (→ Int Int))) x))
    )
    (void)))

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (closed-type I)
  #:contract (closed-type τ)
  [
   (free-type-variables τ ())
   ---
   (closed-type τ)])

(define-judgment-form TAG
  #:mode (free-type-variables I O)
  #:contract(free-type-variables τ α*)
  [
   ---
   (free-type-variables k0 ())]
  [
   (free-type-variables τ α*)
   ---
   (free-type-variables (k1 τ) α*)]
  [
   (free-type-variables τ_0 α*_0)
   (free-type-variables τ_1 α*_1)
   (where α* ,(set-union (term α*_0) (term α*_1)))
   ---
   (free-type-variables (k2 τ_0 τ_1) α*)]
  [
   ---
   (free-type-variables α (α))]
  [
   (free-type-variables τ α*_τ)
   (where α* ,(set-remove (term α*_τ) (term α)))
   ---
   (free-type-variables (∀ (α) τ) α*)])

(define-judgment-form TAG
  #:mode (no-free-variables I)
  #:contract (no-free-variables e)
  [
   (free-variables e ())
   ---
   (no-free-variables e)]
  [
   (free-variables e x*)
   (side-condition #false)
   ---
   (no-free-variables e)])

(define-judgment-form TAG
  #:mode (free-variables I O)
  #:contract (free-variables e x*)
  [
   (free-variables x x*)
   ---
   (free-variables (box x) x*)]
  [
   ---
   (free-variables integer ())]
  [
   ---
   (free-variables boolean ())]
  [
   (where (fun x_f (x) e) Λ)
   (free-variables e x*_Λ)
   (where x* ,(set-subtract (term x*_Λ) (term (x_f x))))
   ---
   (free-variables Λ x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x* ,(set-union (term x*_0) (term x*_1)))
   ---
   (free-variables (cons e_0 e_1) x*)]
  [
   ---
   (free-variables x (x))]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x* ,(set-union (term x*_0) (term x*_1)))
   ---
   (free-variables (e_0 e_1) x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (free-variables e_2 x*_2)
   (where x* ,(set-union (term x*_0) (term x*_1) (term x*_2)))
   ---
   (free-variables (if e_0 e_1 e_2) x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_pre1)
   (where x*_1 ,(set-remove (term x*_pre1) (term x)))
   (where x* ,(set-union (term x*_0) (term x*_1)))
   ---
   (free-variables (let (x e_0) e_1) x*)]
  [
   (free-variables Λ x*)
   ---
   (free-variables (:: Λ τ) x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_pre1)
   (where x*_1 ,(set-remove (term x*_pre1) (term x)))
   (where x* ,(set-union (term x*_0) (term x*_1)))
   ---
   (free-variables (require (x τ e_0) e_1) x*)]
  [
   (free-variables e x*)
   ---
   (free-variables (unop e) x*)]
  [
   (free-variables e_0 x*_0)
   (free-variables e_1 x*_1)
   (where x* ,(set-union (term x*_0) (term x*_1)))
   ---
   (free-variables (binop e_0 e_1) x*)])

(module+ test
  (test-case "closed:basic"
    (check-not-judgment-holds*
     (no-free-variables (+ x 5))
     (no-free-variables (if (= x 1) 1 (* x (fact (- x 1))))))
    (check-judgment-holds*
     (no-free-variables 3)
     (no-free-variables (fun f (x) 2))
     (no-free-variables (fun f (x) x))
     (no-free-variables (fun fact (x) (if (= x 1) 1 (* x (fact (- x 1))))))
     (no-free-variables (let (y (:: (fun f (x) x) (→ Int Int))) (y 4)))
     (no-free-variables (+ 3 3)))

    (check-judgment-holds*
     (closed-type Int)
     (closed-type Bool))

    (void)))

;; -----------------------------------------------------------------------------

(define-judgment-form TAG
  #:mode (enough-annotations I)
  #:contract (enough-annotations e)
  [
   (enough-annotations/typed e)
   ---
   (enough-annotations e)])

(define-judgment-form TAG
  #:mode (enough-annotations/typed I)
  #:contract (enough-annotations/typed e)
  [
   ---
   (enough-annotations/typed (box x))]
  [
   ---
   (enough-annotations/typed integer)]
  [
   ---
   (enough-annotations/typed boolean)]
  [
   (side-condition #false)
   ---
   (enough-annotations/typed Λ)]
  [
   (enough-annotations/typed e_0)
   (enough-annotations/typed e_1)
   ---
   (enough-annotations/typed (cons e_0 e_1))]
  [
   ---
   (enough-annotations/typed x)]
  [
   (enough-annotations/typed e_0)
   (enough-annotations/typed e_1)
   ---
   (enough-annotations/typed (e_0 e_1))]
  [
   (enough-annotations/typed e_0)
   (enough-annotations/typed e_1)
   (enough-annotations/typed e_2)
   ---
   (enough-annotations/typed (if e_0 e_1 e_2))]
  [
   (enough-annotations/typed e_0)
   (enough-annotations/typed e_1)
   ---
   (enough-annotations/typed (let (x e_0) e_1))]
  [
   (where (fun x_f (x) e) Λ)
   (enough-annotations/typed e)
   ---
   (enough-annotations/typed (:: Λ τ))]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/typed e_1)
   ---
   (enough-annotations/typed (require (x τ e_0) e_1))]
  [
   (enough-annotations/typed e)
   ---
   (enough-annotations/typed (unop e))]
  [
   (enough-annotations/typed e_0)
   (enough-annotations/typed e_1)
   ---
   (enough-annotations/typed (binop e_0 e_1))])

(define-judgment-form TAG
  #:mode (enough-annotations/untyped I)
  #:contract (enough-annotations/untyped e)
  [
   ---
   (enough-annotations/untyped (box x))]
  [
   ---
   (enough-annotations/untyped integer)]
  [
   ---
   (enough-annotations/untyped boolean)]
  [
   (where (fun x_f (x) e) Λ)
   (enough-annotations/untyped e)
   ---
   (enough-annotations/untyped Λ)]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/untyped e_1)
   ---
   (enough-annotations/untyped (cons e_0 e_1))]
  [
   ---
   (enough-annotations/untyped x)]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/untyped e_1)
   ---
   (enough-annotations/untyped (e_0 e_1))]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/untyped e_1)
   (enough-annotations/untyped e_2)
   ---
   (enough-annotations/untyped (if e_0 e_1 e_2))]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/untyped e_1)
   ---
   (enough-annotations/untyped (let (x e_0) e_1))]
  [
   (enough-annotations/untyped e)
   ---
   (enough-annotations/untyped (unop e))]
  [
   (enough-annotations/untyped e_0)
   (enough-annotations/untyped e_1)
   ---
   (enough-annotations/untyped (binop e_0 e_1))])

(module+ test
  (test-case "enough-annotations"
    (check-judgment-holds*
     (enough-annotations (+ 1 1))
     (enough-annotations (:: (fun f (x) x) (→ Int Int)))
     (enough-annotations (let (x 4) (+ x x)))
     (enough-annotations (require (x Int ((fun f (x) 1) 0)) x)))
    (check-not-judgment-holds*
     (enough-annotations (fun f (x) x))
     (enough-annotations (let (x (fun f (y) y)) (x 1))))
    (void)))

;; =============================================================================
;; === misc / helpers / util

(define-metafunction TAG
  type-env-ref : Γ x -> τ
  [(type-env-ref Γ x)
   ,(or
      (for/first ([xt (in-list (term Γ))]
                  #:when (equal? (term x) (car xt)))
        (cadr xt))
      (raise-arguments-error 'type-env-ref "unbound variable" "var" (term x) "env" (term Γ)))])

(define-metafunction TAG
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction TAG
  type-annotation : t -> τ
  [(type-annotation (:: _ τ))
   τ])

(define-metafunction TAG
  primop-type : primop -> τ
  [(primop-type +)
   (→ Int (→ Int Int))]
  [(primop-type -)
   (→ Int (→ Int Int))]
  [(primop-type *)
   (→ Int (→ Int Int))]
  [(primop-type =)
   (→ Int (→ Int Bool))]
  [(primop-type set-box!)
   (∀ (α) (→ (Box α) (→ α α)))]
  [(primop-type car)
   (∀ (α_0) (∀ (α_1) (→ (Pair α_0 α_1) α_0)))]
  [(primop-type cdr)
   (∀ (α_0) (∀ (α_1) (→ (Pair α_0 α_1) α_1)))]
  [(primop-type make-box)
   (∀ (α) (→ α (Box α)))]
  [(primop-type unbox)
   (∀ (α) (→ (Box α) α))])

(define-metafunction TAG
  apply-primop : [σ (primop vc ...)] -> A
  [(apply-primop [σ (car (cons vc_0 _))])
   [σ vc_0]]
  [(apply-primop [σ (cdr (cons _ vc_1))])
   [σ vc_1]]
  [(apply-primop [σ (make-box vc)])
   [σ_x (box x)]
   (where x #{fresh-location σ})
   (where σ_x #{runtime-env-set σ (x vc)})]
  [(apply-primop [σ (unbox (box x))])
   [σ vc]
   (where vc #{runtime-env-ref σ x})]
  [(apply-primop [σ (+ integer_0 integer_1)])
   [σ vc]
   (where vc ,(+ (term integer_0) (term integer_1)))]
  [(apply-primop [σ (- integer_0 integer_1)])
   [σ vc]
   (where vc ,(- (term integer_0) (term integer_1)))]
  [(apply-primop [σ (* integer_0 integer_1)])
   [σ vc]
   (where vc ,(* (term integer_0) (term integer_1)))]
  [(apply-primop [σ (= integer_0 integer_1)])
   [σ vc]
   (where vc ,(= (term integer_0) (term integer_1)))]
  [(apply-primop [σ (set-box! (box x) vc)])
   [σ_x vc]
   (where σ_x #{runtime-env-update σ (x vc)})])

(define-metafunction TAG
  apply-check : [σ (check K vc)] -> A
  [(apply-check [σ (check K vc)])
   A_next
   (where A_next [σ vc])
   (judgment-holds (value-check A_next K))]
  [(apply-check [σ (check K vc)])
   (CheckError K vc)])

(define-metafunction TAG
  runtime-env-set : σ (x vc) -> σ
  [(runtime-env-set σ (x vc))
   ,(cons (term (x vc)) (term σ))])

(define-metafunction TAG
  runtime-env-ref : σ x -> vc
  [(runtime-env-ref σ x)
   ,(or
      (for/first ([xv (in-list (term σ))]
                  #:when (equal? (car xv) (term x)))
        (cadr xv))
      (raise-arguments-error 'runtime-env-ref "unbound variable" "var" (term x) "env" (term σ)))])

(define-metafunction TAG
  runtime-env-update : σ (x vc) -> σ
  [(runtime-env-update σ (x vc))
   ,(let* ([success? (box #f)]
           [σ+ (for/list ([xv (in-list (term σ))])
                 (if (equal? (term x) (car xv))
                   (begin (set-box! success? #true) (term (x vc)))
                   xv))])
      (if (unbox success?)
        σ+
        (raise-arguments-error 'runtime-env-update "unbound variable" "var" (term x) "env" (term σ))))])

(define-metafunction TAG
  fresh-location : σ -> x
  [(fresh-location σ)
   any_0
   (where any_0 ,(variable-not-in (term σ) 'loc))])

(define-metafunction TAG
  fresh-type-variable : any -> α
  [(fresh-type-variable any)
   any_0
   (where any_0 ,(variable-not-in (term any) 'α))])

;; =============================================================================
;; === test

(module+ test
  (check α=?
    (term (:: (fun f (x) (:: x (Box Int))) (→ (Box Int) (Box Int))))
    (term (:: (fun f (x) (:: x (Box Int))) (→ (Box Int) (Box Int)))))

  (test-case "type-check"
    (check-mf-apply* #:is-equal? α=?
     [(type-check# 4)
      (:: 4 Int)]
     [(type-check# #false)
      (:: #false Bool)]
     [(type-check# #true)
      (:: #true Bool)]
     [(type-check# (:: (fun f (x) x) (→ (Box Int) (Box Int))))
      (:: (fun f (x) (:: x (Box Int))) (→ (Box Int) (Box Int)))]
     ;[(type-check# (:: (fun f (x) x) (→ (Box Bool) (Box Bool))))
     ; (:: (fun f (x) (:: x (Box Bool))) (→ (Box Bool) (Box Bool)))]
     [(type-check# (cons 1 1))
      (:: (cons (:: 1 Int) (:: 1 Int)) (Pair Int Int))]
     [(type-check# ((:: (fun f (x) 4) (→ Int Int)) 3))
      (:: ((:: (fun f (x) (:: 4 Int)) (→ Int Int)) (:: 3 Int)) Int)]
     [(type-check# (if 1 2 3))
      (:: (if (:: 1 Int) (:: 2 Int) (:: 3 Int)) Int)]
     [(type-check# (let (x 4) x))
      (:: (let (x (:: 4 Int)) (:: x Int)) Int)]
     [(type-check# (require (x Int 1) x))
      (:: (require (x Int 1) (:: x Int)) Int)]
     [(type-check# (car (cons 1 2)))
      (:: (car (:: (cons (:: 1 Int) (:: 2 Int)) (Pair Int Int))) Int)]
     [(type-check# (cdr (cons 2 1)))
      (:: (cdr (:: (cons (:: 2 Int) (:: 1 Int)) (Pair Int Int))) Int)]
     [(type-check# (make-box 3))
      (:: (make-box (:: 3 Int)) (Box Int))]
     [(type-check# (unbox (make-box 3)))
      (:: (unbox (:: (make-box (:: 3 Int)) (Box Int))) Int)]
     [(type-check# (+ 1 1))
      (:: (+ (:: 1 Int) (:: 1 Int)) Int)]
     [(type-check# (- 1 1))
      (:: (- (:: 1 Int) (:: 1 Int)) Int)]
     [(type-check# (* 1 1))
      (:: (* (:: 1 Int) (:: 1 Int)) Int)]
     [(type-check# (= 1 1))
      (:: (= (:: 1 Int) (:: 1 Int)) Bool)]
     [(type-check# (set-box! (make-box 2) 3))
      (:: (set-box! (:: (make-box (:: 2 Int)) (Box Int)) (:: 3 Int)) Int)])
    (void))

  (test-case "sound-elaboration"
    (check-judgment-holds*
     (sound-elaboration 4 (:: 4 Int))
     (sound-elaboration (:: (fun f (x) x) (→ Int Int))
                        (:: (fun f (x) (:: x Int)) (→ Int Int)))
     (sound-elaboration (+ 2 2) (:: (+ (:: 2 Int) (:: 2 Int)) Int))
     (sound-elaboration (make-box 3) (:: (make-box (:: 3 Int)) (Box Int))))
    (void))

  (test-case "erase-types"
    (check-mf-apply* #:is-equal? α=?
     [(erase-types# (:: 3 Int))
      3]
     [(erase-types# (:: (fun f (x) (:: 4 Int)) (→ Int Int)))
      (fun f (x) 4)])
    (void))
)

(module+ test
  (test-case "completion:basic"
    (check-mf-apply* #:is-equal? α=?
     [(completion# (:: 3 Int))
      3]
     [(completion# (:: #true Bool))
      #true]
     [(completion# (:: (fun f (x) (:: x Int)) (→ Int Int)))
      (fun f (x) x)]
     [(completion# (:: (cons (:: 1 Int) (:: (cons (:: 1 Int) (:: 2 Int)) (Pair Int Int))) (Pair Int (Pair Int Int))))
      (cons 1 (cons 1 2))]
     [(completion# (:: x Int))
      x]
     [(completion# (:: ((:: f (→ Int Int)) (:: 3 Int)) Int))
      (check Int (f 3))]
     [(completion# (:: (if (:: 1 Int) (:: 2 Int) (:: 3 Int)) Int))
      (if 1 2 3)]
     [(completion# (:: (let (x (:: 2 Int)) (:: x Int)) Int))
      (let (x 2) x)]
     [(completion# (:: (require (x Int 2) (:: x Int)) Int))
      (let (x (check Int 2)) x)]
     [(completion# (:: (unbox (:: (make-box (:: 1 Int)) (Box Int))) Int))
      (check Int (unbox (make-box 1)))]
     [(completion# (:: (+ (:: 1 Int) (:: 2 Int)) Int))
      (+ 1 2)])
    (void)))

(module+ test
  (test-case "eval:basic"
    (check-mf-apply*
     [(unload# (eval# 2))
      2]
     [(unload# (eval# ((fun f (x) x) 3)))
      3]
     [(unload# (eval# (if 1 2 3)))
      2]
     [(unload# (eval# (if #false 2 3)))
      3]
     [(unload# (eval# (let (x 2) x)))
      2]
     [(unload# (eval# (car (cons 1 2))))
      1]
     [(unload# (eval# (cdr (cons 1 2))))
      2]
     [(unload# (eval# (make-box 1)))
      (box 1)]
     [(unload# (eval# (unbox (make-box 1))))
      1]
     [(unload# (eval# (+ 2 2)))
      4]
     [(unload# (eval# (- 3 1)))
      2]
     [(unload# (eval# (* 4 4)))
      16]
     [(unload# (eval# (= 2 2)))
      #true]
     [(unload# (eval# (set-box! (make-box 3) 4)))
      4]
     [(unload# (eval# ((fun f (b) (if b b (f #true))) #false)))
      #true])
  (void)))

