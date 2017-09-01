#lang racket/base

;; "Between soundness and unsoundness, and what it means for performance."

;; Outline:
;; 1. AEXP is a dynamically typed language
;; 2. Adding an optional type system, AEXP-TYPED
;; 3. AEXP is not type sound
;; 4. How to enforce tag soundness, AEXP-TAGGED
;; 5. Claims about tag soundness
;; 6. How to enforce type soundness, AEXP-MONITORED
;; 7. Claims about AEXP-MONITORED
;; 7. Discussion
;; (Search for "=== Section N" to jump to a section of the outline)

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics)

(module+ test
  (require rackunit))

;; =============================================================================
;; === Section 1
;; =============================================================================

;; AEXP is a dynamically typed language for arithmetic expressions.
(define-language AEXP
  (a ::= v x (let (x a) a) (δ a ...))

  ;; Values are integers and locations
  (v ::= integer (box x))

  ;; Primitive operations work on the bit-level representation of values
  ;; These are unsafe, evaluation might get stuck.
  (δ ::= + make-box set-box! unbox)

  ;; To avoid stuck states, AEXP has a target language with a general
  ;;  form for dynamic checks.
  ;; (A smart compiler could add the fewest checks necessary.)
  (c ::= v x (let (x c) c) (δ c ...) (assert k c))

  ;; The `assert` form checks "machine tags"
  (k ::= int box)

  ;; Evaluation is defined on compiled terms,
  ;;  and may yield either a result state or a runtime error
  (A ::= [σ c] RuntimeError)
  (σ ::= ((x v) ...))
  (RuntimeError ::= (Assert k v))
  (E ::= hole (let (x E) c) (δ v ... E c ...) (assert k E))

  (x ::= variable-not-otherwise-mentioned)

  #:binding-forms
  (let (x a_x) a #:refers-to x)
  (let (x c_x) c #:refers-to x))

(define (α=? t0 t1)
  (alpha-equivalent? AEXP t0 t1))

;; -----------------------------------------------------------------------------
;; the `eval` metafunction:
;; - compiles a source term
;; - applies a reduction relation
;; - "unloads" the result by substituting the value of any locations in the result

(define-metafunction AEXP
  eval : a -> any
  [(eval a)
   (unload A_final)
   (where A_init (pre-eval a))
   (where (A_final natural_num-steps) (-->AEXP* A_init))])

(define-metafunction AEXP
  pre-eval : a -> A
  [(pre-eval a)
   [() c]
   (where c (compile a))])

(module+ test
  (test-case "eval"
    (check-true
      (redex-match? AEXP 4
        (term (eval (+ 2 2)))))
    (check-true
      (redex-match? AEXP (Assert int (box _))
        (term (eval (+ 2 (make-box 2))))))))

;; -----------------------------------------------------------------------------
;; the `compile` metafunction translates source terms to core terms
;; by adding checks to enforce primitive operations assumptions

(define-metafunction AEXP
  compile : a -> c
  [(compile a)
   c
   (judgment-holds (dynamic-completion a c))
   (judgment-holds (sound-completion a c))])

;; "completion" is a reference to Henglein.
;; The completion of a source term is the same term with added dynamic checks.
;; `dynamic-completion` adds checks to protect `+` `unbox` and `set-box!`
(define-judgment-form AEXP
  #:mode (dynamic-completion I O)
  #:contract (dynamic-completion a c)
  [
   ---
   (dynamic-completion v v)]
  [
   ---
   (dynamic-completion x x)]
  [
   (dynamic-completion a_x c_x)
   (dynamic-completion a c)
   ---
   (dynamic-completion (let (x a_x) a) (let (x c_x) c))]
  [
   (dynamic-completion a_0 c_0)
   (dynamic-completion a_1 c_1)
   (where c_0+ (assert int c_0))
   (where c_1+ (assert int c_1))
   ---
   (dynamic-completion (+ a_0 a_1) (+ c_0+ c_1+))]
  [
   (dynamic-completion a c)
   ---
   (dynamic-completion (make-box a) (make-box c))]
  [
   (dynamic-completion a_0 c_0)
   (dynamic-completion a_1 c_1)
   (where c_0+ (assert box c_0))
   ---
   (dynamic-completion (set-box! a_0 a_1) (set-box! c_0+ c_1))]
  [
   (dynamic-completion a_0 c_0)
   (where c_0+ (assert box c_0))
   ---
   (dynamic-completion (unbox a_0) (unbox c_0+))])

(define-judgment-form AEXP
  #:mode (sound-completion I I)
  #:contract (sound-completion a c)
  [
   (where a_c (erase-asserts c))
   (side-condition ,(α=? (term a) (term a_c)))
   ---
   (sound-completion a c)])

;; -----------------------------------------------------------------------------
;; helper functions

(define-metafunction AEXP
  erase-asserts : any -> any
  [(erase-asserts (assert k c))
   (erase-asserts c)]
  [(erase-asserts (any ...))
   ((erase-asserts any) ...)]
  [(erase-asserts any)
   any])

(define-metafunction AEXP
  unload : A -> any
  [(unload RuntimeError)
   RuntimeError]
  [(unload [σ integer])
   integer]
  [(unload [σ (box x)])
   (box (unload σ x))])

(define -->AEXP
  (reduction-relation AEXP
   #:domain A
   [-->
    [σ (in-hole E (let (x v) c))]
    [σ (in-hole E c_x)]
    E-Let
    (where c_x (substitute c x v))]
   [-->
    [σ (in-hole E (δ v ...))]
    [σ_res (in-hole E v_res)]
    E-Delta
    (where [σ_res v_res] (apply-primop δ σ v ...))]
   [-->
    [σ (in-hole E (assert k v))]
    [σ (in-hole E v)]
    E-AssertSuccess
    (judgment-holds (do-assert v k))]
   [-->
    [σ (in-hole E (assert k v))]
    (Assert k v)
    E-AssertFailure
    (side-condition (not (judgment-holds (do-assert v k))))]))

;; Apply reduction relation `-->AEXP` to a term, count the number of steps
(define-metafunction AEXP
  -->AEXP* : A -> (A natural)
  [(-->AEXP* A)
   ,(reflexive-transitive-closure/count-steps -->AEXP (term A))])

(define-metafunction AEXP
  apply-primop : δ σ v ... -> [σ v]
  [(apply-primop + σ integer_0 integer_1)
   [σ ,(+ (term integer_0) (term integer_1))]]
  [(apply-primop make-box σ v)
   [σ_res (box x)]
   (where x (fresh-location σ))
   (where σ_res (runtime-env-set σ x v))]
  [(apply-primop set-box! σ (box x) v)
   [σ_res v]
   (where σ_res (runtime-env-set σ x v))]
  [(apply-primop unbox σ (box x))
   [σ v]
   (where v (runtime-env-ref σ x))])

(define-metafunction AEXP
  fresh-location : σ -> x
  [(fresh-location σ)
   ,(variable-not-in (term σ) 'loc)])

(define-metafunction AEXP
  runtime-env-set : σ x v -> σ
  [(runtime-env-set ((x_first v_first) ... (x v_old) (x_rest v_rest) ...) x v)
   ((x_first v_first) ... (x v) (x_rest v_rest) ...)]
  [(runtime-env-set ((x_rest v_rest) ...) x v)
   ((x v) (x_rest v_rest) ...)])

(define-metafunction AEXP
  runtime-env-ref : σ x -> v
  [(runtime-env-ref ((x_first v_first) ... (x v) (x_rest v_rest) ...) x)
   v])

(define-judgment-form AEXP
  #:mode (do-assert I I)
  #:contract (do-assert v k)
  [
   ---
   (do-assert integer int)]
  [
   ---
   (do-assert (box _) box)])

(define-syntax-rule (reflexive-transitive-closure/count-steps --> t)
  (let loop ([curr-A t]
             [num-steps 0])
    (define next-A* (apply-reduction-relation --> curr-A))
    (cond
     [(null? next-A*)
      (list curr-A num-steps)]
     [(null? (cdr next-A*))
      (loop (car next-A*) (+ num-steps 1))]
     [else
      (raise-arguments-error (string->symbol (format "~a*" (object-name -->))) "non-deterministic reduction"
        "current-term" curr-A
        "next-terms" next-A*)])))

;; =============================================================================
;; === Section 2
;; =============================================================================

;; AEXP is a simple language, but a static type system can offer some benefits:
;; + [T0] detect errors at compile-time instead of at run-time
;;        (furthermore, rule out a class of runtime errors)
;; + [T1] remove the need for some "asserts"
;;        (i.e. programs run faster)
;; + [T2] help programmers reason about code
;;        (with a type soundness guarantee)

;; AEXP-TYPED adds a simple, optional type system to AEXP
;; It provides benefits T1 and T2, but not T3.

(define-extended-language AEXP-TYPED
  AEXP

  (τ ::= (Box τ) Int Nat)
  (Γ ::= ((x τ) ...))

  ;; New source term `dyn` is like `let`, but the binding is not type checked.
  ;; Similar to Typed Racket's `require/typed`,
  ;;  except the bound expression is evaluated in scope of previous definitions.
  (a ::= .... (dyn (x τ a) a))

  ;; Type-annotated source terms
  (t ::= (:: v τ) (:: x τ) (:: (let (x t) t) τ) (:: (δ t ...) τ) (:: (dyn (x τ a) t) τ))

  ;; The type checker can catch errors at compile-time
  (TypeError ::= (Type a))
  (maybe-A ::= A TypeError)
  (maybe-t ::= t TypeError)

  #:binding-forms
  (:: (let (x t_x) t #:refers-to x) τ)
  (:: (dyn (x τ_x t_x) t #:refers-to x) τ))

;; -----------------------------------------------------------------------------
;; the `eval-typed` metafunction:
;; - type checks a source term
;; - compiles the term to core syntax
;; - evaluates the core term using the AEXP reduction relation

(define-metafunction AEXP-TYPED
  eval-typed : a -> any
  [(eval-typed a)
   (unload A_final)
   (where A_init (pre-eval-typed a))
   (where (A_final natural_num-steps) (-->AEXP* A_init))]
  [(eval-typed a)
   TypeError
   (where TypeError (pre-eval-typed a))])

(define-metafunction AEXP-TYPED
  pre-eval-typed : a -> maybe-A
  [(pre-eval-typed a)
   TypeError
   (where TypeError (type-check a))]
  [(pre-eval-typed a)
   [() c]
   (where t (type-check a))
   (where c (compile-typed-unsound t))])

(module+ test
  (test-case "eval-typed"
    (check-equal?
      (term (eval-typed (+ 2 2)))
      (term 4))
    (check-equal?
      (term (eval-typed (let (x 2) (dyn (y Nat 2) (+ x y)))))
      (term 4))))

;; -----------------------------------------------------------------------------
;; The following "theorems" argue that AEXP-TYPED provides benefits T0 and T1

;; Claim: there exists an AEXP term that
;; 1. evaluates to a RuntimeError
;; 2. fails to type check
;; Consequence: the type system can catch errors ahead of time
(define-metafunction AEXP-TYPED
  theorem:T0-0 : a -> boolean
  [(theorem:T0-0 a)
   #true
   (where TypeError (pre-eval-typed a))
   (where A_init (pre-eval a))
   (where (RuntimeError _) (-->AEXP* A_init))]
  [(theorem:T0-0 a)
   #false])

(module+ test
  (test-case "theorem:T0-0"
    (check-true
      (term (theorem:T0-0 (+ 2 (make-box 2)))))))

;; Claim: if a term type-checks, then it reduces without error
(define-metafunction AEXP-TYPED
  theorem:T0-1 : a -> boolean
  [(theorem:T0-1 a)
   #true
   (where TypeError (pre-eval-typed a))]
  [(theorem:T0-1 a)
   #true
   (where A_init (pre-eval-typed a))
   (judgment-holds (fully-typed a))
   (where (A_final _) (-->AEXP* A_init))])

(define-judgment-form AEXP-TYPED
  #:mode (fully-typed I)
  #:contract (fully-typed a)
  [
   ---
   (fully-typed v)]
  [
   ---
   (fully-typed x)]
  [
   (fully-typed a_x)
   (fully-typed a)
   ---
   (fully-typed (let (x a_x) a))]
  [
   (fully-typed a) ...
   ---
   (fully-typed (δ a ...))])

(module+ test
  (test-case "theorem:T0-1"
    ;; TODO more tests
    (check-true
      (term (theorem:T0-1 (+ 2 2))))))

;; Claim: for all AEXP terms `a`, if:
;; Premise 1. `(pre-eval a)` and `(pre-eval-typed a)` are defined
;; Premise 2. `(-->AEXP* (pre-eval a))` and `(-->AEXP* (pre-eval-typed a))`
;;            reduce without error,
;; then:
;; 1. the typed version evaluates in fewer steps
(define-metafunction AEXP-TYPED
  theorem:T1 : a -> boolean
  [(theorem:T1 a)
   ,(<= (term natural_typed) (term natural_dyn))
   (where A_typed (pre-eval-typed a))
   (where A_dyn (pre-eval a))
   (where (A_final natural_typed) (-->AEXP* A_typed))
   (where (A_final natural_dyn) (-->AEXP* A_dyn))]
  [(theorem:T1 a)
   #true
   (where A_typed (pre-eval-typed a))
   (where (RuntimeError _) (-->AEXP* A_typed))]
  [(theorem:T1 a)
   #true
   (where TypeError (pre-eval-typed a))]
  [(theorem:T1 a)
   #true
   (where (RuntimeError _) (-->AEXP* A_dyn))])

(module+ test
  (test-case "theorem:T1"
    (check-true
      (term (theorem:T1 (+ 2 2))))))

;; -----------------------------------------------------------------------------
;; static type checking

(define-metafunction AEXP-TYPED
  type-check : a -> maybe-t
  [(type-check a)
   t
   (judgment-holds (well-typed () a t))]
  [(type-check a)
   (Type a)])

(define-judgment-form AEXP-TYPED
  #:mode (well-typed I I O)
  #:contract (well-typed Γ a t)
  [
   --- T-Nat
   (well-typed Γ natural (:: natural Nat))]
  [
   (side-condition ,(< (term integer) 0))
   --- T-Int
   (well-typed Γ integer (:: integer Int))]
  [
   (where τ (type-env-ref Γ x))
   --- T-Var
   (well-typed Γ x (:: x τ))]
  [
   (well-typed Γ a_x t_x)
   (where τ_x (type-annotation t_x))
   (where Γ_x (type-env-set Γ x τ_x))
   (well-typed Γ_x a t)
   (where τ (type-annotation t))
   --- T-Let
   (well-typed Γ (let (x a_x) a) (:: (let (x t_x) t) τ))]
  [
   (well-typed Γ a t) ...
   (where (τ_arg ...) ((type-annotation t) ...))
   (where τ (primop-codomain δ τ_arg ...))
   --- T-Primop
   (well-typed Γ (δ a ...) (:: (δ t ...) τ))]
  [
   (where Γ_x (type-env-set Γ x τ_x))
   (well-typed Γ_x a t)
   (where τ (type-annotation t))
   --- T-Dyn
   (well-typed Γ (dyn (x τ_x a_x) a) (:: (dyn (x τ_x a_x) t) τ))])

(define-metafunction AEXP-TYPED
  primop-codomain : δ τ ... -> any
  [(primop-codomain + Nat Nat)
   Nat]
  [(primop-codomain + Int Nat)
   Int]
  [(primop-codomain + Nat Int)
   Int]
  [(primop-codomain + Int Int)
   Int]
  [(primop-codomain make-box τ)
   (Box τ)]
  [(primop-codomain set-box! (Box τ_0) τ_1)
   τ_1]
  [(primop-codomain unbox (Box τ))
   τ]
  [(primop-codomain _ ...)
   ;; type error, to prevent T-Primop from succeeding
   #f])

;; -----------------------------------------------------------------------------
;; well typed values, [σ v] ⊨ τ
;; (this is important later)

(define-judgment-form AEXP-TYPED
  #:mode (well-typed-value I I)
  #:contract (well-typed-value [σ v] τ)
  [
   ---
   (well-typed-value [_ integer] Int)]
  [
   ---
   (well-typed-value [_ natural] Nat)]
  [
   (where v (runtime-env-ref σ x))
   (well-typed-value [σ v] τ)
   ---
   (well-typed-value [σ (box x)] (Box τ))])

;; -----------------------------------------------------------------------------
;; compile-typed-unsound

;; This compiler is unsound because it assumes all annotations
;;  on dynamically typed code (i.e. all `τ` in `dyn`-expressions)
;;  are correct.

(define-metafunction AEXP-TYPED
  compile-typed-unsound : t -> c
  [(compile-typed-unsound t)
   c
   (judgment-holds (typed-unsound-completion t c))
   (where a (erase-types t))
   (judgment-holds (sound-completion a c))])

(module+ test
  (test-case "compile-typed-unsound"
    (define t
      (term (:: (dyn (x Nat -2) (:: (+ (:: x Nat) (:: x Nat)) Nat)) Nat)))
    (define c
      (term (let (x -2) (+ x x))))

    (check-true
      (redex-match? AEXP-TYPED t t))
    (define a (term (erase-types ,t)))
    (check-equal? a c)
    (check-true (redex-match? AEXP-TYPED a a))
    (check-true
      (judgment-holds (sound-completion (erase-types ,t) ,c)))
    (check-true (redex-match? AEXP-TYPED c (term (compile-typed-unsound ,t))))
    (void)))

(define-judgment-form AEXP-TYPED
  #:mode (typed-unsound-completion I O)
  #:contract (typed-unsound-completion t c)
  [
   --- TUC-Val
   (typed-unsound-completion (:: v τ) v)]
  [
   --- TUC-Var
   (typed-unsound-completion (:: x τ) x)]
  [
   (typed-unsound-completion t_x c_x)
   (typed-unsound-completion t c)
   --- TUC-Let
   (typed-unsound-completion (:: (let (x t_x) t) τ) (let (x c_x) c))]
  [
   (typed-unsound-completion t c) ...
   ---
   (typed-unsound-completion (:: (δ t ...) τ) (δ c ...))]
  [
   (dynamic-completion a_x c_x)
   (typed-unsound-completion t c)
   ---
   (typed-unsound-completion (:: (dyn (x τ_x a_x) t) τ) (let (x c_x) c))])

;; -----------------------------------------------------------------------------
;; helper functions, tests

(define-metafunction AEXP-TYPED
  type-env-ref : Γ x -> τ
  [(type-env-ref ((x_first τ_first) ... (x τ) (x_rest τ_rest) ...) x)
   τ])

(define-metafunction AEXP-TYPED
  type-env-set : Γ x τ -> Γ
  [(type-env-set ((x_first τ_first) ... (x τ_old) (x_rest τ_rest) ...) x)
   ((x_first τ_first) ... (x τ) (x_rest τ_rest) ...)]
  [(type-env-set ((x_rest τ_rest) ...) x τ)
   ((x τ) (x_rest τ_rest) ...)])

(define-metafunction AEXP-TYPED
  type-annotation : t -> τ
  [(type-annotation (:: _ τ))
   τ])

(define-metafunction AEXP-TYPED
  erase-types : any -> any
  [(erase-types (:: any τ))
   (erase-types any)]
  [(erase-types (dyn (x τ any_x) any))
   (let (x any_x) (erase-types any))]
  [(erase-types (any ...))
   ((erase-types any) ...)]
  [(erase-types any)
   any])

(module+ test
  (test-case "primop-codomain"
    (check-equal?
      (term (primop-codomain + Int Int))
      (term Int))
    (check-equal?
      (term (primop-codomain + Nat Nat))
      (term Nat))
    (check-equal?
      (term (primop-codomain make-box (Box Int)))
      (term (Box (Box Int))))
    (check-equal?
      (term (primop-codomain set-box! (Box Int) Int))
      (term Int))
    (check-equal?
      (term (primop-codomain unbox (Box (Box Int))))
      (term (Box Int))))

  (test-case "type-check"
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check 2))))
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check -2))))
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check (let (x 4) x)))))
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check (+ 2 2)))))
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check (dyn (x Int (make-box 4)) (+ x 1))))))
    (check-true (redex-match? AEXP-TYPED t
      (term (type-check (make-box 2)))))

    (check-true (redex-match? AEXP-TYPED TypeError
      (term (type-check (+ 2 (make-box 2))))))))

;; =============================================================================
;; === Section 3
;; =============================================================================

;; A "classic" type soundness claim for AEXP-TYPED is:
;;
;;   If `a` has the static type `τ` and compiles to the core term `c`,
;;   then evaluating `c` will result in one of two outcomes:
;;   1. `c` reduces to a final state `[σ v]` 
;;      and `[σ v] ⊨ τ`
;;   2. `c` reduces to an assert error due to an untyped subterm
;;
;; Here is a counterexample to the theorem

(define-metafunction AEXP-TYPED
  counterexample:classic-soundness : a -> boolean
  [(counterexample:classic-soundness a)
   ,(not (judgment-holds (well-typed-value A_final τ)))
   (where τ (type-annotation (type-check a)))
   (where A_init (pre-eval-typed a))
   (where (A_final _) (-->AEXP* A_init))])

(module+ test
  (test-case "classic-soundness-counterexample"
    (check-true
      (term (counterexample:classic-soundness (dyn (x Nat -2) (+ x x)))))))

;; =============================================================================
;; === Section 4
;; =============================================================================

;; "Classic" soundness does not hold for the "unsound" compiler because
;;  that compiler assumes the type annotations on `dyn` terms are correct.
;; This is a bad assumption.
;;
;; How to remove the assumption?
;; 1. Remove all dynamically typed code
;; 2. Add run-time checks
;;
;; How to add run-time checks?
;; - One idea, use `assert` from the core language.
;;   This doesn't work because we have a type `Nat`
;;    that doesn't correspond to a machine tag `k`
;; - Second idea, add a generalized kind of tag so there is one tag
;;   for each logical type.
;;
;; This section explores the "generalized tag" idea,
;;  shows it satisfies a kind of soundness,
;;  and shows that the soundness is NOT classic type soundness.

(define-extended-language AEXP-TAGGED
  AEXP-TYPED

  (K ::= Int Nat Box)

  (c ::= .... (check K c))
  (E ::= .... (check K E))
  (RuntimeError ::= .... (Check K v)))

(define-metafunction AEXP-TAGGED
  eval-tagged : a -> any
  [(eval-tagged a)
   (unload A_final)
   (where A_init (pre-eval-tagged a))
   (where (A_final natural_num-steps) (-->AEXP-TAGGED* A_init))]
  [(eval-tagged a)
   TypeError
   (where TypeError (pre-eval-tagged a))])

(define-metafunction AEXP-TAGGED
  pre-eval-tagged : a -> maybe-A
  [(pre-eval-tagged a)
   TypeError
   (where TypeError (type-check a))]
  [(pre-eval-tagged a)
   [() c]
   (where t (type-check a))
   (where c (compile-tagged t))])

(define -->AEXP-TAGGED
  (extend-reduction-relation -->AEXP
   AEXP-TAGGED
   [-->
    [σ (in-hole E (check K v))]
    [σ (in-hole E v)]
    E-CheckSuccess
    (judgment-holds (well-tagged-value v K))]
   [-->
    [σ (in-hole E (check K v))]
    (Check K v)
    E-CheckFailure
    (side-condition (not (judgment-holds (well-tagged-value v K))))]))

(define-metafunction AEXP-TAGGED
  -->AEXP-TAGGED* : A -> (A natural)
  [(-->AEXP-TAGGED* A)
   ,(reflexive-transitive-closure/count-steps -->AEXP-TAGGED (term A))])

(module+ test
  (test-case "eval-tagged"
    (check-equal?
      (term (eval-tagged (+ 2 2)))
      (term 4))
    (check-equal?
      (term (eval-tagged (let (x 2) (dyn (y Nat 2) (+ x y)))))
      (term 4))))

;; -----------------------------------------------------------------------------
;; compile-tagged

;; This compiler preserves tag soundness by defending
;;  typed expressions from possibly-untyped code.
;; 1. Check `dyn`-expressions
;;   `(dyn (x τ a) t)` ===> `(let (x (check K a)) t)`
;; 2. Check the results of unbox, since dynamically typed code may
;;    have created or written to the box
;;   `(unbox t)` ===> `(check K (unbox t))`
;; The general principle is to add a tag check at every point
;;  where dynamically-typed code might enter typed code.

(define-metafunction AEXP-TAGGED
  compile-tagged : t -> c
  [(compile-tagged t)
   c
   (judgment-holds (tagged-completion t c))
   (where a (erase-types t))
   (judgment-holds (sound-completion-tagged a c))])

;; Need a new copy of this metafunction because `c` has new meaning
(define-judgment-form AEXP-TAGGED
  #:mode (sound-completion-tagged I I)
  #:contract (sound-completion-tagged a c)
  [
   (where a_c (erase-checks (erase-asserts c)))
   (side-condition ,(α=? (term a) (term a_c)))
   ---
   (sound-completion-tagged a c)])

(define-judgment-form AEXP-TAGGED
  #:mode (tagged-completion I O)
  #:contract (tagged-completion t c)
  [
   ---
   (tagged-completion (:: v _) v)]
  [
   ---
   (tagged-completion (:: x _) x)]
  [
   (tagged-completion t_x c_x)
   (tagged-completion t c)
   ---
   (tagged-completion (:: (let (x t_x) t) _) (let (x c_x) c))]
  [
   (eliminator? δ)
   (tagged-completion t c) ...
   (where K (tag-of τ))
   ---
   (tagged-completion (:: (δ t ...) τ) (check K (δ c ...)))]
  [
   (side-condition ,(not (judgment-holds (eliminator? δ))))
   (tagged-completion t c) ...
   ---
   (tagged-completion (:: (δ t ...) τ) (δ c ...))]
  [
   (dynamic-completion a_x c_x)
   (where K (tag-of τ_x))
   (where c_check (check K c_x))
   (tagged-completion t c)
   ---
   (tagged-completion (:: (dyn (x τ_x a_x) t) _) (let (x c_check) c))])

(define-judgment-form AEXP-TAGGED
  #:mode (eliminator? I)
  #:contract (eliminator? δ)
  [
   ---
   (eliminator? unbox)])

(define-metafunction AEXP-TAGGED
  tag-of : τ -> K
  [(tag-of K)
   K]
  [(tag-of (Box _))
   Box])

(module+ test
  (test-case "compile-tagged"
    (define t (term (:: (let (x (:: 2 Nat))
                      (:: (dyn (y Nat 2)
                        (:: (+ (:: x Nat) (:: y Nat)) Nat)) Nat)) Nat)))
    (check-true
      (redex-match? AEXP-TAGGED t t))
    (define a (term (erase-types ,t)))
    (check-true
      (redex-match? AEXP-TAGGED a a))
    (define c (term (compile-tagged ,t)))
    (check-true
      (redex-match? AEXP-TAGGED c c))
    (void)))

;; -----------------------------------------------------------------------------
;; helpers, other tests

(define-judgment-form AEXP-TAGGED
  #:mode (well-tagged-value I I)
  #:contract (well-tagged-value v K)
  [
   ---
   (well-tagged-value natural Nat)]
  [
   ---
   (well-tagged-value integer Int)]
  [
   ---
   (well-tagged-value (box _) Box)])

(define-metafunction AEXP-TAGGED
  erase-checks : any -> any
  [(erase-checks (check K c))
   (erase-checks c)]
  [(erase-checks (any ...))
   ((erase-checks any) ...)]
  [(erase-checks any)
   any])

;; =============================================================================
;; === Section 5
;; =============================================================================

;; AEXP-TAGGED satisfies a notion of tag soundness:
;;
;;  If `a` is well typed at `τ` and compiles to `c`, then either:
;;  - `a` reduces to `[σ v]` such that `[σ v] ⊨ K`
;;  - `a` reduces to an Assert error in dynamically typed code
;;  - `a` reduces to a Check error because of a failed tag check
;;    TODO can we say more about how these tag checks might fail?

;; Claim: exists a term that
;; - reduces to an ill-tagged value when unsound
;; - reduces to a Check error when tag-sound
(define-metafunction AEXP-TAGGED
  example:tagged-is-not-unsound : a -> boolean
  [(example:tagged-is-not-unsound a)
   ,(not (judgment-holds (well-typed-value A_final τ)))
   (where τ (type-annotation (type-check a)))
   (where A_unsound (pre-eval-typed a))
   (where (A_final _) (-->AEXP* A_unsound))
   (where c_dyn (compile (erase-types a)))
   (where (A_dyn _) (-->AEXP* [() c_dyn]))
   (where A_tagged (pre-eval-tagged a))
   (where ((Check _ _) _) (-->AEXP-TAGGED* A_tagged))])

(module+ test
  (test-case "tagged-is-better-than-unsound"
    (check-true
      (term (example:tagged-is-not-unsound (dyn (x Nat -2) (+ x x)))))))

;; AEXP-TAGGED is tag-sound, but not type sound.
;; Proof: there is a term with static type `τ` that reduces to a `[σ v]`
;;  such that `[σ v] ⊨ τ` is NOT true.

(define-metafunction AEXP-TAGGED
  counterexample:generalized-soundness : a -> boolean
  [(counterexample:generalized-soundness a)
   ,(not (judgment-holds (well-typed-value [σ v] τ)))
   (where τ (type-annotation (type-check a)))
   (where A_init (pre-eval-tagged a))
   (where ([σ v] _) (-->AEXP-TAGGED* A_init))])

(module+ test
  (check-true
    (term (counterexample:generalized-soundness
      (dyn (x (Box Nat) (make-box (make-box -1))) x)))))

;; Claim: for all AEXP term with no dynamic typing and no unbox operations,
;;  tagged evaluation and unsound evaluation take the same number of steps.
(define-metafunction AEXP-TAGGED
  example:tagged-sometimes-fast : a -> boolean
  [(example:tagged-sometimes-fast a)
   ,(= (term natural_unsound) (term natural_tagged))
   (where A_unsound (pre-eval-typed a))
   (where A_tagged (pre-eval-tagged a))
   (where (A_final natural_unsound) (-->AEXP* A_unsound))
   (where (A_final natural_tagged) (-->AEXP-TAGGED* A_tagged))])

(module+ test
  (test-case "tagged-sometimes-fast"
    (check-true
      (term (example:tagged-sometimes-fast (+ 2 2))))
    (check-true
      (term (example:tagged-sometimes-fast (let (x 1) (let (y 2) (+ x (+ y y)))))))))

;; Claim: for all AEXP terms with at least one `dyn` or `unbox`,
;;  tagged evaluation is slower than unsound
(define-metafunction AEXP-TAGGED
  example:tagged-sometimes-slow : a -> boolean
  [(example:tagged-sometimes-slow a)
   ,(< (term natural_unsound) (term natural_tagged))
   (where A_unsound (pre-eval-typed a))
   (where A_tagged (pre-eval-tagged a))
   (where (A_final natural_unsound) (-->AEXP* A_unsound))
   (where (A_final natural_tagged) (-->AEXP-TAGGED* A_tagged))])

(module+ test
  (test-case "tagged-sometimes-slow"
    (check-true
      (term (example:tagged-sometimes-slow (unbox (make-box 2)))))))

;; =============================================================================
;; === Section 6
;; =============================================================================

;; How to get type soundness?
;; - For the AEXP language, we could do "deep tag checks"
;;   on every value in σ every time control enters typed code.
;;   This will break down if the language adds "infinite" values like functions
;;    or streams.
;;   Also, checking the entire heap every time control changes from untyped-to-typed
;;    will hurt performance.
;; - Idea 2 is to monitor higher-order values.
;;   For AEXP, this means we guard typed boxes against dynamically typed code

;; A monitor is a new kind of value that protects an existing value.
;; In general, need one monitor for each "higher-order" value in the language.
;; In AEXP, the only higher-order value is the box.

(define-judgment-form AEXP
  #:mode (higher-order-value I)
  #:contract (higher-order-value v)
  [
   ---
   (higher-order-value (box _))])

(module+ test
  (test-case "higher-order-value"
    (check-true (judgment-holds (higher-order-value (box x))))
    (check-false (judgment-holds (higher-order-value 2)))))

;; To implement monitors:
;; 1. extend the value forms
;; 2. extend the core language
;; 3. extend the reduction relation with new rules for the new monitors
;; 4. extend the compiler to make monitors instead of checks

;; -----------------------------------------------------------------------------

(define-extended-language AEXP-MONITORED
  AEXP-TAGGED
  (c ::= .... (mon τ c))
  (E ::= .... (mon τ E)))

(module+ test
  (check α=?
    (term (let (x 1) x))
    (term (let (y 1) y))))

(define -->AEXP-MONITORED
  (extend-reduction-relation -->AEXP-TAGGED
   ;; extends 'TAGGED' to inherit (check ....)
   AEXP-MONITORED
   [-->
    [σ (in-hole E (let (x c_x) c))]
    [σ c_subst]
    E-LetMon
    (where (mon (Box τ) (box x_loc)) c_x)
    (where c_subst (substitute c x c_x))]
   [-->
    [σ (in-hole E (set-box! (mon (Box τ) (box x)) v))]
    [σ (in-hole E (set-box! (box x) (mon τ v)))]
    E-MonSet]
   [-->
    [σ (in-hole E (unbox (mon (Box τ) (box x))))]
    [σ (in-hole E (mon τ (unbox (box x))))]
    E-MonUnbox]))

(define-metafunction AEXP-MONITORED
  -->AEXP-MONITORED* : A -> (A natural)
  [(-->AEXP-MONITORED* A)
   ,(reflexive-transitive-closure/count-steps -->AEXP-MONITORED (term A))])

(module+ test
  (test-case "-->AEXP-MONITORED*"
    (check-false
      (redex-match? AEXP-MONITORED v (term (mon Nat 2))))
    (check-true
      (redex-match? AEXP-MONITORED A (term [() (check Nat 2)])))
    (check-equal?
      (term (-->AEXP-MONITORED* [() (let (y (check Nat 2)) (+ 2 y))]))
      (term ([() 4] 3)))
    (check-equal?
      ;; only monitor boxes
      (term (-->AEXP-MONITORED* [() (mon Nat 2)]))
      (term ([() (mon Nat 2)] 0)))
    (check-equal?
      (term (-->AEXP-MONITORED* [() (let (y (check Nat 2)) (+ 2 y))]))
      (term ([() 4] 3)))))

;; -----------------------------------------------------------------------------

(define-metafunction AEXP-MONITORED
  eval-monitored : a -> any
  [(eval-monitored a)
   (unload-monitored A_final)
   (where A_init (pre-eval-monitored a))
   (where (A_final _) (-->AEXP-MONITORED* A_init))]
  [(eval-monitored a)
   TypeError
   (where TypeError (pre-eval-monitored a))])

(define-metafunction AEXP-MONITORED
  pre-eval-monitored : a -> maybe-A
  [(pre-eval-monitored a)
   TypeError
   (where TypeError (type-check a))]
  [(pre-eval-monitored a)
   [() c]
   (where t (type-check a))
   (where c (compile-monitored t))])

(define-metafunction AEXP-MONITORED
  unload-monitored : A -> any
  [(unload-monitored RuntimeError)
   RuntimeError]
  [(unload-monitored [σ integer])
   integer]
  [(unload-monitored [σ (box x)])
   (box (unload-monitored σ x))]
  [(unload-monitored [σ (mon τ v)])
   (mon τ (unload-monitored [σ v]))])

(module+ test
  (test-case "eval-monitored"
    (check-equal?
      (term (eval-monitored (+ 2 2)))
      (term 4))
    (check-equal?
      (term (eval-monitored (let (x 2) (dyn (y Nat 2) (+ x y)))))
      (term 4))
    (check-equal?
      (term (eval-monitored
        (let (b (make-box 1))
          (dyn (y Nat (set-box! b 2))
            (let (z (unbox b))
              (+ z y))))))
      (term 4))
    (check-true (redex-match? AEXP-MONITORED (Check _ _)
      (term (eval-monitored
        (dyn (y (Box Nat) (make-box -2))
          42)))))))

;; -----------------------------------------------------------------------------

(define-metafunction AEXP-MONITORED
  compile-monitored : t -> c
  [(compile-monitored t)
   c
   (judgment-holds (monitored-completion t c))
   ;; TODO hard to define sound completion, because adding lots more checks
   #;(where a (erase-types t))
   #;(judgment-holds (sound-completion-monitored a c))])

;; The interesting case here is for `dyn`, see below.
(define-judgment-form AEXP-MONITORED
  #:mode (monitored-completion I O)
  #:contract (monitored-completion t c)
  [
   ---
   (monitored-completion (:: v _) v)]
  [
   ---
   (monitored-completion (:: x _) x)]
  [
   (monitored-completion t_x c_x)
   (monitored-completion t c)
   ---
   (monitored-completion (:: (let (x t_x) t) _) (let (x c_x) c))]
  [
   (monitored-completion t c) ...
   ---
   (monitored-completion (:: (δ t ...) τ) (δ c ...))]
  [
   (dynamic-completion a_x c_x)
   ;; compile the type annotation into a DEEP run-time check
   (where E_mon (type->check τ_x))
   (where c_mon (in-hole E_mon c_x))
   (monitored-completion t c)
   ---
   (monitored-completion (:: (dyn (x τ_x a_x) t) _) (let (x c_mon) c))])

;; Compile a type into a context that checks and enforces the type
;; - for tag-types, just check
;; - for higher-order types, check the value and wrap in a monitor
(define-metafunction AEXP-MONITORED
  type->check : τ -> E
  [(type->check K)
   (check K hole)]
  [(type->check (Box τ))
   (mon (Box τ)
     (let (b hole)
       (let (ignore (set-box! (check Box b) (in-hole E_v (unbox b))))
         b)))
   (where E_v (type->check τ))])

(define-judgment-form AEXP-MONITORED
  #:mode (sound-completion-monitored I I)
  #:contract (sound-completion-monitored a c)
  [
   (where a_c (erase-monitors (erase-asserts c)))
   (side-condition ,(α=? (term a) (term a_c)))
   ---
   (sound-completion-monitored a c)])

(define-metafunction AEXP-MONITORED
  erase-monitors : any -> any
  [(erase-monitors (mon τ any))
   (erase-monitors any)]
  [(erase-monitors (any ...))
   ((erase-monitors any) ...)]
  [(erase-monitors any)
   any])

(module+ test
  (test-case "type->check"
    (check-equal?
      (term (type->check Nat))
      (term (check Nat hole)))
    (check-equal?
      (term (type->check Int))
      (term (check Int hole)))
    (let ([E (term (type->check (Box Nat)))])
      (check-true
        (redex-match? AEXP-MONITORED E E))
      (check-true
        (redex-match? AEXP-MONITORED c (term (in-hole ,E (box z)))))
      (check α=?
        (term (in-hole ,E (box z)))
        (term (in-hole (mon (Box Nat)
                (let (b hole)
                  (let (ignore (set-box! (check Box b) (check Nat (unbox b))))
                    b))) (box z))))))

  (test-case "compile-monitored"
    (check-true (redex-match? AEXP-MONITORED c
      (term (compile-monitored
        (:: (let (x (:: 2 Nat))
          (:: (dyn (y Nat 2)
            (:: (+ (:: x Nat) (:: y Nat)) Nat)) Nat)) Nat)))))
    (void)))

;; =============================================================================
;; === Section 6
;; =============================================================================

;; AEXP-MONITORED has a type soundness
;;
;;  If `a` is well typed at `τ` and compiles to `c`, then either:
;;  - `a` reduces to `[σ v]` such that `[σ v] ⊨ τ`
;;  - `a` reduces to an Assert error in dynamically typed code
;;  - `a` reduces to a Check error because of a failed tag check

(define-metafunction AEXP-MONITORED
  theorem:mon-soundness : a -> boolean
  [(theorem:mon-soundness a)
   #true
   (where A_init (pre-eval-monitored a))
   (where (RuntimeError _) (-->AEXP-MONITORED* A_init))]
  [(theorem:mon-soundness a)
   ,(judgment-holds (well-typed-value A_final τ))
   (where τ (type-annotation (type-check a)))
   (where A_init (pre-eval-monitored a))
   (where (A_final _) (-->AEXP-MONITORED* A_init))])

(module+ test
  (test-case "mon-soundness"
    (check-true
      (term (theorem:mon-soundness
        (dyn (x Nat -2) (+ x x)))))
    (check-true
      (term (theorem:mon-soundness
        (dyn (x (Box Nat) (make-box (make-box -1)))
          x))))))

;; Claim: exist terms (with no dyn)
;;  where monitored evaluation is faster than tagged
(define-metafunction AEXP-MONITORED
  example:monitored-sometimes-fast : a -> boolean
  [(example:monitored-sometimes-fast a)
   ,(< (term natural_monitored) (term natural_tagged))
   (where A_monitored (pre-eval-monitored a))
   (where A_tagged (pre-eval-tagged a))
   (where (A_final natural_monitored) (-->AEXP-MONITORED* A_monitored))
   (where (A_final natural_tagged) (-->AEXP-TAGGED* A_tagged))])

(module+ test
  (test-case "monitored-sometimes-fast"
    (check-true
      (term (example:monitored-sometimes-fast (unbox (make-box 2)))))))

;; Claim: exist terms (with dyn)
;;  where monitored evaluation is slower
(define-metafunction AEXP-MONITORED
  example:monitored-sometimes-slow : a -> boolean
  [(example:monitored-sometimes-slow a)
   ,(< (term natural_tagged) (term natural_monitored))
   (where A_monitored (pre-eval-monitored a))
   (where A_tagged (pre-eval-tagged a))
   (where (A_final natural_monitored) (-->AEXP-MONITORED* A_monitored))
   (where (A_final2 natural_tagged) (-->AEXP-TAGGED* A_tagged))])

(module+ test
  (test-case "monitored-sometimes-slow"
    (check-true
      (term (example:monitored-sometimes-slow
        (dyn (x (Box Nat) (make-box 2))
          (+ 2 (unbox x))))))))

;; =============================================================================
;; === Section 7
;; =============================================================================

;; Summary / Discussion

