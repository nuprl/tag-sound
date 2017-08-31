#lang racket/base

;; "Between soundness and unsoundness, and what it means for performance."

;; Outline:
;; 1. AEXP is a dynamically typed language
;; 2. Adding an optional type system
;; 3. AEXP is not type sound
;; 4. How to enforce tag soundness (AEXP-TAGGED)
;; 5. How to enforce type soundness (AEXP-TYPED)
;; 6. Soundness vs. performance
;; (Search for "Section N" to jump to a section of the outline)

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
  (RuntimeError ::= (CheckError k v))
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
      (redex-match? AEXP (CheckError int (box _))
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
   (where a (erase-asserts c))
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
    (judgment-holds (well-tagged v k))]
   [-->
    [σ (in-hole E (assert k v))]
    (CheckError k v)
    E-AssertFailure
    (judgment-holds (not-well-tagged v k))]))

;; Apply reduction relation `-->AEXP` to a term, count the number of steps
(define-metafunction AEXP
  -->AEXP* : A -> (A natural)
  [(-->AEXP* A)
   ,(let loop ([curr-A (term A)]
               [num-steps 0])
      (define next-A* (apply-reduction-relation -->AEXP curr-A))
      (cond
       [(null? next-A*)
        (list curr-A num-steps)]
       [(null? (cdr next-A*))
        (loop (car next-A*) (+ num-steps 1))]
       [else
        (raise-arguments-error '-->AEXP* "non-deterministic reduction"
          "current-term" curr-A
          "next-terms" next-A*)]))])

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
  #:mode (well-tagged I I)
  #:contract (well-tagged v k)
  [
   ---
   (well-tagged integer int)]
  [
   ---
   (well-tagged (box _) box)])

(define-judgment-form AEXP
  #:mode (not-well-tagged I I)
  #:contract (not-well-tagged v k)
  [
   (side-condition ,(not (judgment-holds (well-tagged v k))))
   ---
   (not-well-tagged v k)])

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
;; We will show that it provides benefits T0 and T1, but not T2

(define-extended-language AEXP-TYPED
  AEXP

  (τ ::= (Box τ) Int Nat)
  (Γ ::= ((x τ) ...))

  ;; New source term `dyn` is like `let`, but the binding is not type checked.
  ;; Similar to Typed Racket's `require/typed`,
  ;;  except the bound expression is evaluated in scope of previous definitions.
  (a ::= .... (dyn (x τ a) a))

  ;; Type-annotated source terms
  (t ::= (:: v τ) (:: x τ) (:: (let (x t) t) τ) (:: (δ t ...) τ) (:: (dyn (x τ t) t) τ))

  ;; The type checker can catch errors at compile-time
  (TypeError ::= (Type τ e))
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
   (where TypeError (type-check a))
   (where c (compile-typed t))])

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
   (where A (pre-eval a))
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
   TypeError
   (judgment-holds (well-typed () a TypeError))])

(define-judgment-form AEXP-TYPED
  #:mode (well-typed I I O)
  #:contract (well-typed Γ a maybe-t)
  [
   ---
   (well-typed Γ a (Type Int 3))])

;; -----------------------------------------------------------------------------
;; compile typed

(define-metafunction AEXP-TYPED
  compile-typed : t -> c
  [(compile-typed t)
   ,(error 'die)])

