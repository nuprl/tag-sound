#lang mf-apply racket/base

;; Model of Typed Racket,
;;  showing difference between type soundness and tag soundness semantics.

;; Outline:
;; - one source language, looks like Typed Racket
;; - three semantics,
;;   * type sound
;;   * tag sound
;;   * unsound
;; proofs of type and tag soundness

;; TODO
;; - count runtime time checks ?
;; - be careful! don't mix typing with evaluation

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
  (τ ::= Int Nat (→ τ τ) (Vectorof τ) (Listof τ)
         (U τ ...) (∀ (α) τ) (μ (α) τ) α)
  ;; Types,
  ;; - simple types with non-trivial subtyping
  ;; - parameterized types with covariant, contravariant, and invariant positions
  ;; - unions, universals, and recursives because they have non-obvious tags

  (κ ::= Int Nat → Vector List (U κ ...))
  ;; Tags,
  ;; - one for each base type
  ;; - one for each value constructor
  ;; Purpose: so partial functions can check their inputs.
  ;;  The reduction relation uses tag-checks to make partial functions total

  (PROGRAM ::= (MODULE ...))
  ;; A program is a sequence of modules.
  (MODULE ::= (module-λ x REQUIRE-λ ... DEFINE-λ ... PROVIDE)
              (module-τ x REQUIRE-τ ... DEFINE-τ ... PROVIDE))
  ;; A module is either typed or untyped,
  ;;  begins with a sequence of requires from other modules,
  ;;  contains a sequence of definitions,
  ;;  and ends with a sequence of provided definitions
  (REQUIRE-λ ::= (require x x ...))
  ;; An untyped require is a module name followed by a seqence of identifiers
  (REQUIRE-τ ::= (require/typed x [x τ] ...))
  ;; A typed require is a module named followed by a sequence of type-annotated identifiers.
  (DEFINE-λ ::= (define x e))
  ;; An untyped definition is an idenfier and an expression
  (DEFINE-τ ::= (define x τ e))
  ;; A typed definition is an identifier, an expected type annotation, and an expression
  (PROVIDE ::= (provide x ...))
  ;; A provide form is a sequence of identifiers to export
  ;;
  ;; Purpose: simulate macro-level gradual typing,
  ;;  where typed code can statically assert that untyped values match a type

  ;; TODO maybe change order, goal is to
  ;;  (1) explain all syntax
  ;;  (2) get into evaluation
  ;;  (3) add auxliary technical structures
  ;;  Tailor variable names to the "importance" of things.

  (e ::= integer (fun x (x) e) (vector e ...) (cons e e) nil
         (ifz e e e)
         (+ e e) (- e e) (* e e) (% e e) (vector-ref e e) (vector-set! e e e) (first e) (rest e))
  ;; Expressions come in three flavors:
  ;; - value constructors (for integers, functions, vectors, lists)
  ;; - control flow (if)
  ;; - destructors
  ;; Purpose: recursive functions,
  ;;  partial primops due to type and value errors,
  ;;  mutable values

  (v ::= integer Λ (vector v ...) (cons v v) nil
         (mon-fun τ v) (mon-vector τ v))
  (Λ ::= (fun x (x) e))
  ;; Value forms, including `monitor` values.
  ;; The monitors protect typed functions and vectors.
  ;;  (The type-sound evaluator will use monitors. The tag-sound will not.)

  (Σ ::= (e ρ Σ*))
  ;; The expression evaluator is a perversion of the CEK machine, states are a tuple of:
  ;; - `e` the current expression being reduced
  ;; - `ρ` the current runtime environment
  ;; - `Ψ` the current module environemnt
  ;; - `Σ*` a stack of "next states", the first Σ on the stack is expecting the value of `e`
  (Σ* ::= (Σ ...))

  (P-ENV ::= (MODULE-BINDING ...))
  (MODULE-BINDING ::= (x ρ))
  ;; A module enviroment binds names to runtime environments,
  ;;  think: "evaluating the module produced these values for its definitions"

  (ρ ::= ρλ ρτ)
  (ρλ ::= (x:v ...))
  (ρτ ::= (x:v:τ ...))
  (x:v ::= (x v))
  (x:v:τ ::= (x v τ))
  ;; A runtime environment binds identifiers to values

  (Γ ::= ((x τ) ...))
  ;; Type context, for checking expressions

  (E ::= hole (vector v ... E e ...) (cons E e) (cons v E)
         (ifz E e e) (+ E e) (+ v E) (- E e) (- v E) (* E e) (* v E) (% E e) (% v E)
         (vector-ref E e) (vector-ref v E) (vector-set! E e e) (vector-set! v E e) (vector-set! v v E)
         (first E) (rest E))
  ;; Left-to-right eager evaluation contexts

  (A ::= Σ Error)
  (Error ::= ValueError TypeError)
  (ValueError ::= DivisionByZero BadIndex EmptyList)
  (TypeError ::= (TE v τ))
  ;; Evaluation can produce either a final value or an error,
  ;;  errors can be due to bad values, or to ill-typed values.
  ;; Type soundness restricts the possible errors.

  (α x ::= variable-not-otherwise-mentioned)
  (α* ::= (α ...))
  (x* ::= (x ...))
  (τ* ::= (τ ...))
#:binding-forms
  (fun x_f (x) e #:refers-to (shadow x_f x)))

;; -----------------------------------------------------------------------------
;; --- evaluation
;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-program : PROGRAM -> P-ENV
  [(eval-program PROGRAM P-ENV)
   #{eval-program/env () PROGRAM}])

(define-metafunction μTR
  eval-program/env : P-ENV PROGRAM -> P-ENV
  [(eval-program/env P-ENV ())
   P-ENV]
  [(eval-program/env P-ENV (MODULE_0 MODULE_1 ...))
   #{eval-program/env P-ENV_+ (MODULE_1 ...)}
   (where P-ENV_+ (eval-module P-ENV MODULE_0))])

(define-metafunction μTR
  eval-module : P-ENV MODULE -> P-ENV
  [(eval-module P-ENV MODULE_λ)
   P-ENV_final
   (where (module-λ x REQUIRE-λ ... DEFINE-λ ... PROVIDE) MODULE_λ)
   (where ρλ_init #{eval-untyped-require* P-ENV (REQUIRE-λ ...)})
   (where ρλ_body #{eval-untyped-define* ρλ_init (DEFINE-λ ...)})
   (where ρλ_public #{eval-untyped-provide ρλ_body PROVIDE})
   (where P-ENV_final #{env-add P-ENV (x ρλ_public)})]
  [(eval-module P-ENV MODULE_τ)
   P-ENV_final
   (where (module-τ x REQUIRE-τ ... DEFINE-τ ... PROVIDE) MODULE_τ)
   (where ρτ_init #{eval-typed-require* P-ENV (REQUIRE-τ ...)})
   (where ρτ_body #{eval-typed-define* ρτ_init (DEFINE-τ ...)})
   (where ρτ_public #{eval-typed-provide ρτ_body PROVIDE})
   (where P-ENV_final #{env-add P-ENV (x ρτ_public)})])

;; ---

(define-metafunction μTR
  eval-untyped-require* : P-ENV (REQUIRE-λ ...) -> ρλ
  [(eval-untyped-require* P-ENV ())
   ()]
  [(eval-untyped-require* P-ENV (REQUIRE-λ_first REQUIRE-λ_rest ...))
   #{env-add ρλ_rest x:v}
   (where x:v #{eval-untyped-require P-ENV REQUIRE-λ_first})
   (where ρλ_rest #{eval-untyped-require* P-ENV (REQUIRE-λ_rest ...)})])

(define-metafunction μTR
  eval-typed-require* : P-ENV (REQUIRE-τ ...) -> ρτ
  [(eval-typed-require* P-ENV ())
   ()]
  [(eval-typed-require* P-ENV (REQUIRE-τ_first REQUIRE-τ_rest ...))
   #{env-add ρτ_rest x:v:τ}
   (where x:v:τ #{eval-typed-require P-ENV REQUIRE-τ_first})
   (where ρτ_rest #{eval-typed-require* P-ENV (REQUIRE-τ_rest ...)})])

(define-metafunction μTR
  eval-untyped-require : P-ENV REQUIRE-λ -> ρλ
  [(eval-untyped-require P-ENV REQUIRE-λ)
   ρλ
   (where (require x_mod x_require ...) REQUIRE-λ)
   (where (x_mod ρ_mod) (program-env-ref P-ENV x_mod))
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'eval-untyped-require
                        "required identifier not provided by module"
                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
   (where ρ_mixed (#{env-ref ρ_mod x_require any_fail} ...))
   (where ρλ #{runtime-env->untyped-runtime-env ρ_mixed})]
  [(eval-untyped-require P-ENV REQUIRE-λ)
   ,(raise-arguments-error 'eval-untyped-require
      "required module does not exist"
      "module" (term x) "env" (term P-ENV))
   (where (require x_mod _ ...) REQUIRE-λ)])

(define-metafunction μTR
  eval-typed-require : P-ENV REQUIRE-τ -> ρτ
  [(eval-typed-require P-ENV REQUIRE-τ)
   ρτ
   (where (require x_mod [x_require τ_require] ...) REQUIRE-τ)
   (where (x_mod ρ_mod) (program-env-ref P-ENV x_mod))
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'eval-typed-require
                        "required identifier not provided by module"
                        "id" x "module" (term x_mod) "env" (term ρ_mod))))
   (where ρ_mixed (#{env-ref ρ x_require any_fail} ...))
   (where ρτ #{runtime-env->typed-runtime-env ρ_mixed (τ_require ...)})]
  [(eval-typed-require P-ENV REQUIRE-τ)
   ,(raise-arguments-error 'eval-typed-require
      "required module does not exist"
      "module" (term x) "env" (term P-ENV))
   (where (require x_mod _ ...) REQUIRE-τ)])

(define-metafunction μTR
  runtime-env->untyped-runtime-env : ρ -> ρλ
  [(runtime-env->untyped-runtime-env ρλ)
   ρλ]
  [(runtime-env->untyped-runtime-env ρτ)
   ρλ
   (where ((x v τ) ...) ρτ)
   (where ρλ ((x #{apply-monitor# v τ}) ...))])

(define-metafunction μTR
  runtime-env->typed-runtime-env : ρ τ* -> ρτ
  [(runtime-env->typed-runtime-env ρτ τ*)
   ρτ_sub
   (where ((x v τ_actual) ...) ρτ)
   (where (τ_expected ...) τ*)
   (where ρτ_sub ((x v #{assert-below τ_expected τ_actual}) ...))]
  [(runtime-env->typed-runtime-env ρλ τ*)
   ρτ
   (where ((x v) ...) ρλ)
   (where (τ ...) τ*)
   (where ρτ ((x #{apply-monitor# v τ} τ) ...))])

(define-judgment-form μTR
  #:mode (apply-monitor I I O)
  #:contract (apply-monitor v τ v)
  [
   (flat-value v)
   (where κ #{type->tag τ})
   (well-tagged-value v κ)
   ---
   (apply-monitor v τ v)]
  [
   (apply-monitor v_0 τ v_0+)
   (apply-monitor v_1 (Listof τ) v_1+)
   (where v_mon (cons v_0+ v_1+))
   ---
   (apply-monitor (cons v_0 v_1) (Listof τ) v_mon)]
  [
   (fun-value v)
   (well-tagged-value v #{type->tag τ})
   (where v_mon (mon-fun τ v))
   ---
   (apply-monitor v τ v_mon)]
  [
   (vector-value v)
   (where v_mon (mon-vector τ v))
   ---
   (apply-monitor v τ v_mon)])

(define-metafunction μTR
  apply-monitor# : v τ -> v
  [(apply-monitor# v τ)
   v_mon
   (judgment-holds (apply-monitor v τ v_mon))])

(define-metafunction μTR
  assert-below : τ τ -> τ
  [(assert-below τ_0 τ_1)
   τ_0
   (judgment-holds (<: τ_0 τ_1))]
  [(assert-below τ_0 τ_1)
   ,(raise-argument-error 'assert-below (format "supertype of ~a" (term τ_0))
      "given" (term τ_1))])

(define-metafunction μTR
  eval-untyped-define* : ρλ (DEFINE-λ ...) -> ρλ
  [(eval-untyped-define* ρλ ())
   ρλ]
  [(eval-untyped-define* ρλ (DEFINE-λ_first DEFINE-λ_rest ...))
   #{eval-untyped-define* ρλ_+ (DEFINE-λ_rest ...)}
   (where (define x e) DEFINE-λ_first)
   (where v #{eval-value ρλ e})
   (where ρλ_+ #{env-add ρλ (x v)})])

(define-metafunction μTR
  eval-typed-define* : ρτ (DEFINE-τ ...) -> ρτ
  [(eval-typed-define* ρτ ())
   ρτ]
  [(eval-typed-define* ρτ (DEFINE-τ_first DEFINE-τ_rest ...))
   #{eval-typed-define* ρτ_+ (DEFINE-τ_rest ...)}
   (where (define x τ e) DEFINE-τ_first)
   ;; TODO error, don't know how to thread "vector state" through evaluation
   (where [v ρτ_new] #{eval-value ρτ e})
   (side-condition (error 'not-implemented))
   (where ρτ_+ #{env-add ρτ (x v τ)})])

(define-metafunction μTR
  eval-untyped-provide : ρλ PROVIDE -> ρλ
  [(eval-untyped-provide ρλ PROVIDE)
   #{eval-provide ρλ PROVIDE}])

(define-metafunction μTR
  eval-typed-provide : ρτ PROVIDE -> ρτ
  [(eval-typed-provide ρτ PROVIDE)
   #{eval-provide ρτ PROVIDE}])

;; eval-provide
;; Filter a runtime environment, remove all identifiers that are not in the
;;  given list of provides.
;; Error if an identifier is provided, but not defined in the runtime environment
(define-metafunction μTR
  eval-provide : ρ PROVIDE -> ρ
  [(eval-provide ρ (provide x_provide ...))
   (#{env-ref ρ x_provide any_fail} ...)
   (where any_fail ,(λ (x)
                      (raise-user-error 'provide "provided identifier not defined in module: ~a" x)))])

(module+ test
  (test-case "eval-provide"
    (check-mf-apply*
      ((eval-provide () (provide))
       ())
      ((eval-provide ((x 4) (y 5)) (provide x y))
        ((x 4) (y 5)))
      ((eval-provide ((x 4) (y 5)) (provide y x))
       ((y 5) (x 4)))
      ((eval-provide ((x 4) (y 5)) (provide y))
       ((y 5))))

    (check-exn exn:fail:contract?
      (λ () (term (eval-provide ((x 4)) (provide y)))))))

(define-metafunction μTR
  eval-value : ρ e -> [v ρ]
  [(eval-value ρ e)
   [v ρ]
   (where Σ_0 #{load-expression ρ e})
   (where A ,(step-expression* (term Σ_0)))
   (where [v ρ] #{unload-answer A})])

(define-metafunction μTR
  load-expression : ρ e -> Σ
  [(load-expression ρ e)
   (e ρ ())])

(define-metafunction μTR
  unload-answer : A -> [v ρ]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   [v ρ]
   (where (v ρ ()) Σ)]
  [(unload-answer Σ)
   ,(raise-arguments-error 'unload-answer "evaluation ended with non-empty continuation" "state" (term Σ))])

(define step-expression
  (reduction-relation μTR
   #:domain A
   [-->
     Σ
     BadIndex]
  ))

(define step-expression*
  (make--->* step-expression))

;; -----------------------------------------------------------------------------
;; --- typing
;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (<: I I)
  #:contract (<: τ τ)
  [
   --- Sub-Refl
   (<: τ τ)])

(define-metafunction μTR
  subtype? : τ τ -> boolean
  [(subtype? τ_0 τ_1)
   (judgment-holds (<: τ_0 τ_1))])

(define-judgment-form μTR
  #:mode (well-tagged-value I I)
  #:contract (well-tagged-value v κ)
  [
   ---
   (well-tagged-value integer Int)]
  [
   ---
   (well-tagged-value natural Nat)]
  [
   (fun-value v)
   ---
   (well-tagged-value v →)]
  [
   (vector-value v)
   ---
   (well-tagged-value v Vector)]
  [
   ---
   (well-tagged-value nil List)]
  [
   ---
   (well-tagged-value (cons v_0 v_1) List)]
  [
   ;; TODO edit if performance is an issue
   (where (κ_pre ... κ_mid κ_post ...) (κ ...))
   (well-tagged-value v κ_mid)
   ---
   (well-tagged-value v (U κ ...))])

(define-judgment-form μTR
  #:mode (not-well-tagged-value I I)
  #:contract (not-well-tagged-value v κ)
  [
   (side-condition ,(not (judgment-holds (well-tagged-value v κ))))
   ---
   (not-well-tagged-value v κ)])

(define-judgment-form μTR
  #:mode (flat-value I)
  #:contract (flat-value v)
  [
   ---
   (flat-value integer)]
  [
   ---
   (flat-value nil)])

(define-judgment-form μTR
  #:mode (vector-value I)
  #:contract (vector-value v)
  [
   ---
   (vector-value (vector v ...))]
  [
   ---
   (vector-value (mon-vector τ v))])

(define-judgment-form μTR
  #:mode (fun-value I)
  #:contract (fun-value v)
  [
   ---
   (fun-value Λ)]
  [
   ---
   (fun-value (mon-fun τ v))])

(define-judgment-form μTR
  #:mode (tag-of I I)
  #:contract (tag-of τ κ)
  [
   ---
   (tag-of κ κ)]
  [
   ---
   (tag-of (→ τ_0 τ_1) →)]
  [
   ---
   (tag-of (Vectorof τ) Vector)]
  [
   ---
   (tag-of (Listof τ) List)]
  [
   (tag-of τ κ) ...
   ---
   (tag-of (U τ ...) (U κ ...))]
  [
   (tag-of τ κ)
   ---
   (tag-of (∀ (α) τ) κ)]
  [
   (tag-of τ κ)
   ---
   (tag-of (μ (α) τ) κ)])

(define-metafunction μTR
  type->tag : τ -> κ
  [(type->tag τ)
   κ
   (judgment-holds (tag-of τ κ))])

;; -----------------------------------------------------------------------------
;; --- grammar
;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-formed-type I)
  #:contract (well-formed-type τ)
  [
   (all-unions-discriminative τ)
   (all-recursive-types-contractive τ)
   (all-abstractions-guarded τ)
   (closed-type τ)
   ---
   (well-formed-type τ)])

(define-judgment-form μTR
  #:mode (all-unions-discriminative I)
  #:contract (all-unions-discriminative τ)
  [
   ;; TODO
   ---
   (all-unions-discriminative τ)])

(define-judgment-form μTR
  #:mode (all-recursive-types-contractive I)
  #:contract (all-recursive-types-contractive τ)
  [
   ---
   (all-recursive-types-contractive Int)]
  [
   ---
   (all-recursive-types-contractive Nat)]
  [
   (all-recursive-types-contractive τ_dom)
   (all-recursive-types-contractive τ_cod)
   ---
   (all-recursive-types-contractive (→ τ_dom τ_cod))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (Vectorof τ))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (Listof τ))]
  [
   (all-recursive-types-contractive τ) ...
   ---
   (all-recursive-types-contractive (U τ ...))]
  [
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (∀ (α) τ))]
  [
   (formally-contractive (α) τ)
   (all-recursive-types-contractive τ)
   ---
   (all-recursive-types-contractive (μ (α) τ))]
  [
   ---
   (all-recursive-types-contractive α)])

;; formally-contractive = does not have the form `(μ (α_i ...) α_i)`
(define-judgment-form μTR
  #:mode (formally-contractive I I)
  #:contract (formally-contractive α* τ)
  [
   ---
   (formally-contractive α* Int)]
  [
   ---
   (formally-contractive α* Nat)]
  [
   ---
   (formally-contractive α* (→ _ _))]
  [
   ---
   (formally-contractive α* (Vectorof _))]
  [
   ---
   (formally-contractive α* (Listof _))]
  [
   (formally-contractive α* τ_i) ...
   ---
   (formally-contractive α* (U τ_i ...))]
  [
   (where α*_+ ,(set-remove (term α*) (term α)))
   (formally-contractive α*_+ τ)
   ---
   (formally-contractive α* (∀ (α) τ))]
  [
   (where α*_+ ,(set-add (term α*) (term α)))
   (formally-contractive α*_+ τ)
   ---
   (formally-contractive α* (μ (α) τ))]
  [
   (side-condition ,(not (set-member? (term α*) (term α))))
   ---
   (formally-contractive α* α)])

(define-judgment-form μTR
  #:mode (all-abstractions-guarded I)
  #:contract (all-abstractions-guarded τ)
  [
   ;; TODO
   ---
   (all-abstractions-guarded τ)])

(define-judgment-form μTR
  #:mode (closed-type I)
  #:contract (closed-type τ)
  [
   (free-type-variables τ ())
   ---
   (closed-type τ)])

(define-judgment-form μTR
  #:mode (free-type-variables I O)
  #:contract (free-type-variables I O)
  [
   ---
   (free-type-variables Int ())]
  [
   ---
   (free-type-variables Nat ())]
  [
   (free-type-variables τ_dom α*_dom)
   (free-type-variables τ_cod α*_cod)
   (where α* ,(set-union (term α*_dom) (term α*_cod)))
   ---
   (free-type-variables (→ τ_dom τ_cod) α*)]
  [
   (free-type-variables τ α*)
   ---
   (free-type-variables (Vectorof τ) α*)]
  [
   (free-type-variables τ α*)
   ---
   (free-type-variables (Listof τ) α*)]
  [
   (free-type-variables τ_i α*_i) ...
   (where α* ,(set-union* (term (α*_i ...))))
   ---
   (free-type-variables (U τ_i ...) α*)]
  [
   (free-type-variables τ_body α*_body)
   (where α* ,(set-remove (term α*_body) (term α)))
   ---
   (free-type-variables (∀ (α) τ_body) α*)]
  [
   (free-type-variables τ_body α*_body)
   (where α* ,(set-remove (term α*_body) (term α)))
   ---
   (free-type-variables (μ (α) τ_body) α*)]
  [
   ---
   (free-type-variables α (α))])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-formed-program I)
  #:contract (well-formed-program P)
  [
   (where (MODULE ...) P)
   (well-formed-module MODULE) ...
   ;; TODO only require provided
   ---
   (well-formed-program P)])

(define-judgment-form μTR
  #:mode (well-formed-module I)
  #:contract (well-formed-module MODULE)
  [
   ;; TODO only provide defined
   ---
   (well-formed-module MODULE)])

;; -----------------------------------------------------------------------------
;; --- UTILITIES
;; -----------------------------------------------------------------------------

(define (set-union* x**)
  (for/fold ([acc '()])
            ([x* (in-list x**)])
    (set-union acc x*)))

(define-metafunction μTR
  env-add : any any -> any
  [(env-add any_env any_val)
   ,(cons (term any_val) (term any_env))])

(define-metafunction μTR
  env-ref : any x any_fail -> any
  [(env-ref any_env x any_fail)
   (let loop ([env (term any_env)])
     (cond
      [(null? env)
       ((term any_fail))]
      [(equal? (car (car env)) (term x))
       (car env)]
      [else
       (loop (cdr env))]))])

(define-metafunction μTR
  program-env-ref : P-ENV x -> ρ
  [(program-env-ref P-ENV x)
   #{env-ref P-ENV x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'program-env-ref "unbound identifier" "id" x "env" (term P-ENV))))])

(define-metafunction μTR
  runtime-env-ref : ρ x -> any
  [(runtime-env-ref ρ x)
   #{env-ref ρ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'runtime-env-ref "unbound identifier" "id" x "env" (term ρ))))])

