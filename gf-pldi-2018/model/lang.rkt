#lang racket/base

;; TODO more restrictions on TST ?

(provide
  μTR
  α=?
  UN
  TY)

(require
  redex/reduction-semantics)

;; =============================================================================

(define-language μTR
  (τ ::= Int Nat (→ τ τ) (Vectorof τ) (Listof τ)
         (U τ ...) (∀ (α) τ) (μ (α) τ) α
         TST)
  ;; Types,
  ;; - two base types with a subtyping relationship
  ;; - parameterized types with covariant, contravariant, and invariant positions
  ;; - unions, universals, and recursives

  (κ ::= Int Nat → Vector List (U κ ...)
         TST)
  ;; Tags,
  ;; - one for each base type
  ;; - one for each value constructor
  ;; - ... and U because ???
  ;; Purpose: so partial functions can check their inputs.
  ;;  The reduction relation uses tag-checks to make partial functions total

  (PROGRAM ::= (MODULE ...))
  ;; A program is a sequence of modules.

  (TYPED-MODULE ::= (module M typed TYPED-REQUIRE ... TYPED-DEFINE ... TYPED-PROVIDE))
  (UNTYPED-MODULE ::= (module M untyped UNTYPED-REQUIRE ... UNTYPED-DEFINE ... UNTYPED-PROVIDE))
  (MODULE ::= TYPED-MODULE UNTYPED-MODULE)
  ;; A module is either "typed" or "untyped",
  ;;  begins with a sequence of requires,
  ;;  contains a sequence of definitions,
  ;;  and ends with a provide

  (L ::= untyped typed)
  ;; "L" is for language, either typed or untyped

  (UNTYPED-REQUIRE ::= (require M x ...))
  ;; An untyped require is a module name followed by a seqence of identifiers
  (TYPED-REQUIRE ::= (require M Γ))
  ;; A typed require is a module named followed by a sequence of type-annotated identifiers.
  (UNTYPED-DEFINE ::= (define x UNTYPED-EXPR))
  ;; An untyped definition is an idenfier and an expression
  (TYPED-DEFINE ::= (define x τ TYPED-EXPR))
  ;; A typed definition is an identifier, an expected type annotation, and an expression
  (UNTYPED-PROVIDE ::= PROVIDE)
  (TYPED-PROVIDE ::= PROVIDE)
  ;; A provide form is a sequence of identifiers to export

  (REQUIRE ::= UNTYPED-REQUIRE TYPED-REQUIRE)
  (DEFINE ::= UNTYPED-DEFINE TYPED-DEFINE)
  (PROVIDE ::= (provide x ...))

  (v ::= TYPED-VALUE UNTYPED-VALUE
         (mon-fun τ v) (mon-vector τ v))
  ;; Value forms may be typed values, untyped values, or monitored values.
  ;; Monitors are necessary for type soundness, they guard places where
  ;;  untyped values could slip into typed code.

  (e ::= UNTYPED-EXPR TYPED-EXPR (check κ e))
  ;; Expressions may be typed, untyped, or a tag-check

  (TYPED-EXPR ::= TYPED-VALUE x
                  (make-vector τ TYPED-EXPR ...)
                  (cons TYPED-EXPR TYPED-EXPR) (TYPED-EXPR TYPED-EXPR)
                  (ifz TYPED-EXPR TYPED-EXPR TYPED-EXPR)
                  (BINOP TYPED-EXPR TYPED-EXPR)
                  (vector-ref TYPED-EXPR TYPED-EXPR)
                  (vector-set! TYPED-EXPR TYPED-EXPR TYPED-EXPR)
                  (from-untyped τ TYPED-EXPR))
  (TYPED-VALUE ::= integer
                   (fun x τ (x) TYPED-EXPR)
                   (vector τ loc)
                   (cons TYPED-VALUE TYPED-VALUE)
                   nil)
  ;; typed expressions have:
  ;; - type-annotated (higher-order) values
  ;; - boundaries to untyped code (`from-untyped`)

  (UNTYPED-EXPR ::= UNTYPED-VALUE x
                    (make-vector UNTYPED-EXPR ...)
                    (cons UNTYPED-EXPR UNTYPED-EXPR) (UNTYPED-EXPR UNTYPED-EXPR)
                    (ifz UNTYPED-EXPR UNTYPED-EXPR UNTYPED-EXPR)
                    (BINOP UNTYPED-EXPR UNTYPED-EXPR)
                    (vector-ref UNTYPED-EXPR UNTYPED-EXPR)
                    (vector-set! UNTYPED-EXPR UNTYPED-EXPR UNTYPED-EXPR)
                    (from-typed τ UNTYPED-EXPR))
  (UNTYPED-VALUE ::= integer
                     (fun x (x) UNTYPED-EXPR)
                     (vector loc)
                     (cons UNTYPED-VALUE UNTYPED-VALUE)
                     nil)
  ;; untyped expressions have:
  ;; - untyped values
  ;; - boundaries to typed code

  (Λ ::= (fun x (x) UNTYPED-EXPR) (fun x τ (x) TYPED-EXPR))
  (BINOP ::= + - * %)

  (UNTYPED-STATE ::= (untyped σ UNTYPED-EXPR))
  (TYPED-STATE ::= (typed σ TYPED-EXPR))
  (Σ ::= UNTYPED-STATE TYPED-STATE)
  ;; Evaluation states consist of:
  ;; - `L` outermost language
  ;; - `σ` the current store
  ;; - `e` the current expression being reduced

  (E ::= hole
         (make-vector v ... E e ...)
         (cons E e) (cons v E)
         (E e) (v E)
         (ifz E e e)
         (BINOP E e)
         (BINOP v E)
         (vector-ref E e) (vector-ref v E)
         (vector-set! E e e) (vector-set! v E e) (vector-set! v v E)
         (first E) (rest E)
         (check κ E))
  ;; Left-to-right eager evaluation contexts.
  ;; Contexts do **not** reduce under boundaries, the reduction relations will
  ;;  have explicit rules for switching between languages.

  (UNTYPED-A ::= UNTYPED-STATE Error)
  (TYPED-A ::= TYPED-STATE Error)
  (A ::= UNTYPED-A TYPED-A)
  ;; Valid results of evaluation

  (Error ::= BoundaryError TypeError)
  (TypeError ::= (TE v EXPECTED))
  (BoundaryError ::= ValueError (BE EXPECTED v))
  (ValueError ::= DivisionByZero BadIndex EmptyList)
  (EXPECTED ::= τ κ string)
  ;; Errors can be due to ill-typed values in untyped code,
  ;;  or boundary errors.
  ;; A boundary error is either:
  ;; - between a module and the runtime
  ;; - between two modules
  ;; Though the model doesn't currently distinguish between these.

  (VAL-ENV ::= (M:ρ ...))
  (M:ρ ::= (M ρ))
  ;; A toplevel value environment maps module names to local value environments.
  ;;  think: "evaluating the modules produced these values for its definitions"
  ;;  (another good name: namespaces)

  (ρ ::= (x:v ...))
  (x:v ::= (x v))
  ;; A local value environment binds identifiers to values

  (σ ::= ((loc v*) ...))
  ;; Store, or heap.
  ;; Maps locations to sequences of values, representing the contents of a vector.

  (TYPE-ENV ::= (M:Γ ...))
  (M:Γ ::= (x Γ))
  ;; A toplevel type environment maps module names to local type environments.

  (Γ ::= (x:τ ...))
  (x:τ ::= (x τ))
  ;; A local type context maps variable names to types

  (α loc x M ::= variable-not-otherwise-mentioned)
  (α* ::= (α ...))
  (x* ::= (x ...))
  (τ* ::= (τ ...))
  (v* ::= (v ...))
#:binding-forms
  (∀ (α) τ #:refers-to α)
  (μ (α) τ #:refers-to α)
  (fun x_f τ (x) e #:refers-to (shadow x_f x))
  (fun x_f (x) e #:refers-to (shadow x_f x)))

;; -----------------------------------------------------------------------------

(define-term UN untyped)
(define-term TY typed)

(define (α=? t0 t1)
  (alpha-equivalent? μTR t0 t1))
