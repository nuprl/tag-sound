#lang racket/base

(provide
  μTR
  α=?)

(require
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

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
  ;; A program environment binds names to runtime environments,
  ;;  think: "evaluating the module produced these values for its definitions"

  (ρ ::= ρλ ρτ)
  (ρλ ::= (x:v ...))
  (ρτ ::= (x:v:τ ...))
  (x:v ::= (x v))
  (x:v:τ ::= (x v τ))
  ;; A runtime environment binds identifiers to (typed) values
  ;; Types are preserved to protect typed values used by untyped modules.

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

