#lang racket/base

(provide
  μTR
  α=?
  type->tag
  tag-of)

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
  (REQUIRE-τ ::= (require x [x τ] ...))
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

  (e ::= integer x (fun x (x) e) (vector e ...) (cons e e) nil
         (e e) (ifz e e e)
         (+ e e) (- e e) (* e e) (% e e) (vector-ref e e) (vector-set! e e e) (first e) (rest e)
         (mon-fun x τ e) (mon-vector x τ e)
         (!! [x κ e] e))
  ;; Expressions come in three flavors:
  ;; - value constructors (for integers, functions, vectors, lists)
  ;; - control flow (if)
  ;; - destructors
  ;; Purpose: recursive functions,
  ;;  partial primops due to type and value errors,
  ;;  mutable values

  (v ::= integer Λ (vector x) (cons v v) nil
         (mon-fun x τ v) (mon-vector x τ v))
  (Λ ::= (fun x (x) e))
  ;; Value forms, including `monitor` values.
  ;; The monitors protect typed functions and vectors.
  ;;  (The type-sound evaluator will use monitors. The tag-sound will not.)

  (Σ ::= (e σ x S))
  ;; Evaluation states consist of:
  ;; - `e` the current expression being reduced
  ;; - `σ` the current store
  ;; - `x` the current module name (important to check if typed/untyped)
  ;; - `S` is the current context, the type-boundary call stack
  ;; The module is for error-soundness,
  ;;  to prove that typed modules do not commit type errors

  (S ::= () (FRAME S))
  (FRAME ::= (x E τ))
  ;; A type boundary call stack is made of frames.
  ;; A frame is a context to return to.
  ;;  The context always has a name and an expected type.
  ;;  (If there is no expected type, then you didn't cross a boundary.)

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

  (σ ::= ((l v*) ...))
  ;; Store, maps locations to vectors

  (P-TYPE ::= (M-TYPE ...))
  (M-TYPE ::= (x Γ))
  ;; A program type context records names and types.
  ;; For each typed module, records the types.
  ;; Ignores untyped modules (we could record names but no big deal).

  (Γ ::= ((x τ) ...))
  ;; Local type context, for checking expressions

  (E ::= hole (vector v ... E e ...) (cons E e) (cons v E)
         (E e) (v E)
         (ifz E e e) (+ E e) (+ v E) (- E e) (- v E) (* E e) (* v E) (% E e) (% v E)
         (vector-ref E e) (vector-ref v E) (vector-set! E e e) (vector-set! v E e) (vector-set! v v E)
         (first E) (rest E)
         (!! (x κ E) e))
  ;; Left-to-right eager evaluation contexts

  (A ::= Σ Error)
  (Error ::= BoundaryError TypeError)
  (TypeError ::= (TE v EXPECTED))
  (BoundaryError ::= DivisionByZero BadIndex EmptyList (BE x EXPECTED x v))
  (EXPECTED ::= τ κ string)
  ;; Evaluation can produce either a final value or an error,
  ;;  errors can be due to ill-typed values in untyped code,
  ;;  or boundary errors.
  ;; A boundary error is either:
  ;; - between a module and the runtime
  ;; - between two modules

  (α l x ::= variable-not-otherwise-mentioned)
  (α* ::= (α ...))
  (x* ::= (x ...))
  (τ* ::= (τ ...))
  (v* ::= (v ...))
#:binding-forms
  (fun x_f (x) e #:refers-to (shadow x_f x))
  (!! (x κ e_0) e #:refers-to x))

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (tag-of I O)
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

