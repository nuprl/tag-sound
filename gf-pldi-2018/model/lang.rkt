#lang racket/base

;; TODO more restrictions on TST ?

(provide
  μTR
  α=?
  UN
  TY)

(require
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

(define-language++ μTR #:alpha-equivalent? α=?
  (τ ::= Int Nat (→ τ τ) (Vectorof τ) (Listof τ)
         (U τ ...) (∀ (α) τ) (μ (α) τ) α
         TST)
  ;; Types,
  ;; - simple types with non-trivial subtyping
  ;; - parameterized types with covariant, contravariant, and invariant positions
  ;; - unions, universals, and recursives because they have non-obvious tags

  (κ ::= Int Nat → Vector List (U κ ...)
         TST)
  ;; Tags,
  ;; - one for each base type
  ;; - one for each value constructor
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
  ;; "L" is for language.

  (UNTYPED-REQUIRE ::= (require M x ...))
  ;; An untyped require is a module name followed by a seqence of identifiers
  (TYPED-REQUIRE ::= (require M Γ))
  ;; A typed require is a module named followed by a sequence of type-annotated identifiers.
  (UNTYPED-DEFINE ::= (define x e))
  ;; An untyped definition is an idenfier and an expression
  (TYPED-DEFINE ::= (define x τ e))
  ;; A typed definition is an identifier, an expected type annotation, and an expression
  (UNTYPED-PROVIDE ::= PROVIDE)
  (TYPED-PROVIDE ::= PROVIDE)
  ;; A provide form is a sequence of identifiers to export

  (REQUIRE ::= UNTYPED-REQUIRE TYPED-REQUIRE)
  (DEFINE ::= UNTYPED-DEFINE TYPED-DEFINE)
  (PROVIDE ::= (provide x ...))

  (e ::= v x (vector τ e ...) (vector e ...) (cons e e)
         (e e)
         (ifz e e e)
         (+ e e) (- e e) (* e e) (% e e)
         (vector-ref e e) (vector-set! e e e) (first e) (rest e)

         (!! [x κ e] e) ;; TODO use 'let' or 'lambda'

         (check τ e) (protect τ e))
  (BINOP ::= + - * %)
  ;; Expressions come in three flavors:
  ;; - value constructors (for integers, functions, vectors, lists)
  ;; - control flow (if)
  ;; - destructors
  ;; - internal forms for gradual type checking (check protect)
  ;; Purpose: recursive functions,
  ;;  partial primops due to type and value errors,
  ;;  mutable values

  (v ::= integer Λ (vector τ loc) (vector loc) (cons v v) nil
         (mon-fun τ v) (mon-vector τ v))
  (Λ ::= (fun x (x) e) (fun x τ (x) e))
  ;; Value forms, including `monitor` values.
  ;; The monitors protect typed functions and vectors.
  ;;  (The type-sound evaluator will use monitors. The tag-sound will not.)

  (Σ ::= (L σ e))
  ;; Evaluation states consist of:
  ;; - `L` the outermost language
  ;; - `σ` the current store
  ;; - `e` the current expression being reduced

  (VAL-ENV ::= (M:ρ ...))
  ;; ... namespace ?
  (M:ρ ::= (M ρ))
  ;; A toplevel value environment binds names to runtime environments,
  ;;  think: "evaluating the modules produced these values for its definitions"

  (ρ ::= (x:v ...))
  (x:v ::= (x v))
  ;; A runtime environment binds identifiers to (typed) values
  ;; Types are preserved to protect typed values used by untyped modules.

  (σ ::= ((loc v*) ...))
  ;; Store, or heap. Maps locations to vector contents

  (TYPE-ENV ::= (M:Γ ...))
  (M:Γ ::= (x Γ))
  ;; A toplevel type environment records names and types.
  ;; For each typed module, records the types.
  ;; Ignores untyped modules (we could record names but no big deal).

  (Γ ::= (x:τ ...))
  (x:τ ::= (x τ) (x κ))
  ;; Local type context, for checking expressions
  ;; ... needs TST because expression typing flips between typed and untyped code

  (E ::= hole (vector τ v ... E e ...) (vector v ... E e ...) (cons E e) (cons v E)
         (E e) (v E)
         (ifz E e e) (+ v ... E e ...) (- v ... E e ...) (* v ... E e ...) (% v ... E e ...)
         (vector-ref v ... E e ...) (vector-set! v ... E e ...)
         (first E) (rest E)
         (check τ E) (protect τ E))
  ;; Left-to-right eager evaluation contexts

  (A ::= Σ Error)
  (Error ::= BoundaryError TypeError)
  (TypeError ::= (TE v EXPECTED))
  (BoundaryError ::= ValueError (BE EXPECTED v))
  (ValueError ::= DivisionByZero BadIndex EmptyList)
  (EXPECTED ::= τ κ string)
  ;; Evaluation can produce either a final value or an error,
  ;;  errors can be due to ill-typed values in untyped code,
  ;;  or boundary errors.
  ;; A boundary error is either:
  ;; - between a module and the runtime
  ;; - between two modules

  (α loc x M ::= variable-not-otherwise-mentioned)
  (α* ::= (α ...))
  (x* ::= (x ...))
  (τ* ::= (τ ...))
  (v* ::= (v ...))
#:binding-forms
  (∀ (α) τ #:refers-to α)
  (μ (α) τ #:refers-to α)
  (fun x_f τ (x) e #:refers-to (shadow x_f x))
  (fun x_f (x) e #:refers-to (shadow x_f x))
  (!! (x κ e_0) e #:refers-to x))

;; -----------------------------------------------------------------------------

(define-term UN untyped)
(define-term TY typed)
