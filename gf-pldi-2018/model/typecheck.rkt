#lang mf-apply racket/base

;; Common typechecking functions
;; ... static type checking for any kind of program, nevermind the semantics

(provide
  <:
  subtype?
  not-well-tagged-value
  well-tagged-value

  flat-value

  higher-order-value
  not-higher-order-value

  fun-value
  not-fun-value
  list-value
  not-list-value
  vector-value
  not-vector-value
  integer-value
  not-integer-value

  well-typed-program
  well-typed-module
  well-dyn-expression
  well-typed-expression
  well-typed-expression/TST
  infer-expression-type ;; really not sure about this one

  require->local-type-env
  define->local-type-env
  local-type-env->provided

  tagged-completion
  well-tagged-expression
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define-judgment-form μTR
  #:mode (well-typed-program I O)
  #:contract (well-typed-program PROGRAM TYPE-ENV)
  [
   (where (MODULE ...) PROGRAM)
   (well-typed-module* () (MODULE ...) TYPE-ENV_N)
   (where TYPE-ENV ,(reverse (term TYPE-ENV_N)))
   ---
   (well-typed-program PROGRAM TYPE-ENV)])

(define-metafunction μTR
  well-typed-program# : PROGRAM -> any
  [(well-typed-program# PROGRAM)
   TYPE-ENV
   (judgment-holds (well-typed-program PROGRAM TYPE-ENV))]
  [(well-typed-program# PROGRAM)
   #false])

(define-judgment-form μTR
  #:mode (well-typed-module* I I O)
  #:contract (well-typed-module* TYPE-ENV (MODULE ...) TYPE-ENV)
  [
   ---
   (well-typed-module* TYPE-ENV () TYPE-ENV)]
  [
   (well-typed-module TYPE-ENV_0 MODULE_0 TYPE-ENV_1)
   (well-typed-module* TYPE-ENV_1 (MODULE_rest ...) TYPE-ENV_n)
   ---
   (well-typed-module* TYPE-ENV_0 (MODULE_0 MODULE_rest ...) TYPE-ENV_n)])

(define-judgment-form μTR
  #:mode (well-typed-module I I O)
  #:contract (well-typed-module TYPE-ENV MODULE TYPE-ENV)
  [
   (where (module M _ REQUIRE ... DEFINE ... PROVIDE) MODULE)
   (where Γ_req #{require->local-type-env TYPE-ENV (REQUIRE ...)})
   (where Γ_def #{define->local-type-env (DEFINE ...)})
   (where Γ #{local-type-env-append Γ_req Γ_def})
   (well-typed-define Γ DEFINE) ...
   (where Γ_provide #{local-type-env->provided Γ PROVIDE})
   (where TYPE-ENV_+ #{toplevel-type-env-set TYPE-ENV M Γ_provide})
   ---
   (well-typed-module TYPE-ENV MODULE TYPE-ENV_+)])

(define-judgment-form μTR
  #:mode (well-typed-define I I)
  #:contract (well-typed-define Γ DEFINE)
  [
   (where (define x e) UNTYPED-DEFINE)
   (well-dyn-expression Γ e)
   ---
   (well-typed-define Γ UNTYPED-DEFINE)]
  [
   (where (define x τ e) TYPED-DEFINE)
   (well-typed-expression Γ e τ)
   ---
   (well-typed-define Γ TYPED-DEFINE)])

(define-judgment-form μTR
  #:mode (well-typed-expression I I I)
  #:contract (well-typed-expression Γ e τ)
  [
   ---
   (well-typed-expression Γ natural Nat)]
  [
   ---
   (well-typed-expression Γ integer Int)]
  [
   (where [_ τ_0] #{local-type-env-ref Γ x})
   (<: τ_0 τ)
   ---
   (well-typed-expression Γ x τ)]
  [
   (<: τ τ_fun)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (where Γ_f #{local-type-env-set Γ x_f τ})
   (where Γ_x #{local-type-env-set Γ_f x_arg τ_dom})
   (well-typed-expression Γ_x e_body τ_cod)
   ---
   (well-typed-expression Γ (fun x_f τ_fun (x_arg) e_body) τ)]
  [
   (<: τ_vec τ)
   (where (Vectorof τ_elem) #{coerce-vector-type τ})
   (well-typed-expression Γ e τ_elem) ...
   ---
   (well-typed-expression Γ (vector τ_vec e ...) τ)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   (well-typed-expression Γ e_0 τ_elem)
   (well-typed-expression Γ e_1 τ)
   ---
   (well-typed-expression Γ (cons e_0 e_1) τ)]
  [
   (where (Listof τ_elem) #{coerce-list-type τ})
   ---
   (well-typed-expression Γ nil τ)]
  [
   (infer-expression-type Γ e_fun τ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ})
   (well-typed-expression Γ e_fun τ)
   (well-typed-expression Γ e_arg τ_dom)
   ---
   (well-typed-expression Γ (e_fun e_arg) τ_cod)]
  [
   (well-typed-expression Γ e_0 Int)
   (well-typed-expression Γ e_1 τ)
   (well-typed-expression Γ e_2 τ)
   ---
   (well-typed-expression Γ (ifz e_0 e_1 e_2) τ)]
  [
   (well-typed-expression Γ e_0 Int)
   (well-typed-expression Γ e_1 Int)
   ---
   (well-typed-expression Γ (+ e_0 e_1) Int)]
  [
   (well-typed-expression Γ e_0 Nat)
   (well-typed-expression Γ e_1 Nat)
   ---
   (well-typed-expression Γ (+ e_0 e_1) Nat)]
  [
   (well-typed-expression Γ e_0 Int)
   (well-typed-expression Γ e_1 Int)
   ---
   (well-typed-expression Γ (- e_0 e_1) Int)]
  [
   (well-typed-expression Γ e_0 Int)
   (well-typed-expression Γ e_1 Int)
   ---
   (well-typed-expression Γ (* e_0 e_1) Int)]
  [
   (well-typed-expression Γ e_0 Nat)
   (well-typed-expression Γ e_1 Nat)
   ---
   (well-typed-expression Γ (* e_0 e_1) Nat)]
  [
   (well-typed-expression Γ e_0 Int)
   (well-typed-expression Γ e_1 Int)
   ---
   (well-typed-expression Γ (% e_0 e_1) Int)]
  [
   (well-typed-expression Γ e_0 Nat)
   (well-typed-expression Γ e_1 Nat)
   ---
   (well-typed-expression Γ (% e_0 e_1) Nat)]
  [
   (well-typed-expression Γ e_vec (Vectorof τ))
   (well-typed-expression Γ e_i Int)
   ---
   (well-typed-expression Γ (vector-ref e_vec e_i) τ)]
  [
   (well-typed-expression Γ e_vec (Vectorof τ))
   (well-typed-expression Γ e_i Int)
   (well-typed-expression Γ e_val τ)
   ---
   (well-typed-expression Γ (vector-set! e_vec e_i e_val) τ)]
  [
   (well-typed-expression Γ e (Listof τ))
   ---
   (well-typed-expression Γ (first e) τ)]
  [
   (where (Listof τ_elem) τ)
   (well-typed-expression Γ e τ)
   ---
   (well-typed-expression Γ (rest e) τ)]
  [
   (well-typed-expression Γ e τ)
   ---
   (well-typed-expression Γ e (U τ_0 ... τ τ_1 ...))]
  [
   (well-typed-expression Γ e #{mu-fold (μ (α) τ)})
   ---
   (well-typed-expression Γ e (μ (α) τ))]
  [
   (well-typed-expression Γ e τ)
   ---
   (well-typed-expression Γ e (∀ (α) τ))])

(define-judgment-form μTR
  #:mode (well-dyn-expression I I)
  #:contract (well-dyn-expression Γ e)
  [
   ---
   (well-dyn-expression Γ integer)]
  [
   (where Γ_f #{local-type-env-set Γ x_fun TST})
   (where Γ_x #{local-type-env-set Γ_f x_arg TST})
   (well-dyn-expression Γ_x e)
   ---
   (well-dyn-expression Γ (fun x_fun (x_arg) e))]
  [
   ---
   (well-dyn-expression Γ nil)]
  [
   (where [_ TST] #{local-type-env-ref Γ x})
   ---
   (well-dyn-expression Γ x)]
  [
   (well-dyn-expression Γ e) ...
   ---
   (well-dyn-expression Γ (vector e ...))]
  [
   (well-dyn-expression Γ e_hd)
   (well-dyn-expression Γ e_tl)
   ---
   (well-dyn-expression Γ (cons e_hd e_tl))]
  [
   (well-dyn-expression Γ e_fun)
   (well-dyn-expression Γ e_arg)
   ---
   (well-dyn-expression Γ (e_fun e_arg))]
  [
   (well-dyn-expression Γ e_0)
   (well-dyn-expression Γ e_1)
   (well-dyn-expression Γ e_2)
   ---
   (well-dyn-expression Γ (ifz e_0 e_1 e_2))]
  [
   (well-dyn-expression Γ e_0)
   (well-dyn-expression Γ e_1)
   ---
   (well-dyn-expression Γ (+ e_0 e_1))]
  [
   (well-dyn-expression Γ e_0)
   (well-dyn-expression Γ e_1)
   ---
   (well-dyn-expression Γ (- e_0 e_1))]
  [
   (well-dyn-expression Γ e_0)
   (well-dyn-expression Γ e_1)
   ---
   (well-dyn-expression Γ (* e_0 e_1))]
  [
   (well-dyn-expression Γ e_0)
   (well-dyn-expression Γ e_1)
   ---
   (well-dyn-expression Γ (% e_0 e_1))]
  [
   (well-dyn-expression Γ e_vec)
   (well-dyn-expression Γ e_i)
   ---
   (well-dyn-expression Γ (vector-ref e_vec e_i))]
  [
   (well-dyn-expression Γ e_vec)
   (well-dyn-expression Γ e_i)
   (well-dyn-expression Γ e_arg)
   ---
   (well-dyn-expression Γ (vector-set! e_vec e_i e_arg))]
  [
   (well-dyn-expression Γ e)
   ---
   (well-dyn-expression Γ (first e))]
  [
   (well-dyn-expression Γ e)
   ---
   (well-dyn-expression Γ (rest e))])

(define-judgment-form μTR
  #:mode (well-typed-expression/TST I I I)
  #:contract (well-typed-expression/TST Γ e τ)
  [
   (well-dyn-expression Γ e)
   ---
   (well-typed-expression/TST Γ e TST)]
  [
   (not-TST τ)
   (well-typed-expression Γ e τ)
   ---
   (well-typed-expression/TST Γ e τ)])

(define-metafunction μTR
  require->local-type-env : TYPE-ENV (REQUIRE ...) -> Γ
  [(require->local-type-env TYPE-ENV ())
   ()]
  [(require->local-type-env TYPE-ENV (TYPED-REQUIRE_0 TYPED-REQUIRE_rest ...))
   #{local-type-env-append Γ_expected Γ_rest}
   (where (require M Γ_expected) TYPED-REQUIRE_0)
   (where (M Γ_actual) #{toplevel-type-env-ref TYPE-ENV M})
   (side-condition
     (unless (judgment-holds (valid-require Γ_expected Γ_actual))
       (raise-arguments-error 'require->local-type-env "invalid require"
         "require" (term TYPED-REQUIRE_0)
         "toplevel-type-env" (term TYPE-ENV))))
   (where Γ_rest #{require->local-type-env TYPE-ENV (TYPED-REQUIRE_rest ...)})]
  [(require->local-type-env TYPE-ENV (UNTYPED-REQUIRE_0 UNTYPED-REQUIRE_rest ...))
   #{local-type-env-append Γ_expected Γ_rest}
   (where (require M x ...) UNTYPED-REQUIRE_0)
   (where Γ_expected ((x TST) ...))
   (where (M Γ_actual) #{toplevel-type-env-ref TYPE-ENV M})
   (side-condition
     (unless (judgment-holds (valid-require Γ_expected Γ_actual))
       (raise-arguments-error 'require->local-type-env "invalid require"
         "require" (term UNTYPED-REQUIRE_0)
         "toplevel-type-env" (term TYPE-ENV))))
   (where Γ_rest #{require->local-type-env TYPE-ENV (UNTYPED-REQUIRE_rest ...)})])

(define-judgment-form μTR
  #:mode (valid-require I I)
  #:contract (valid-require Γ Γ)
  [
   --- R-Base
   (valid-require () Γ)]
  [
   (where [x _] #{local-type-env-ref Γ x})
   (valid-require (x:τ_rest ...) Γ)
   --- R-TST
   (valid-require ((x TST) x:τ_rest ...) Γ)]
  [
   (where [x TST] #{local-type-env-ref Γ x})
   (valid-require (x:τ_rest ...) Γ)
   --- R-Type-TST
   (valid-require ((x τ) x:τ_rest ...) Γ)]
  [
   (where [x τ_actual] #{local-type-env-ref Γ x})
   (not-TST τ_actual)
   (<: τ_actual τ)
   (valid-require (x:τ_rest ...) Γ)
   --- R-Type-Type
   (valid-require ((x τ) x:τ_rest ...) Γ)])

(define-metafunction μTR
  define->local-type-env : (DEFINE ...) -> Γ
  [(define->local-type-env ((define x _) ...))
   ((x TST) ...)]
  [(define->local-type-env ((define x τ _) ...))
   ((x τ) ...)])

(define-metafunction μTR
  local-type-env->provided : Γ PROVIDE -> Γ
  [(local-type-env->provided Γ (provide))
   ()]
  [(local-type-env->provided Γ (provide x_0 x_rest ...))
   (x:τ_0 x:τ_rest ...)
   (where x:τ_0 #{local-type-env-ref Γ x_0})
   (where (x:τ_rest ...) #{local-type-env->provided Γ (provide x_rest ...)})])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (<: I I)
  #:contract (<: τ τ)
  [
   --- Sub-Nat
   (<: Nat Int)]
  [
   --- Sub-Refl
   (<: τ τ)]
  [
   (<: τ_0 τ_1)
   --- Sub-List
   (<: (Listof τ_0) (Listof τ_1))]
  [
   (<: τ_dom1 τ_dom0)
   (<: τ_cod0 τ_cod1)
   --- Sub-Fun
   (<: (→ τ_dom0 τ_cod0) (→ τ_dom1 τ_cod1))]
  [
   (subtype* #{coerce-sequence τ} (τ_u ...))
   --- Sub-Union
   (<: τ (U τ_u ...))]
  [
   (where τ_0sub (substitute τ_0 α_0 α_0))
   (where τ_1sub (substitute τ_1 α_1 α_0))
   (<: τ_0sub τ_1sub)
   --- Sub-Forall-R
   (<: (∀ (α_0) τ_0) (∀ (α_1) τ_1))]
  [
   (<: (mu-fold (μ (α) τ_0)) τ_1)
   --- Sub-Mu-L
   (<: (μ (α) τ_0) τ_1)]
  [
   (<: τ_0 (mu-fold (μ (α) τ_1)))
   --- Sub-Mu-R
   (<: τ_0 (μ (α) τ_1))])

(define-metafunction μTR
  subtype? : τ τ -> boolean
  [(subtype? τ_0 τ_1)
   ,(judgment-holds (<: τ_0 τ_1))])

(define-judgment-form μTR
  #:mode (subtype* I I)
  #:contract (subtype* τ* τ*)
  [
   ---
   (subtype* () τ*)]
  [
   (exists-subtype τ_0 τ*)
   (subtype* (τ_0rest ...) τ*)
   ---
   (subtype* (τ_0 τ_0rest ...) τ*)])

(define-judgment-form μTR
  #:mode (exists-subtype I I)
  #:contract (exists-subtype τ τ*)
  [
   (<: τ τ_1)
   --- Sub-First
   (exists-subtype τ (τ_1 τ_1rest ...))]
  [
   (exists-subtype τ (τ_1rest ...))
   ---
   (exists-subtype τ (τ_1 τ_1rest ...))])

;; -----------------------------------------------------------------------------

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
  #:mode (higher-order-value I)
  #:contract (higher-order-value v)
  [
   (fun-value v)
   ---
   (higher-order-value v)]
  [
   (vector-value v)
   ---
   (higher-order-value v)])

(define-judgment-form μTR
  #:mode (not-higher-order-value I)
  #:contract (not-higher-order-value v)
  [
   (not-fun-value v)
   (not-vector-value v)
   ---
   (not-higher-order-value v)])

(define-judgment-form μTR
  #:mode (vector-value I)
  #:contract (vector-value v)
  [
   ---
   (vector-value (vector x_loc))]
  [
   ---
   (vector-value (vector τ x_loc))]
  [
   ---
   (vector-value (mon-vector τ v))])

(define-judgment-form μTR
  #:mode (not-vector-value I)
  #:contract (not-vector-value v)
  [
   (side-condition ,(not (judgment-holds (vector-value v))))
   ---
   (not-vector-value v)])

(define-judgment-form μTR
  #:mode (list-value I)
  #:contract (list-value v)
  [
   ---
   (list-value nil)]
  [
   (list-value v_1)
   ---
   (list-value (cons _ v_1))])

(define-judgment-form μTR
  #:mode (not-list-value I)
  #:contract (not-list-value v)
  [
   (side-condition ,(not (judgment-holds (list-value v))))
   ---
   (not-list-value v)])

(define-judgment-form μTR
  #:mode (integer-value I)
  #:contract (integer-value v)
  [
   ---
   (integer-value integer)])

(define-judgment-form μTR
  #:mode (not-integer-value I)
  #:contract (not-integer-value v)
  [
   (side-condition ,(not (judgment-holds (integer-value v))))
   ---
   (not-integer-value v)])

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
  #:mode (not-fun-value I)
  #:contract (not-fun-value v)
  [
   (side-condition ,(not (judgment-holds (fun-value v))))
   ---
   (not-fun-value v)])

;; -----------------------------------------------------------------------------

;; Simple type inference, doesn't even do a good job.
(define-judgment-form μTR
  #:mode (infer-expression-type I I O)
  #:contract (infer-expression-type Γ e τ)
  [
   ---
   (infer-expression-type Γ natural Nat)]
  [
   (side-condition ,(< (term integer) 0))
   ---
   (infer-expression-type Γ integer Int)]
  [
   (where [_ τ] #{local-type-env-ref Γ x})
   ---
   (infer-expression-type Γ x τ)]
  [
   ---
   (infer-expression-type Γ (vector τ_vec e _ ...) τ_vec)]
  [
   (infer-expression-type Γ e_0 τ)
   ---
   (infer-expression-type Γ (cons e_0 _) (Listof τ))]
  [
   ---
   (infer-expression-type Γ (fun x_fun τ_fun (x_arg) e_body) τ_fun)]
  [
   ---
   (infer-expression-type Γ (mon-fun τ _) τ)]
  [
   ---
   (infer-expression-type Γ (mon-vector τ _) τ)])

(define-metafunction μTR
  infer-expression-type# : Γ e -> τ
  [(infer-expression-type# Γ e)
   τ
   (judgment-holds (infer-expression-type Γ e τ))]
  [(infer-expression-type# Γ e)
   ,(raise-arguments-error 'infer-expression-type "failed to infer type" "expression" (term e) "type env" (term Γ))])

(define-judgment-form μTR
  #:mode (tagged-completion I I I O)
  #:contract (tagged-completion Γ e κ e)
  [
   ;; TODO
   ---
   (tagged-completion Γ e κ 42)])

(define-judgment-form μTR
  #:mode (well-tagged-expression I I I)
  #:contract (well-tagged-expression Γ e κ)
  [
   ;; TODO
   ---
   (well-tagged-expression Γ e κ)])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "subtype?"
    (check-mf-apply*
     [(subtype? Int Int)
      #true]
     [(subtype? (Listof Int) (Listof Int))
      #true]
     [(subtype? (Listof Nat) (Listof Int))
      #true]
     [(subtype? (→ Int Nat) (→ Nat Int))
      #true]
     [(subtype? Int (U Int Nat))
      #true]
     [(subtype? Nat (U Int Nat))
      #true]
     [(subtype? (U Int Nat) (U Nat Int))
      #true]
     [(subtype? (∀ (α) (Listof α)) (∀ (α) (Listof α)))
      #true]
     [(subtype? (∀ (α) (Listof (→ α Nat))) (∀ (α) (Listof (→ α Int))))
      #true]
     [(subtype? (Listof Nat) (μ (α) (U Nat (Listof α))))
      #true]
     [(subtype? (Listof (Listof Nat)) (μ (α) (U Nat (Listof α))))
      #true]
     [(subtype? (Listof (Listof (Listof Nat))) (μ (α) (U Nat (Listof α))))
      #true]
    )
  )

  (test-case "well-tagged"
    (check-judgment-holds*
     (well-tagged-value 1 Nat)
     (well-tagged-value 1 Int)
     (well-tagged-value 1 (U Int Vector))
     (well-tagged-value (vector aaa) Vector)
     (well-tagged-value (fun f (x) x) →)
     (well-tagged-value (cons 1 (cons 3 nil)) List))

    (check-not-judgment-holds*
     (well-tagged-value 1 Vector)
     (well-tagged-value (fun f (x) x) List)
     (well-tagged-value (vector aa) List))

    (check-judgment-holds*
     (not-well-tagged-value 1 Vector))

    (check-not-judgment-holds*
     (not-well-tagged-value (fun f (x) x) →))
  )

  (test-case "flat-value"
    (check-judgment-holds*
     (flat-value 3)
     (flat-value -2)
     (flat-value nil))

    (check-not-judgment-holds*
     (flat-value (cons 3 nil))
     (flat-value (fun f (x) x))
     (flat-value (vector a))))

  (test-case "vector-value"
    (check-judgment-holds*
     (vector-value (vector aaa))
     (vector-value (mon-vector (Vectorof Int) (vector aaa)))
     (vector-value (mon-vector (Vectorof Nat) (vector (Vectorof Nat) aaa))))

    (check-not-judgment-holds*
     (vector-value (fun f (x) 3))
     (vector-value 4)
     (vector-value (cons 3 nil))))

  (test-case "fun-value"
    (check-judgment-holds*
     (fun-value (fun f (x) x))
     (fun-value (mon-fun (→ Int Int) (fun f (x) (cons 0 nil)))))

    (check-not-judgment-holds*
     (fun-value -2)
     (fun-value 2)
     (fun-value (vector aaa))))

  (test-case "well-typed-expression"
    (check-judgment-holds*
     (well-typed-expression () 2 Nat)
     (well-typed-expression () 2 Int)
     (well-typed-expression () -2 Int)
     (well-typed-expression ((x Nat)) x Nat)
     (well-typed-expression ((x (Listof Int))) x (Listof Int))
     (well-typed-expression () (fun f (→ Nat Nat) (x) x) (→ Nat Nat))
     (well-typed-expression () (fun f (→ Int (→ Int Int)) (a) (fun g (→ Int Int) (b) (+ a b))) (→ Int (→ Int Int)))
     (well-typed-expression () (vector (Vectorof Int) -1 1) (Vectorof Int))
     (well-typed-expression ((hd Int) (tl Int)) (cons hd (cons tl nil)) (Listof Int))
     (well-typed-expression ((f (→ Int (→ Int (Listof Int))))) (f 4) (→ Int (Listof Int)))
     (well-typed-expression () (ifz 2 3 -4) Int)
     (well-typed-expression () (+ 2 2) Int)
     (well-typed-expression () (+ 2 2) Nat)
     (well-typed-expression () (- -2 -2) Int)
     (well-typed-expression () (- 2 2) Int)
     (well-typed-expression () (* 2 2) Int)
     (well-typed-expression () (* 2 2) Nat)
     (well-typed-expression () (% 2 2) Int)
     (well-typed-expression () (% 2 2) Nat)
     (well-typed-expression () (vector-ref (vector (Vectorof Int) 0) 10) Int)
     (well-typed-expression () (vector-set! (vector (Vectorof Int) 0) 1 2) Int)
     (well-typed-expression () (first nil) Int)
     (well-typed-expression () (rest nil) (Listof (Listof Int)))

     (well-typed-expression () (vector (Vectorof Nat) 1 2) (Vectorof Nat))
    )

    (check-not-judgment-holds*
     (well-typed-expression () -2 Nat)
     (well-typed-expression () (ifz (vector (Vectorof Int) 0) 3 -4) Int)
    )
  )

  (test-case "infer-expression-type"
    (check-mf-apply*
     ((infer-expression-type# () 1)
      Nat)
     ((infer-expression-type# () -3)
      Int)
     ((infer-expression-type# ((x Nat)) x)
      Nat)
     ((infer-expression-type# () (vector (Vectorof Nat) 1 2 3))
      (Vectorof Nat))
     ((infer-expression-type# () (vector (Vectorof Int) 1 2 3))
      (Vectorof Int))
     ((infer-expression-type# () (cons 1 nil))
      (Listof Nat))
     ((infer-expression-type# () (mon-fun (→ (Listof Nat) Int) (fun f (x) 0)))
      (→ (Listof Nat) Int))
     ((infer-expression-type# () (mon-vector (Vectorof (→ Nat Nat)) (vector (Vectorof (→ Nat Nat)) zz)))
      (Vectorof (→ Nat Nat)))))

  (test-case "well-dyn-expression"
    (check-judgment-holds*
     (well-dyn-expression () 4)
     (well-dyn-expression () (fun f (x) x))
     (well-dyn-expression () nil)
     (well-dyn-expression ((x TST)) x)
     (well-dyn-expression () (vector 1 2 3))
     (well-dyn-expression () (cons 1 nil))
     (well-dyn-expression ((f TST) (x TST)) (f x))
     (well-dyn-expression () (ifz 1 2 3))
     (well-dyn-expression () (+ 2 2))
     (well-dyn-expression () (- 2 2))
     (well-dyn-expression () (* 2 2))
     (well-dyn-expression () (% 2 2))
     (well-dyn-expression () (vector-ref (vector 1) 0))
     (well-dyn-expression () (vector-set! (vector 1) 2 3))
     (well-dyn-expression () (first nil))
     (well-dyn-expression () (rest nil))

     (well-dyn-expression () (+ nil 1))
     (well-dyn-expression () (ifz (vector 0) 3 -4)))

    (check-not-judgment-holds*
     (well-dyn-expression ((f (→ Int Int)) (x Int)) (f x))))

  (test-case "local-type-env->provided"
    (check-mf-apply*
     ((local-type-env->provided () (provide))
      ())
     ((local-type-env->provided ((x Int)) (provide x))
      ((x Int)))
     ((local-type-env->provided ((x Int) (y Int)) (provide x y))
      ((x Int) (y Int)))
     ((local-type-env->provided ((x Int) (y Int)) (provide x))
      ((x Int)))
     ((local-type-env->provided ((x Int) (y Int)) (provide y))
      ((y Int))))

    (check-exn exn:fail:contract?
      (λ () (term #{local-type-env->provided () (provide x)})))
    (check-exn exn:fail:contract?
      (λ () (term #{local-type-env->provided ((y Int)) (provide x)})))
  )

  (test-case "define->local-type-env"
    (check-mf-apply*
     ((define->local-type-env ((define x 0) (define y 1)))
      ((x TST) (y TST)))
     ((define->local-type-env ((define x (vector 1 2)) (define y (fun fn (a) 3))))
      ((x TST) (y TST)))
     ((define->local-type-env ((define x Int (vector 1)) (define y (→ Nat Nat) (fun fn (a) 4))))
      ((x Int) (y (→ Nat Nat))))))

  (test-case "valid-require"
    (check-judgment-holds*
     (valid-require () ())
     (valid-require ((x TST) (y TST)) ((x TST) (y TST)))
     (valid-require ((x TST) (y TST)) ((x TST) (y TST) (z TST)))
     (valid-require ((x TST) (y TST)) ((x (→ Nat Nat)) (y Nat)))
     (valid-require ((x Int) (y (→ Nat Nat))) ((x TST) (y TST)))
     (valid-require ((x Int) (y (→ Nat Nat))) ((x Int) (y (→ Nat Nat))))
     (valid-require ((x Int) (y (→ Nat Nat))) ((x Nat) (y (→ Int Nat))))
    )

    (check-exn exn:fail:contract?
     (λ () (judgment-holds (valid-require ((x TST) (y TST)) ((y Nat)))))))

  (test-case "require->local-type-env"
    (check-mf-apply*
     ((require->local-type-env () ())
      ())
     ((require->local-type-env ((M0 ((x Int)))) ((require M0 x)))
      ((x TST)))
     ((require->local-type-env ((M0 ((x TST)))) ((require M0 x)))
      ((x TST)))
     ((require->local-type-env ((M0 ((x Int)))) ((require M0 ((x Int)))))
      ((x Int)))
     ((require->local-type-env ((M0 ((x TST)))) ((require M0 ((x Int)))))
      ((x Int)))
     ((require->local-type-env ((M0 ((x TST))) (M1 ((y TST))))
                               ((require M0 x) (require M1 y)))
      ((x TST) (y TST)))
     ((require->local-type-env ((M0 ((x TST))) (M1 ((y TST))))
                               ((require M0 ((x (→ Nat Nat)))) (require M1 ((y (Vectorof Int))))))
      ((x (→ Nat Nat)) (y (Vectorof Int))))
     ((require->local-type-env ((M0 ((x (→ Nat Nat)))) (M1 ((y (Vectorof Int)))))
                               ((require M0 ((x (→ Nat Nat)))) (require M1 ((y (Vectorof Int))))))
      ((x (→ Nat Nat)) (y (Vectorof Int))))
     ((require->local-type-env ((M0 ((x (→ Nat Nat)))) (M1 ((y (Vectorof Int)))))
                               ((require M0 x) (require M1 y)))
      ((x TST) (y TST)))))

  (test-case "well-typed-program:I"
    (check-mf-apply*

     ((well-typed-program#
       ((module mu UN
         (define x 4)
         (provide x))))
      ((mu ((x TST)))))

     ((well-typed-program#
       ((module mt TY
         (define x Int 4)
         (provide x))))
      ((mt ((x Int)))))

     ((well-typed-program#
       ((module M UN
         (define x (+ 2 2))
         (provide x))))
      ((M ((x TST)))))

     ((well-typed-program#
       ((module M UN
         (define x 2)
         (define y (+ x x))
         (provide x y))))
      ((M ((x TST) (y TST)))))

     ((well-typed-program#
       ((module M UN
         (define x (fun a (b) (+ b 1)))
         (define y (x 4))
         (provide y))))
      ((M ((y TST)))))

     ((well-typed-program#
       ((module M typed
         (define fact (→ Int Int)
           (fun fact (→ Int Int) (n) (ifz n 1 (* n (fact (- n 1))))))
         (define f0 Int (fact 0))
         (define f1 Int (fact 1))
         (define f2 Int (fact 2))
         (define f3 Int (fact 3))
         (define f4 Int (fact 4))
         (provide f0 f1 f2 f3 f4))))
      ((M ((f0 Int) (f1 Int) (f2 Int) (f3 Int) (f4 Int)))))

     ((well-typed-program#
       ((module M typed
         (define v (Vectorof Int) (vector (Vectorof Int) 1 2 (+ 2 1)))
         (define x Int (vector-ref v 2))
         (define dontcare Int (vector-set! v 0 0))
         (define y Int (vector-ref v 0))
         (provide x y))))
      ((M ((x Int) (y Int)))))

     ((well-typed-program#
       ((module M typed
         (define second (→ (Listof Int) Int) (fun f (→ (Listof Int) Int) (xs) (first (rest xs))))
         (define v Int (second (cons 1 (cons 2 nil))))
         (provide v))))
      ((M ((v Int)))))

     ((well-typed-program#
       ((module M0 untyped
         (define x (+ 1 nil))
         (provide))
        (module M1 untyped
         (define x (vector-ref 4 4))
         (provide))
        (module M2 untyped
         (define x (4 4))
         (provide))))
      ((M0 ()) (M1 ()) (M2 ())))

     ((well-typed-program#
      ((module M0 typed
        (define x Int (% 1 0))
        (provide))
       (module M1 untyped
        (define x (% 1 0))
        (provide))
       (module M2 typed
        (define x Int (first nil))
        (provide))
       (module M3 untyped
        (define x (rest nil))
        (provide))
       (module M4 typed
        (define x Int (vector-ref (vector (Vectorof Int) 1) 999))
        (provide))
       (module M5 untyped
        (define x (vector-set! (vector 0) 4 5))
        (provide))))
      ((M0 ()) (M1 ()) (M2 ()) (M3 ()) (M4 ()) (M5 ())))

     ((well-typed-program#
      ((module M0 typed
        (define v (Vectorof Int) (vector (Vectorof Int) 0))
        (provide v))
       (module M1 untyped
        (require M0 v)
        (define x (vector-set! v 0 nil))
        (provide))))
      ((M0 ((v (Vectorof Int)))) (M1 ())))

     ((well-typed-program#
      ((module M0 untyped
        (define v (vector -1))
        (provide v))
       (module M1 typed
        (require M0 ((v (Vectorof Nat))))
        (define x Nat (vector-ref v 0))
        (provide))))
      ((M0 ((v TST))) (M1 ())))

     ((well-typed-program#
      ((module M0 untyped
        (define v -1)
        (provide v))
       (module M1 typed
        (require M0 ((v Nat)))
        (define x Int 42)
        (provide))))
      ((M0 ((v TST))) (M1 ())))

     ((well-typed-program#
      ((module M0 typed
        (define f (→ Nat Nat) (fun f (→ Nat Nat) (x) (+ x 2)))
        (provide f))
       (module M1 untyped
        (require M0 f)
        (define x (f -1))
        (provide))))
      ((M0 ((f (→ Nat Nat)))) (M1 ())))

     ((well-typed-program#
      ((module M0 untyped
        (define f (fun f (x) nil))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int Int))))
        (define x Int (f 3))
        (provide))))
      ((M0 ((f TST))) (M1 ())))

     ((well-typed-program#
      ((module M0 untyped
        (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int (→ Int Int)))))
        (define f2 (→ Int Int) (f 2))
        (define f23 Int (f2 3))
        (provide f23))))
      ((M0 ((f TST))) (M1 ((f23 Int)))))

     ((well-typed-program#
      ((module M0 untyped
        (define f (fun a (x) (fun b (y) (fun c (z) (+ (+ a b) c)))))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Int (→ Int Int)))))
        (provide f))
       (module M2 untyped
        (require M1 f)
        (define f2 (f 2))
        (define f23 (f2 3))
        (provide))))
      ((M0 ((f TST))) (M1 ((f (→ Int (→ Int Int))))) (M2 ())))

     ((well-typed-program#
      ((module M0 untyped
        (define f (fun a (x) (vector-ref x 0)))
        (provide f))
       (module M1 typed
        (require M0 ((f (→ Nat Nat))))
        (define v Nat (f 4))
        (provide))))
      ((M0 ((f TST))) (M1 ())))
    )

    (check-mf-apply*
     ((well-typed-program#
      ((module M typed
        (define x Int (first 4))
        (provide))))
      #f)
     ((well-typed-program#
       ((module M typed
         (define x Int (+ 1 nil))
         (provide))))
      #f))
  )
)
