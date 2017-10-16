#lang mf-apply racket/base

(provide
  <:
  subtype?
  not-well-tagged-value
  well-tagged-value

  flat-value

  higher-order-value
  not-higher-order-value

  vector-value
  fun-value
  not-fun-value
  not-vector-value

  well-typed-program
  well-typed-state
  well-typed-expression

  runtime-env-models
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define-judgment-form μTR
  #:mode (<: I I)
  #:contract (<: τ τ)
  [
   ---
   (<: Nat Int)]
  [
   --- Sub-Refl
   (<: τ τ)])

(define-metafunction μTR
  subtype? : τ τ -> boolean
  [(subtype? τ_0 τ_1)
   ,(judgment-holds (<: τ_0 τ_1))])

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
   (vector-value (mon-vector x τ v))])

(define-judgment-form μTR
  #:mode (not-vector-value I)
  #:contract (not-vector-value v)
  [
   (side-condition ,(not (judgment-holds (vector-value v))))
   ---
   (not-vector-value v)])

(define-judgment-form μTR
  #:mode (fun-value I)
  #:contract (fun-value v)
  [
   ---
   (fun-value Λ)]
  [
   ---
   (fun-value (mon-fun x τ v))])

(define-judgment-form μTR
  #:mode (not-fun-value I)
  #:contract (not-fun-value v)
  [
   (side-condition ,(not (judgment-holds (fun-value v))))
   ---
   (not-fun-value v)])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (runtime-env-models I I I)
  #:contract (runtime-env-models ρ Γ x*)
  [
   (same-domain ρλ Γ)
   (well-typed-runtime-env Γ ρλ x*)
   ---
   (runtime-env-models ρλ Γ x*)]
  [
   (same-domain ρτ Γ)
   (well-typed-runtime-env Γ ρτ x*)
   ---
   (runtime-env-models ρτ Γ x*)])

(define-judgment-form μTR
  #:mode (well-typed-runtime-env I I I)
  #:contract (well-typed-runtime-env Γ ρ x*)
  [
   ---
   (well-typed-runtime-env Γ () x*)]
  [
   (where [_ τ_1] #{type-env-ref Γ x_0})
   (<: τ_0 τ_1)
   (well-typed-expression Γ v_0 τ_0 x*)
   (well-typed-runtime-env Γ (x:v:τ ...) x*)
   ---
   (well-typed-runtime-env Γ ((x_0 v_0 τ_0) x:v:τ ...) x*)]
  [
   (where [_ τ] #{type-env-ref Γ x_0})
   (well-typed-expression Γ v_0 τ x*)
   (well-typed-runtime-env Γ (x:v ...) x*)
   ---
   (well-typed-runtime-env Γ ((x_0 v_0) x:v ...) x*)])

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-typed-state I I I)
  #:contract (well-typed-state Σ τ x*)
  [
   (typed-module x_mod x*) ;; No rule for empty stack and untyped module
   (where e_sub #{unload-store e σ})
   (well-typed-expression () e_sub τ x*)
   ---
   (well-typed-state (e σ x_mod ()) τ x*)]
  [
   (typed-module x_mod x*)
   (where τ_e (frame->type FRAME))
   (where τ (stack-outermost-type S τ_e))
   (where e_sub (unload-store e σ))
   (well-typed-expression () e_sub τ_e x*)
   ---
   (well-typed-state (e σ x_mod (FRAME S)) τ x*)]
  [
   (untyped-module x_mod x*)
   (where τ_e (frame->type FRAME))
   (where τ (stack-outermost-type S τ_e))
   (where e_sub (unload-store e σ))
   (well-dyn-expression () e_sub x*)
   ---
   (well-typed-state (e σ x_mod (FRAME S)) τ x*)])

(define-judgment-form μTR
  #:mode (well-typed-expression I I I I)
  #:contract (well-typed-expression Γ e τ x*)
  [
   ---
   (well-typed-expression Γ natural Nat _)]
  [
   ---
   (well-typed-expression Γ integer Int _)]
  [
   (where [_ τ] #{type-env-ref Γ x})
   ---
   (well-typed-expression Γ x τ _)]
  [
   (where (→ τ_dom τ_cod) τ)
   (where Γ_f #{type-env-set Γ x_f τ})
   (where Γ_x #{type-env-set Γ_f x_arg τ_dom})
   (well-typed-expression Γ_x e_body τ_cod x*)
   ---
   (well-typed-expression Γ (fun x_f (x_arg) e_body) τ x*)]
  [
   (<: τ_fun τ)
   (where (→ τ_dom τ_cod) τ)
   (where Γ_f #{type-env-set Γ x_fun τ_fun})
   (where Γ_x #{type-env-set Γ_f x_arg τ_dom})
   (well-typed-expression Γ_x e_body τ_cod x*)
   ---
   (well-typed-expression Γ (fun x_fun τ_fun (x_arg) e_body) τ x*)]
  [
   (typed-module x_mod x*)
   (well-typed-expression Γ v τ x*)
   ---
   (well-typed-expression Γ (mon-fun x_mod τ v) τ x*)]
  [
   (untyped-module x_mod x*)
   (well-dyn-expression Γ v x*)
   ---
   (well-typed-expression Γ (mon-fun x_mod τ v) τ x*)]
  [
   (typed-module x_mod x*)
   (well-typed-expression Γ e τ x*)
   ---
   (well-typed-expression Γ (mon-vector x_mod τ e) τ x*)]
  [
   (untyped-module x_mod x*)
   (well-dyn-expression Γ e x*)
   ---
   (well-typed-expression Γ (mon-vector x_mod τ e) τ x*)]
  [
   (where (Vectorof τ_elem) τ)
   (well-typed-expression Γ e τ_elem x*) ...
   ---
   (well-typed-expression Γ (vector e ...) τ x*)]
  [
   (where (Listof τ_elem) τ)
   (well-typed-expression Γ e_0 τ_elem x*)
   (well-typed-expression Γ e_1 τ x*)
   ---
   (well-typed-expression Γ (cons e_0 e_1) τ x*)]
  [
   (where (Listof τ_elem) τ)
   ---
   (well-typed-expression Γ nil τ _)]
  [
   (infer-expression-type Γ e_fun τ)
   (where (→ τ_dom τ_cod) τ)
   (well-typed-expression Γ e_fun τ x*)
   (well-typed-expression Γ e_arg τ_dom x*)
   ---
   (well-typed-expression Γ (e_fun e_arg) τ_cod x*)]
  [
   (well-typed-expression Γ e_0 Int x*)
   (well-typed-expression Γ e_1 τ x*)
   (well-typed-expression Γ e_2 τ x*)
   ---
   (well-typed-expression Γ (ifz e_0 e_1 e_2) τ x*)]
  [
   (well-typed-expression Γ e_0 Int x*)
   (well-typed-expression Γ e_1 Int x*)
   ---
   (well-typed-expression Γ (+ e_0 e_1) Int x*)]
  [
   (well-typed-expression Γ e_0 Nat x*)
   (well-typed-expression Γ e_1 Nat x*)
   ---
   (well-typed-expression Γ (+ e_0 e_1) Nat x*)]
  [
   (well-typed-expression Γ e_0 Int x*)
   (well-typed-expression Γ e_1 Int x*)
   ---
   (well-typed-expression Γ (- e_0 e_1) Int x*)]
  [
   (well-typed-expression Γ e_0 Int x*)
   (well-typed-expression Γ e_1 Int x*)
   ---
   (well-typed-expression Γ (* e_0 e_1) Int x*)]
  [
   (well-typed-expression Γ e_0 Nat x*)
   (well-typed-expression Γ e_1 Nat x*)
   ---
   (well-typed-expression Γ (* e_0 e_1) Nat x*)]
  [
   (well-typed-expression Γ e_0 Int x*)
   (well-typed-expression Γ e_1 Int x*)
   ---
   (well-typed-expression Γ (% e_0 e_1) Int x*)]
  [
   (well-typed-expression Γ e_0 Nat x*)
   (well-typed-expression Γ e_1 Nat x*)
   ---
   (well-typed-expression Γ (% e_0 e_1) Nat x*)]
  [
   (well-typed-expression Γ e_vec (Vectorof τ) x*)
   (well-typed-expression Γ e_i Int x*)
   ---
   (well-typed-expression Γ (vector-ref e_vec e_i) τ x*)]
  [
   (well-typed-expression Γ e_vec (Vectorof τ) x*)
   (well-typed-expression Γ e_i Int x*)
   (well-typed-expression Γ e_val τ x*)
   ---
   (well-typed-expression Γ (vector-set! e_vec e_i e_val) τ x*)]
  [
   (well-typed-expression Γ e (Listof τ) x*)
   ---
   (well-typed-expression Γ (first e) τ x*)]
  [
   (where (Listof τ_elem) τ)
   (well-typed-expression Γ e τ x*)
   ---
   (well-typed-expression Γ (rest e) τ x*)]
  ;; ignore the `!!` form
)

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
   (where [_ τ] #{type-env-ref Γ x})
   ---
   (infer-expression-type Γ x τ)]
  [
   (infer-expression-type Γ e τ)
   ---
   (infer-expression-type Γ (vector e _ ...) (Vectorof τ))]
  [
   (infer-expression-type Γ e_0 τ)
   ---
   (infer-expression-type Γ (cons e_0 _) (Listof τ))]
  [
   ---
   (infer-expression-type Γ (fun x_fun τ (x_arg) e_body) τ)]
  [
   ---
   (infer-expression-type Γ (mon-fun _ τ _) τ)]
  [
   ---
   (infer-expression-type Γ (mon-vector _ τ _) τ)])

(define-metafunction μTR
  infer-expression-type# : Γ e -> τ
  [(infer-expression-type# Γ e)
   τ
   (judgment-holds (infer-expression-type Γ e τ))]
  [(infer-expression-type# Γ e)
   ,(raise-arguments-error 'infer-expression-type "failed to infer type" "expression" (term e) "type env" (term Γ))])

(define-judgment-form μTR
  #:mode (well-dyn-expression I I I)
  #:contract (well-dyn-expression Γ e x*)
  [
   ---
   (well-dyn-expression Γ integer x*)]
  [
   (where Γ_f #{type-env-set Γ x_fun Dyn})
   (where Γ_x #{type-env-set Γ_f x_arg Dyn})
   (well-dyn-expression Γ_x e x*)
   ---
   (well-dyn-expression Γ (fun x_fun (x_arg) e) x*)]
  [
   (side-condition ,(raise-user-error 'well-dyn-expression "unsound: typed function in untyped code ~a" (term (fun x_fun τ (x_arg) e))))
   ---
   (well-dyn-expression Γ (fun x_fun τ (x_arg) e) x*)]
  [
   ---
   (well-dyn-expression Γ nil x*)]
  [
   (typed-module x_mod x*)
   (well-typed-expression Γ v τ x*)
   ---
   (well-dyn-expression Γ (mon-fun x_mod τ v) x*)]
  [
   (untyped-module x_mod x*)
   (well-dyn-expression Γ v x*)
   ---
   (well-dyn-expression Γ (mon-fun x_mod τ v) x*)]
  [
   (typed-module x_mod x*)
   (well-typed-expression Γ e τ x*)
   ---
   (well-dyn-expression Γ (mon-vector x_mod τ e) x*)]
  [
   (untyped-module x_mod x*)
   (well-dyn-expression Γ e x*)
   ---
   (well-dyn-expression Γ (mon-vector x_mod τ e) x*)]
  [
   (where _ #{type-env-ref Γ x})
   ---
   (well-dyn-expression Γ x x*)]
  [
   (well-dyn-expression Γ e x*) ...
   ---
   (well-dyn-expression Γ (vector e ...) x*)]
  [
   (well-dyn-expression Γ e_hd x*)
   (well-dyn-expression Γ e_tl x*)
   ---
   (well-dyn-expression Γ (cons e_hd e_tl) x*)]
  [
   (well-dyn-expression Γ e_fun x*)
   (well-dyn-expression Γ e_arg x*)
   ---
   (well-dyn-expression Γ (e_fun e_arg) x*)]
  [
   (well-dyn-expression Γ e_0 x*)
   (well-dyn-expression Γ e_1 x*)
   (well-dyn-expression Γ e_2 x*)
   ---
   (well-dyn-expression Γ (ifz e_0 e_1 e_2) x*)]
  [
   (well-dyn-expression Γ e_0 x*)
   (well-dyn-expression Γ e_1 x*)
   ---
   (well-dyn-expression Γ (+ e_0 e_1) x*)]
  [
   (well-dyn-expression Γ e_0 x*)
   (well-dyn-expression Γ e_1 x*)
   ---
   (well-dyn-expression Γ (- e_0 e_1) x*)]
  [
   (well-dyn-expression Γ e_0 x*)
   (well-dyn-expression Γ e_1 x*)
   ---
   (well-dyn-expression Γ (* e_0 e_1) x*)]
  [
   (well-dyn-expression Γ e_0 x*)
   (well-dyn-expression Γ e_1 x*)
   ---
   (well-dyn-expression Γ (% e_0 e_1) x*)]
  [
   (well-dyn-expression Γ e_vec x*)
   (well-dyn-expression Γ e_i x*)
   ---
   (well-dyn-expression Γ (vector-ref e_vec e_i) x*)]
  [
   (well-dyn-expression Γ e_vec x*)
   (well-dyn-expression Γ e_i x*)
   (well-dyn-expression Γ e_arg x*)
   ---
   (well-dyn-expression Γ (vector-set! e_vec e_i e_arg) x*)]
  [
   (well-dyn-expression Γ e x*)
   ---
   (well-dyn-expression Γ (first e) x*)]
  [
   (well-dyn-expression Γ e x*)
   ---
   (well-dyn-expression Γ (rest e) x*)])

(define-judgment-form μTR
  #:mode (well-typed-program I I)
  #:contract (well-typed-program any P)
  [
   ---
   (well-typed-program () P)])

;; well-typed-program/env
;; well-typed-module
;; well-typed-expression


;; -----------------------------------------------------------------------------

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "subtype?"
    (check-mf-apply*
     [(subtype? Int Int)
      #true])
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
     (vector-value (mon-vector lbl (Vectorof Int) (vector aaa)))
     (vector-value (mon-vector lbl (Vectorof Nat) (vector aaa))))

    (check-not-judgment-holds*
     (vector-value (fun f (x) 3))
     (vector-value 4)
     (vector-value (cons 3 nil))))

  (test-case "fun-value"
    (check-judgment-holds*
     (fun-value (fun f (x) x))
     (fun-value (mon-fun lbl (→ Int Int) (fun f (x) (cons 0 nil)))))

    (check-not-judgment-holds*
     (fun-value -2)
     (fun-value 2)
     (fun-value (vector aaa))))

  (test-case "well-typed-expression"
    (check-judgment-holds*
     (well-typed-expression () 2 Nat ())
     (well-typed-expression () 2 Int ())
     (well-typed-expression () -2 Int ())
     (well-typed-expression ((x Nat)) x Nat ())
     (well-typed-expression ((x (Listof Int))) x (Listof Int) ())
     (well-typed-expression () (fun f (x) x) (→ Nat Nat) ())
     (well-typed-expression () (fun f (a) (fun g (b) (+ a b))) (→ Int (→ Int Int)) ())
     (well-typed-expression () (mon-fun Mt (→ Nat Nat) (fun f (x) 3)) (→ Nat Nat) (Mt))
     (well-typed-expression () (mon-fun Mu (→ Nat Nat) (fun f (x) nil)) (→ Nat Nat) ())
     (well-typed-expression () (mon-vector Mt (Vectorof Nat) (vector 1)) (Vectorof Nat) (Mt))
     (well-typed-expression () (mon-vector Mu (Vectorof Nat) (vector 1)) (Vectorof Nat) (Mu))
     (well-typed-expression () (vector -1 1) (Vectorof Int) ())
     (well-typed-expression ((hd Int) (tl Int)) (cons hd (cons tl nil)) (Listof Int) ())
     (well-typed-expression ((f (→ Int (→ Int (Listof Int))))) (f 4) (→ Int (Listof Int)) ())
     (well-typed-expression () (ifz 2 3 -4) Int ())
     (well-typed-expression () (+ 2 2) Int ())
     (well-typed-expression () (+ 2 2) Nat ())
     (well-typed-expression () (- -2 -2) Int ())
     (well-typed-expression () (- 2 2) Int ())
     (well-typed-expression () (* 2 2) Int ())
     (well-typed-expression () (* 2 2) Nat ())
     (well-typed-expression () (% 2 2) Int ())
     (well-typed-expression () (% 2 2) Nat ())
     (well-typed-expression () (vector-ref (vector 0) 10) Int ())
     (well-typed-expression () (vector-set! (vector 0) 1 2) Int ())
     (well-typed-expression () (first nil) Int ())
     (well-typed-expression () (rest nil) (Listof (Listof Int)) ())

     (well-typed-expression () (vector 1 2) (Vectorof Nat) (M))
    )

    (check-not-judgment-holds*
     (well-typed-expression () -2 Nat ())
     (well-typed-expression () (ifz (vector 0) 3 -4) Int ())
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
     ((infer-expression-type# () (vector 1 2 3))
      (Vectorof Nat))
     ((infer-expression-type# () (cons 1 nil))
      (Listof Nat))
     ((infer-expression-type# () (mon-fun M (→ (Listof Nat) Int) (fun f (x) 0)))
      (→ (Listof Nat) Int))
     ((infer-expression-type# () (mon-vector M (Vectorof (→ Nat Nat)) (vector)))
      (Vectorof (→ Nat Nat)))))

  (test-case "well-dyn-expression"

    (check-judgment-holds*
     (well-dyn-expression () 4 ())
     (well-dyn-expression () (fun f (x) x) ())
     (well-dyn-expression () nil ())
     (well-dyn-expression () (mon-fun M (→ Nat Nat) (fun f (x) x)) (M))
     (well-dyn-expression () (mon-fun M (→ Nat Nat) (fun f (x) x)) ())
     (well-dyn-expression () (mon-vector M (Vectorof Nat) (vector 1 2)) (M))
     (well-dyn-expression () (mon-vector M (Vectorof Nat) (vector -1 2)) ())
     (well-dyn-expression ((x Nat)) x ())
     (well-dyn-expression () (vector 1 2 3) ())
     (well-dyn-expression () (cons 1 nil) ())
     (well-dyn-expression ((f (→ Int Int)) (x Int)) (f x) ())
     (well-dyn-expression () (ifz 1 2 3) ())
     (well-dyn-expression () (+ 2 2) ())
     (well-dyn-expression () (- 2 2) ())
     (well-dyn-expression () (* 2 2) ())
     (well-dyn-expression () (% 2 2) ())
     (well-dyn-expression () (vector-ref (vector 1) 0) ())
     (well-dyn-expression () (vector-set! (vector 1) 2 3) ())
     (well-dyn-expression () (first nil) ())
     (well-dyn-expression () (rest nil) ())

     (well-dyn-expression () (+ nil 1) ())
     (well-dyn-expression () (ifz (vector 0) 3 -4) ())
   )

   (check-not-judgment-holds*
     (well-dyn-expression () (mon-vector M (Vectorof Nat) (vector -1 2)) (M))
   )
  )

  (test-case "well-typed-state"

    (check-judgment-holds*
     (well-typed-state (2 () M ()) Int (M))
     (well-typed-state ((fun f (x) x) () M ()) (→ Nat Nat) (M))
     (well-typed-state ((vector x) ((x (1 2 3))) M ()) (Vectorof Nat) (M))

     (well-typed-state
       ((vector 2) () Mt
        ((Mu (+ 1 hole) (Vectorof Int)) ((Mt hole Nat) ())))
       Nat (Mt))

     (well-typed-state
       ((+ 2 nil) () Mu
        ((Mt (+ 1 hole) Int) ()))
       Int (Mt))
    )
  )

  (test-case "runtime-env-models"
    (check-judgment-holds*
     (runtime-env-models () () ())
     (runtime-env-models ((x 4)) ((x Nat)) ())
     (runtime-env-models ((x (cons 1 nil))) ((x (Listof Int))) ())
     (runtime-env-models ((x 2) (y (fun f (x) (+ x x)))) ((x Int) (y (→ Int Int))) ())
    )

    (check-not-judgment-holds*
     (runtime-env-models () ((x Int)) ())
     (runtime-env-models ((x 2)) () ())
     (runtime-env-models ((x 2)) ((x (Listof Int))) ())
     (runtime-env-models ((x (fun f (x) 3))) ((x Nat)) ())
    )
  )
)
