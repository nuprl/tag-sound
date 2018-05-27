#lang mf-apply racket/base

;; Static tag checking

(provide
  well-tagged-expression
  tagged-completion
)

(require
  "lang.rkt"
  "metafunctions.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define-judgment-form μTR
  #:mode (tagged-completion I I I O)
  #:contract (tagged-completion Γ e κ e)
  [
   (or-TST Nat κ)
   --- C-Nat
   (tagged-completion Γ natural κ natural)]
  [
   (or-TST Int κ)
   --- C-Int
   (tagged-completion Γ integer κ integer)]
  [
   (or-TST → κ_fun)
   (where (fun x_fun τ_fun (x_arg) e_body) Λ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ_fun})
   (where κ_dom #{type->tag τ_dom})
   (where κ_cod #{type->tag τ_cod})
   (where Γ_fun #{local-type-env-set Γ x_fun τ_fun})
   (where Γ_x #{local-type-env-set Γ_fun x_arg τ_dom})
   (tagged-completion Γ_x e_body κ_cod e_+)
   (where τ_fun+ #{weaken-arrow-domain τ_fun})
   (where Λ_+ (fun x_fun τ_fun+ (x_arg)
                ((fun x_fun τ_fun (x_arg) e_+)
                 (from-untyped κ_dom x_arg))))
   --- C-Fun
   (tagged-completion Γ Λ κ_fun Λ_+)]
  [
   (or-TST Vector κ_vec)
   (tagged-completion Γ e TST e_+) ...
   --- C-Make
   (tagged-completion Γ (make-vector τ e ...) κ_vec (make-vector τ e_+ ...))]
  [
   (or-TST List κ_cons)
   (tagged-completion Γ e_0 TST e_0+)
   (tagged-completion Γ e_1 List e_1+)
   --- C-Cons
   (tagged-completion Γ (cons e_0 e_1) κ_cons (cons e_0+ e_1+))]
  [
   (or-TST List κ_nil)
   --- C-Nil
   (tagged-completion Γ nil κ_nil nil)]
  [
   (where (_ τ) #{local-type-env-ref Γ x})
   (tag-of τ κ)
   (or-TST κ κ_x)
   --- C-Var
   (tagged-completion Γ x κ_x x)]
  [
   (tagged-completion Γ e_0 → e_0+)
   (tagged-completion Γ e_1 TST e_1+)
   (where e_+ ,(if (equal? (term TST) (term κ))
                 (term (e_0+ e_1+))
                 (term (from-untyped κ (from-typed TST (e_0+ e_1+))))))
   --- C-App
   (tagged-completion Γ (e_0 e_1) κ e_+)]
  [
   (tagged-completion Γ e_0 Int e_0+)
   (tagged-completion Γ e_1 κ e_1+)
   (tagged-completion Γ e_2 κ e_2+)
   --- C-Ifz
   (tagged-completion Γ (ifz e_0 e_1 e_2) κ (ifz e_0+ e_1+ e_2+))]
  [
   (tagged-completion Γ e_0 Nat e_0+)
   (tagged-completion Γ e_1 Nat e_1+)
   --- C-Plus0
   (tagged-completion Γ (+ e_0 e_1) Nat (+ e_0+ e_1+))]
  [
   (or-TST Int κ)
   (tagged-completion Γ e_0 Int e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   --- C-Plus1
   (tagged-completion Γ (+ e_0 e_1) κ (+ e_0+ e_1+))]
  [
   (or-TST Int κ)
   (tagged-completion Γ e_0 Int e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   --- C-Minus
   (tagged-completion Γ (- e_0 e_1) κ (- e_0+ e_1+))]
  [
   (tagged-completion Γ e_0 Nat e_0+)
   (tagged-completion Γ e_1 Nat e_1+)
   --- C-Times0
   (tagged-completion Γ (* e_0 e_1) Nat (* e_0+ e_1+))]
  [
   (or-TST Int κ)
   (tagged-completion Γ e_0 Int e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   --- C-Times1
   (tagged-completion Γ (* e_0 e_1) κ (* e_0+ e_1+))]
  [
   (tagged-completion Γ e_0 Nat e_0+)
   (tagged-completion Γ e_1 Nat e_1+)
   --- C-Div0
   (tagged-completion Γ (% e_0 e_1) Nat (% e_0+ e_1+))]
  [
   (or-TST Int κ)
   (tagged-completion Γ e_0 Int e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   --- C-Div1
   (tagged-completion Γ (% e_0 e_1) κ (% e_0+ e_1+))]
  [
   (tagged-completion Γ e_0 Vector e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   (where e_+ (from-untyped κ (from-typed κ (vector-ref e_0+ e_1+))))
   --- C-Ref
   (tagged-completion Γ (vector-ref e_0 e_1) κ e_+)]
  [
   (tagged-completion Γ e_0 Vector e_0+)
   (tagged-completion Γ e_1 Int e_1+)
   (tagged-completion Γ e_2 κ e_2+)
   --- C-Set
   (tagged-completion Γ (vector-set! e_0 e_1 e_2) κ (vector-set! e_0+ e_1+ e_2+))]
  [
   (tagged-completion Γ e List e_+)
   --- C-First
   (tagged-completion Γ (first e) κ (from-untyped κ (first e_+)))]
  [
   (or-TST List κ)
   (tagged-completion Γ e List e_+)
   --- C-Rest
   (tagged-completion Γ (rest e) κ (rest e_+))]
  [
   (tagged-completion Γ e κ e_+)
   --- C-Union
   (tagged-completion Γ e (U κ_0 ... κ κ_1 ...) e_+)])

(define-metafunction μTR
  tagged-completion# : Γ e κ -> e
  [(tagged-completion# Γ e κ)
   e_+
   (judgment-holds (tagged-completion Γ e κ e_+))]
  [(tagged-completion# Γ e κ)
   ,(raise-arguments-error 'tagged-completion "failed to complete"
     "expr" (term e)
     "tag" (term κ)
     "type env" (term Γ))])

(define-judgment-form μTR
  #:mode (well-tagged-expression I I I)
  #:contract (well-tagged-expression Γ e κ)
  [
   (or-TST Nat κ)
   ---
   (well-tagged-expression Γ natural κ)]
  [
   (or-TST Int κ)
   ---
   (well-tagged-expression Γ integer κ)]
  [
   (or-TST → κ)
   (where (→ τ_dom τ_cod) #{coerce-arrow-type τ_fun})
   (tag-of τ_cod κ_cod)
   (where Γ_fun #{local-type-env-set Γ x_fun τ_fun})
   (where Γ_x #{local-type-env-set Γ_fun x_arg τ_dom})
   (well-tagged-expression Γ_x e κ_cod)
   ---
   (well-tagged-expression Γ (fun x_fun τ_fun (x_arg) e) κ)]
  [
   (or-TST Vector κ)
   (well-tagged-expression Γ e TST) ...
   ---
   (well-tagged-expression Γ (make-vector τ e ...) κ)]
  [
   (or-TST List κ)
   (well-tagged-expression Γ e_0 TST)
   (well-tagged-expression Γ e_1 List)
   ---
   (well-tagged-expression Γ (cons e_0 e_1) κ)]
  [
   (or-TST List κ)
   ---
   (well-tagged-expression Γ nil κ)]
  [
   (where (_ τ) #{local-type-env-ref Γ x})
   (or-TST #{type->tag τ} κ)
   ---
   (well-tagged-expression Γ x κ)]
  [
   (well-tagged-expression Γ e_0 →)
   (well-tagged-expression Γ e_1 TST)
   ---
   (well-tagged-expression Γ (e_0 e_1) TST)]
  [
   (well-tagged-expression Γ e_0 Int)
   (well-tagged-expression Γ e_1 κ)
   (well-tagged-expression Γ e_2 κ)
   ---
   (well-tagged-expression Γ (ifz e_0 e_1 e_2) κ)]
  [
   (well-tagged-expression Γ e_0 Nat)
   (well-tagged-expression Γ e_1 Nat)
   ---
   (well-tagged-expression Γ (+ e_0 e_1) Nat)]
  [
   (or-TST Int κ)
   (well-tagged-expression Γ e_0 Int)
   (well-tagged-expression Γ e_1 Int)
   ---
   (well-tagged-expression Γ (+ e_0 e_1) κ)]
  [
   (or-TST Int κ)
   (well-tagged-expression Γ e_0 Int)
   (well-tagged-expression Γ e_1 Int)
   ---
   (well-tagged-expression Γ (- e_0 e_1) κ)]
  [
   (well-tagged-expression Γ e_0 Nat)
   (well-tagged-expression Γ e_1 Nat)
   ---
   (well-tagged-expression Γ (* e_0 e_1) Nat)]
  [
   (or-TST Int κ)
   (well-tagged-expression Γ e_0 Int)
   (well-tagged-expression Γ e_1 Int)
   ---
   (well-tagged-expression Γ (* e_0 e_1) κ)]
  [
   (well-tagged-expression Γ e_0 Nat)
   (well-tagged-expression Γ e_1 Nat)
   ---
   (well-tagged-expression Γ (% e_0 e_1) Nat)]
  [
   (or-TST Int κ)
   (well-tagged-expression Γ e_0 Int)
   (well-tagged-expression Γ e_1 Int)
   ---
   (well-tagged-expression Γ (% e_0 e_1) κ)]
  [
   (or-TST Vector κ)
   (well-tagged-expression Γ e_0 Vector)
   (well-tagged-expression Γ e_1 Int)
   ---
   (well-tagged-expression Γ (vector-ref e_0 e_1) κ)]
  [
   (well-tagged-expression Γ e_0 Vector)
   (well-tagged-expression Γ e_1 Int)
   (well-tagged-expression Γ e_2 κ)
   ---
   (well-tagged-expression Γ (vector-set! e_0 e_1 e_2) κ)]
  [
   (well-tagged-expression Γ e List)
   ---
   (well-tagged-expression Γ (first e) TST)]
  [
   (or-TST List κ)
   (well-tagged-expression Γ e List)
   ---
   (well-tagged-expression Γ (rest e) κ)]
  [
   (well-tagged-expression Γ e TST)
   ---
   (well-tagged-expression Γ (from-untyped κ e) κ)]
  [
   (well-tagged-expression Γ e κ)
   ---
   (well-tagged-expression Γ e (U κ_0 ... κ κ_1 ...))])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "tagged-completion"
    (check-mf-apply* #:is-equal? α=?
     ((tagged-completion# () 3 TST)
      3)
     ((tagged-completion# () 3 Nat)
      3)
     ((tagged-completion# () 3 Int)
      3)
     ((tagged-completion# () -7 TST)
      -7)
     ((tagged-completion# () (fun f (→ Int Int) (x) (+ x 1)) →)
      (fun f (→ TST Int) (x) ((fun f (→ Int Int) (x) (+ x 1)) (from-untyped Int x))))
     ((tagged-completion# () (fun f (→ Int Int) (x) (+ x 1)) TST)
      (fun f (→ TST Int) (x) ((fun f (→ Int Int) (x) (+ x 1)) (from-untyped Int x))))
     ((tagged-completion# () (make-vector (Vectorof Int) 1 -2) Vector)
      (make-vector (Vectorof Int) 1 -2))
     ((tagged-completion# () (make-vector (Vectorof Int) 1 -2) TST)
      (make-vector (Vectorof Int) 1 -2))
     ((tagged-completion# () (cons 1 (cons -2 nil)) List)
      (cons 1 (cons -2 nil)))
     ((tagged-completion# () nil List)
      nil)
     ((tagged-completion# () nil TST)
      nil)
     ((tagged-completion# ((x Int)) x Int)
      x)
     ((tagged-completion# ((x Int)) x TST)
      x)
     ((tagged-completion# ((x TST)) x TST)
      x)
     ((tagged-completion# ((x (Listof TST))) x List)
      x)
     ((tagged-completion# ((f (→ Int Int))) (f 3) Int)
      (from-untyped Int (from-typed TST (f 3))))
     ((tagged-completion# ((f (→ Int (Vectorof Int)))) (f 3) Vector)
      (from-untyped Vector (from-typed TST (f 3))))
     ((tagged-completion# () ((fun f (→ Nat Nat) (x) (+ x 1)) 0) Nat)
      (from-untyped Nat (from-typed TST ((fun f (→ TST Nat) (x) ((fun f (→ Nat Nat) (x) (+ x 1)) (from-untyped Nat x))) 0))))
     ((tagged-completion# () (ifz 0 1 2) Nat)
      (ifz 0 1 2))
     ((tagged-completion# ((xs (Listof Nat))) (ifz (first xs) 1 nil) (U Int List))
      (ifz (from-untyped Int (first xs)) 1 nil))
     ((tagged-completion# () (+ 2 2) Int)
      (+ 2 2))
     ((tagged-completion# () (+ 2 2) Nat)
      (+ 2 2))
     ((tagged-completion# () (- 2 2) Int)
      (- 2 2))
     ((tagged-completion# () (* 2 2) Nat)
      (* 2 2))
     ((tagged-completion# () (* 2 2) Int)
      (* 2 2))
     ((tagged-completion# () (* 2 2) TST)
      (* 2 2))
     ((tagged-completion# () (% 2 2) Nat)
      (% 2 2))
     ((tagged-completion# () (% 2 2) Int)
      (% 2 2))
     ((tagged-completion# ((xs (Listof Int))) (% 2 (first xs)) Int)
      (% 2 (from-untyped Int (first xs))))
     ((tagged-completion# () (vector-ref (make-vector (Vectorof Int) 1 2) 0) Nat)
      (from-untyped Nat (from-typed Nat (vector-ref (make-vector (Vectorof Int) 1 2) 0))))
     ((tagged-completion# () (vector-set! (make-vector (Vectorof Int) 1 2) 0 1) Nat)
      (vector-set! (make-vector (Vectorof Int) 1 2) 0 1))
     ((tagged-completion# () (first nil) Nat)
      (from-untyped Nat (first nil)))
     ((tagged-completion# () (rest nil) List)
      (rest nil))
    )

    (check-exn exn:fail:redex?
      ;; No completion for untyped code
      (λ () (term #{tagged-completion# () (fun f (x) x)})))

    (check-exn exn:fail:contract?
      (λ () (term #{tagged-completion# () (make-vector 1) Vector})))

    (check-exn exn:fail:contract?
      ;; Fails if bad tag
      (λ () (term #{tagged-completion# () (fun f (→ Int Int) (x) (+ x 1)) Int})))
  )

  (test-case "well-tagged-expression"
    (check-judgment-holds*
     (well-tagged-expression () 4 Nat)
     (well-tagged-expression () 4 TST)
     (well-tagged-expression () -4 Int)
     (well-tagged-expression () -4 TST)
     (well-tagged-expression () (make-vector (Vectorof Int) 1 2) Vector)
     (well-tagged-expression () nil TST)
     (well-tagged-expression () (cons 1 nil) List)
     (well-tagged-expression ((x (Vectorof Int))) x Vector)
     (well-tagged-expression () (fun f (→ Nat Nat) (x) (+ x 1)) →)
     (well-tagged-expression () (fun f (→ Nat Nat) (x) (+ x 1)) TST)
     (well-tagged-expression () ((fun f (→ Nat Nat) (x) (+ x 1)) 4) TST)
     (well-tagged-expression () (ifz 1 2 3) Nat)
     (well-tagged-expression () (+ 2 2) Nat)
     (well-tagged-expression () (+ 2 2) Int)
     (well-tagged-expression ((x Nat)) (+ x 1) Nat)
     (well-tagged-expression () (- 2 2) Int)
     (well-tagged-expression () (* 2 2) Nat)
     (well-tagged-expression () (* 2 2) Int)
     (well-tagged-expression () (% 2 2) Nat)
     (well-tagged-expression () (% 2 2) Int)
     (well-tagged-expression () (vector-ref (make-vector (Vectorof Int) 1) 0) TST)
     (well-tagged-expression () (vector-set! (make-vector (Vectorof Int) 1) 0 0) Nat)
     (well-tagged-expression () (first (cons 1 nil)) TST)
     (well-tagged-expression () (rest nil) List)
     (well-tagged-expression () (from-untyped Int (first (cons 1 nil))) Int)
     (well-tagged-expression ((x Int)) x (U Nat List Int))
    )

    (check-not-judgment-holds*
     (well-tagged-expression () (first (cons 1 nil)) Int)
     (well-tagged-expression () (rest (cons 1 nil)) Int)
    )

    (let* ([t0 (term (first xs))]
           [env (term ((xs (Listof Int))))]
           [t1 (term #{tagged-completion# ,env ,t0 Int})])
      (check-false (judgment-holds (well-tagged-expression ,env ,t0 Int)))
      (check-true (judgment-holds (well-tagged-expression ,env ,t1 Int))))
  )
)
