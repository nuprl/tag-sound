#lang mf-apply racket/base

(provide
  set-union*
  substitute*

  (rename-out
   [env-ref unsafe-env-ref]
   [env-set unsafe-env-set]
   [env-set* unsafe-env-set*])

  local-value-env-ref
  local-value-env-set
  local-value-env-update
  local-value-env-append

  toplevel-value-env-ref
  toplevel-value-env-set
  toplevel-value-env-update

  local-type-env-ref
  local-type-env-set
  local-type-env-update
  local-type-env-append

  toplevel-type-env-ref
  toplevel-type-env-set
  toplevel-type-env-update

  store-ref
  store-set
  store-update

  mu-fold
  coerce-sequence
  coerce-arrow-type
  coerce-vector-type
  coerce-list-type
  not-TST

  unload-store/expression

  same-domain

  type->tag
  tag-of

  lambda-strip-type

  typed-context
  untyped-context)

(require
  "lang.rkt"
  racket/set
  redex/reduction-semantics)

;; =============================================================================

(define (set-union* x**)
  (for/fold ([acc '()])
            ([x* (in-list x**)])
    (set-union acc x*)))

(define-metafunction μTR
  substitute* : any (any ...) -> any
  [(substitute* any_thing ())
   any_thing]
  [(substitute* any_thing (any_first any_rest ...))
   (substitute* (substitute any_thing any_key any_val) (any_rest ...))
   (where (any_key any_val _ ...) any_first)]
  [(substitute* any_thing (any_bad any_rest ...))
   ,(raise-arguments-error 'substitute* "bad environment binding"
      "term" (term any_thing)
      "binding" (term any_bad)
      "other bindings" (term (any_rest ...)))])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  env-set : any any -> any
  [(env-set any_env any_val)
   ,(cons (term any_val) (term any_env))])

(define-metafunction μTR
  env-set* : any (any ...) -> any
  [(env-set* any ())
   any]
  [(env-set* any (any_first any_rest ...))
   #{env-set* #{env-set any any_first} (any_rest ...)}])

(define-metafunction μTR
  env-ref : any x any -> any
  [(env-ref any_env x any_fail)
   ,(let loop ([env (term any_env)])
      (cond
       [(null? env)
        (let ((k (term any_fail)))
          (if (procedure? k) (k (term x)) k))]
       [(equal? (car (car env)) (term x))
        (car env)]
       [else
        (loop (cdr env))]))])

(define-metafunction μTR
  env-update : any any any -> any
  [(env-update any_env any_binding any_fail)
   ,(let loop ([env (term any_env)] [acc '()])
      (cond
       [(null? env)
        (let ((k (term any_fail)))
          (if (procedure? k) (k (car (term any_binding))) k))]
       [(equal? (caar env) (car (term any_binding)))
        (term #{env-set* #{env-set ,(cdr env) any_binding} ,acc})]
       [else
        (loop (cdr env) (term #{env-set ,acc ,(car env)}))]))])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  local-value-env-ref : ρ x -> any
  [(local-value-env-ref ρ x)
   #{env-ref ρ x any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'local-value-env-ref "unbound identifier"
          "id" x "type context" (term ρ))))])

(define-metafunction μTR
  local-value-env-set : ρ x v -> ρ
  [(local-value-env-set ρ x v)
   #{env-set ρ (x v)}
   (where #false #{env-ref ρ x #false})]
  [(local-value-env-set ρ x v)
   ,(raise-arguments-error 'local-value-env-set "identifier already bound"
      "id" (term x) "local-value-env" (term ρ) "value" (term v))])

(define-metafunction μTR
  local-value-env-update : ρ x v -> ρ
  [(local-value-env-update ρ x v)
   #{env-update ρ (x v) any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'local-value-env-update "unbound identifier, cannot update"
          "id" x "loval-value-env" (term ρ))))])

(define-metafunction μTR
  local-value-env-append : ρ ρ -> ρ
  [(local-value-env-append ρ_0 ρ_1)
   ,(append (term ρ_0) (term ρ_1))])

(define-metafunction μTR
  toplevel-value-env-ref : VAL-ENV M -> any
  [(toplevel-value-env-ref VAL-ENV M)
   #{env-ref VAL-ENV M any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'toplevel-value-env-ref "unbound identifier"
          "id" x "toplevel-value-env" (term VAL-ENV))))])

(define-metafunction μTR
  toplevel-value-env-set : VAL-ENV M ρ -> VAL-ENV
  [(toplevel-value-env-set VAL-ENV M ρ)
   #{env-set VAL-ENV (M ρ)}
   (where #false #{env-ref VAL-ENV M #false})]
  [(toplevel-value-env-set VAL-ENV M ρ)
   ,(raise-arguments-error 'toplevel-value-env-set "identifier already bound"
      "id" (term M) "toplevel-value-env" (term VAL-ENV) "value" (term ρ))])

(define-metafunction μTR
  toplevel-value-env-update : VAL-ENV M ρ -> VAL-ENV
  [(toplevel-value-env-update VAL-ENV M ρ)
   #{env-update VAL-ENV (M ρ) any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'toplevel-value-env-update "unbound identifier, cannot update"
          "id" x "toplevel-value-env" (term VAL-ENV))))])

(define-metafunction μTR
  local-type-env-ref : Γ x -> any
  [(local-type-env-ref Γ x)
   #{env-ref Γ x any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'local-type-env-ref "unbound identifier"
          "id" x "local-type-env" (term Γ))))])

(define-metafunction μTR
  local-type-env-set : Γ x τ -> Γ
  [(local-type-env-set Γ x τ)
   #{env-set Γ (x τ)}
   (where #false #{env-ref Γ x #false})]
  [(local-type-env-set Γ x τ)
   ,(raise-arguments-error 'local-type-env-set "identifier already bound"
      "id" (term x) "local-type-env" (term Γ) "type" (term τ))])

(define-metafunction μTR
  local-type-env-update : Γ x τ -> Γ
  [(local-type-env-update Γ x τ)
   #{env-update Γ (x τ) any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'type-env-update "unbound identifier, cannot update"
          "id" x "local-type-env" (term Γ))))])

(define-metafunction μTR
  local-type-env-append : Γ Γ -> Γ
  [(local-type-env-append Γ_0 Γ_1)
   ,(append (term Γ_0) (term Γ_1))])

(define-metafunction μTR
  toplevel-type-env-ref : TYPE-ENV x -> any
  [(toplevel-type-env-ref TYPE-ENV x)
   #{env-ref TYPE-ENV x any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'toplevel-type-env-ref "unbound identifier"
          "id" x "toplevel-type-env" (term TYPE-ENV))))])

(define-metafunction μTR
  toplevel-type-env-set : TYPE-ENV M Γ -> TYPE-ENV
  [(toplevel-type-env-set TYPE-ENV M Γ)
   #{env-set TYPE-ENV (M Γ)}
   (where #false #{env-ref TYPE-ENV M #false})]
  [(toplevel-type-env-set TYPE-ENV M Γ)
   ,(raise-arguments-error 'topleveltype-env-set "identifier already bound"
      "id" (term M) "toplevel-type-env" (term TYPE-ENV) "value" (term Γ))])

(define-metafunction μTR
  toplevel-type-env-update : TYPE-ENV M Γ -> TYPE-ENV
  [(toplevel-type-env-update TYPE-ENV M Γ)
   #{env-update TYPE-ENV (M Γ) any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'toplevel-type-env-update "unbound identifier, cannot update"
          "id" x "toplevel-type-env" (term Γ))))])

(define-metafunction μTR
  store-ref : σ x -> any
  [(store-ref σ x)
   #{env-ref σ x any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'store-ref "unbound identifier"
          "id" x "store" (term σ))))])

(define-metafunction μTR
  store-set : σ x v* -> σ
  [(store-set σ x v*)
   #{env-set σ (x v*)}
   (where #false #{env-ref σ x #false})]
  [(store-set σ x v*)
   ,(raise-arguments-error 'store-set "identifier already bound"
      "id" (term x) "toplevel-type-env" (term σ) "value" (term v*))])

(define-metafunction μTR
  store-update : σ x v* -> σ
  [(store-update σ x v*)
   #{env-update σ (x v*) any_fail}
   (where any_fail
     ,(λ (x)
        (raise-arguments-error 'store-update "unbound identifier, cannot update"
          "id" x "store" (term σ))))])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  unload-store/expression : e σ -> e
  [(unload-store/expression e ())
   e]
  [(unload-store/expression e σ)
   e_sub
   (judgment-holds (unload-store-of e σ e_sub))])

(define-judgment-form μTR
  #:mode (unload-store-of I I O)
  #:contract (unload-store-of e σ e)
  [
   ---
   (unload-store-of integer σ integer)]
  [
   (where (fun x_f (x) e) Λ)
   (unload-store-of e σ e_sub)
   (where Λ_sub (fun x_f (x) e_sub))
   ---
   (unload-store-of Λ σ Λ_sub)]
  [
   (where [_ (v ...)] #{store-ref σ x})
   (unload-store-of v σ v_sub) ...
   ---
   (unload-store-of (vector x) σ (vector v_sub ...))]
  [
   (where [_ (v ...)] #{store-ref σ x})
   (unload-store-of v σ v_sub) ...
   ---
   (unload-store-of (vector τ x) σ (vector τ v_sub ...))]
  [
   (unload-store-of e_0 σ e_sub0)
   (unload-store-of e σ e_sub) ...
   ---
   (unload-store-of (vector e_0 e ...) σ (vector e_sub0 e_sub ...))]
  [
   (unload-store-of e_0 σ e_sub0)
   (unload-store-of e σ e_sub) ...
   ---
   (unload-store-of (vector τ e_0 e ...) σ (vector τ e_sub0 e_sub ...))]
  [
   (unload-store-of e_0 σ e_0sub)
   (unload-store-of e_1 σ e_1sub)
   ---
   (unload-store-of (cons e_0 e_1) σ (cons e_0sub e_1sub))]
  [
   ---
   (unload-store-of nil σ nil)]
  [
   (unload-store-of v σ v_sub)
   ---
   (unload-store-of (mon-fun x τ v) σ (mon-fun x τ v_sub))]
  [
   (unload-store-of v σ v_sub)
   ---
   (unload-store-of (mon-vector x τ v) σ (mon-vector x τ v_sub))]
  [
   (unload-store-of e_fun σ e_fun-sub)
   (unload-store-of e_arg σ e_arg-sub)
   ---
   (unload-store-of (e_fun e_arg) σ (e_fun-sub e_arg-sub))]
  [
   (unload-store-of e_0 σ e_0+)
   (unload-store-of e_1 σ e_1+)
   (unload-store-of e_2 σ e_2+)
   ---
   (unload-store-of (ifz e_0 e_1 e_2) σ (ifz e_0+ e_1+ e_2+))]
  [
   (unload-store-of e_0 σ e_0+)
   (unload-store-of e_1 σ e_1+)
   ---
   (unload-store-of (+ e_0 e_1) σ (+ e_0+ e_1+))]
  [
   (unload-store-of e_0 σ e_0+)
   (unload-store-of e_1 σ e_1+)
   ---
   (unload-store-of (- e_0 e_1) σ (- e_0+ e_1+))]
  [
   (unload-store-of e_0 σ e_0+)
   (unload-store-of e_1 σ e_1+)
   ---
   (unload-store-of (* e_0 e_1) σ (* e_0+ e_1+))]
  [
   (unload-store-of e_0 σ e_0+)
   (unload-store-of e_1 σ e_1+)
   ---
   (unload-store-of (% e_0 e_1) σ (% e_0+ e_1+))]
  [
   (unload-store-of e_vec σ e_vec+)
   (unload-store-of e_i σ e_i+)
   ---
   (unload-store-of (vector-ref e_vec e_i) σ (vector-ref e_vec+ e_i+))]
  [
   (unload-store-of e_vec σ e_vec+)
   (unload-store-of e_i σ e_i+)
   (unload-store-of e_val σ e_val+)
   ---
   (unload-store-of (vector-set! e_vec e_i e_val) σ (vector-set! e_vec+ e_i+ e_val+))]
  [
   (unload-store-of e σ e_+)
   ---
   (unload-store-of (first e) σ (first e_+))]
  [
   (unload-store-of e σ e_+)
   ---
   (unload-store-of (rest e) σ (rest e_+))])

(define-judgment-form μTR
  #:mode (same-domain I I)
  #:contract (same-domain any any)
  [
   (where any_keys0 ,(map car (term any_0)))
   (where any_keys1 ,(map car (term any_1)))
   (side-condition ,(set=? (term any_keys0) (term any_keys1)))
   ---
   (same-domain any_0 any_1)])

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

(define-metafunction μTR
  lambda-strip-type : Λ -> Λ
  [(lambda-strip-type (fun x_f τ (x_arg) e_body))
   (fun x_f (x_arg) e_body)]
  [(lambda-strip-type (fun x_f (x_arg) e_body))
   (fun x_f (x_arg) e_body)])

;; It's just a fold
(define-metafunction μTR
  lang-of-hole : E L -> L
  [(lang-of-hole hole L)
   L]
  [(lang-of-hole (vector v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (vector τ v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (cons E e) L)
   (lang-of-hole E L)]
  [(lang-of-hole (cons v E) L)
   (lang-of-hole E L)]
  [(lang-of-hole (E e) L)
   (lang-of-hole E L)]
  [(lang-of-hole (v E) L)
   (lang-of-hole E L)]
  [(lang-of-hole (ifz E e e) L)
   (lang-of-hole E L)]
  [(lang-of-hole (+ v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (- v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (* v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (% v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (vector-ref v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (vector-set! v ... E e ...) L)
   (lang-of-hole E L)]
  [(lang-of-hole (first E) L)
   (lang-of-hole E L)]
  [(lang-of-hole (rest E) L)
   (lang-of-hole E L)]
  [(lang-of-hole (check τ E) L)
   (lang-of-hole E UN)
   (where L TY)]
  [(lang-of-hole (protect τ E) L)
   (lang-of-hole E TY)
   (where L UN)]
  [(lang-of-hole E L)
   ,(raise-arguments-error 'lang-of-hole "invalid context" "ctx" (term E) "lang" (term L))])

(define-judgment-form μTR
  #:mode (untyped-context I I)
  #:contract (untyped-context E L)
  [
   (where L_hole #{lang-of-hole E L})
   (where L_hole UN)
   ---
   (untyped-context E L)])

(define-judgment-form μTR
  #:mode (typed-context I I)
  #:contract (typed-context E L)
  [
   (where L_hole #{lang-of-hole E L})
   (where L_hole TY)
   ---
   (typed-context E L)])

(define-metafunction μTR
  mu-fold : (μ (α) τ) -> τ
  [(mu-fold τ)
   (substitute τ_body α τ)
   (where (μ (α) τ_body) τ)])

(define-metafunction μTR
  coerce-sequence : τ -> τ*
  [(coerce-sequence (U τ ...))
   (τ ...)]
  [(coerce-sequence τ)
   (τ)])

(define-metafunction μTR
  coerce-arrow-type : τ -> any
  [(coerce-arrow-type (→ τ_dom τ_cod))
   (→ τ_dom τ_cod)]
  [(coerce-arrow-type (∀ (α) τ))
   #{coerce-arrow-type τ}]
  [(coerce-arrow-type _)
   #f])

(define-metafunction μTR
  coerce-vector-type : τ -> any
  [(coerce-vector-type (Vectorof τ))
   (Vectorof τ)]
  [(coerce-vector-type _)
   #f])

(define-metafunction μTR
  coerce-list-type : τ -> any
  [(coerce-list-type (Listof τ))
   (Listof τ)]
  [(coerce-list-type _)
   #f])

(define-judgment-form μTR
  #:mode (not-TST I)
  #:contract (not-TST τ)
  [
   (side-condition ,(not (equal? (term TST) (term τ))))
   ---
   (not-TST τ)])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "set-union*"
    (check-equal?
      (set-union* '())
      '())
    (check set=?
      (set-union* '((1 2 3) (2 3 4) (3 4 5)))
      '(1 2 3 4 5)))

  (test-case "env-set"
    (check-mf-apply*
     [(env-set () 3)
      (3)]
     [(env-set (2 3) 1)
      (1 2 3)]))

  (test-case "env-ref"
    (check-mf-apply*
     [(env-ref ((a 1) (b 2) (c 3)) a #f)
      (a 1)]
     [(env-ref ((a 1) (b 2)) c #f)
      #f]
     [(env-ref ((a 1) (b 2)) c ,(λ (x) (format "not found ~a" x)))
      "not found c"])

    (check-exn exn:fail:contract?
      (λ () (term (env-ref () x ,(λ (x) (raise-arguments-error 'test "deathcase")))))))

  (test-case "env-update"
    (check-mf-apply*
     [(env-update ((x 2)) (x 3) #false)
      ((x 3))]
     [(env-update ((x 2) (y 3) (z 4)) (y 0) #false)
      ((x 2) (y 0) (z 4))]
     [(env-update ((x 2)) (y 0) #false)
      #false]
     [(env-update ((x 2)) (y 0) ,(λ (z) (format "unbound ~a" z)))
      "unbound y"]))

  (test-case "local-value-env"
    (check-mf-apply*
     [(local-value-env-ref ((x 4)) x)
      (x 4)]
     [(local-value-env-ref ((x 3) (y 1)) y)
      (y 1)])
    (check-exn exn:fail:contract?
      (λ () (term #{local-value-env-ref () x})))
    (check-mf-apply*
     [(local-value-env-set () x 3)
      ((x 3))]
     [(local-value-env-set ((x 1) (y -4)) z 66)
      ((z 66) (x 1) (y -4))])
    (check-exn exn:fail:contract?
      (λ () (term (local-value-env-set ((x 4)) x 5))))
    (check-mf-apply*
     [(local-value-env-update ((x 4)) x 5)
      ((x 5))])
    (check-exn exn:fail:contract?
      (λ () (term (local-value-env-update ((x 5)) y 1))))
    (check-mf-apply*
      ((local-value-env-append ((x 3)) ((y 4)))
       ((x 3) (y 4)))))

  (test-case "toplevel-value-env"
    (check-mf-apply*
     [(toplevel-value-env-ref ((M0 ())) M0)
      (M0 ())]
     [(toplevel-value-env-ref ((M0 ((x 3))) (M1 ((y 4)))) M1)
      (M1 ((y 4)))])
    (check-exn exn:fail:contract?
      (λ () (term #{toplevel-value-env-ref () x})))
    (check-mf-apply*
     [(toplevel-value-env-set () M0 ((x 4) (y 3)))
      ((M0 ((x 4) (y 3))))]
     [(toplevel-value-env-set ((M0 ((x 4)))) M1 ((y 5)))
      ((M1 ((y 5))) (M0 ((x 4))))])
    (check-exn exn:fail:contract?
      (λ () (term (toplevel-value-env-set ((M0 ())) M0 ()))))
    (check-mf-apply*
     [(toplevel-value-env-update ((M0 ((x 0)))) M0 ((x 1)))
      ((M0 ((x 1))))])
    (check-exn exn:fail:contract?
      (λ () (term (toplevel-value-env-update ((M0 ())) M1 ())))))

  (test-case "local-type-env"
    (check-mf-apply*
     [(local-type-env-ref ((x Int)) x)
      (x Int)]
     [(local-type-env-ref ((x Int) (y Int)) y)
      (y Int)])
    (check-exn exn:fail:contract?
      (λ () (term #{local-type-env-ref () x})))
    (check-mf-apply*
     [(local-type-env-set () x Int)
      ((x Int))]
     [(local-type-env-set ((x Int) (y Int)) z (Vectorof Int))
      ((z (Vectorof Int)) (x Int) (y Int))])
    (check-exn exn:fail:contract?
      (λ () (term (local-type-env-set ((x Int)) x Int))))
    (check-mf-apply*
     [(local-type-env-update ((x Int)) x Nat)
      ((x Nat))])
    (check-exn exn:fail:contract?
      (λ () (term (local-type-env-update ((x Int)) y Nat))))
    (check-mf-apply*
      ((local-type-env-append ((x Int)) ((y Int)))
       ((x Int) (y Int)))))

  (test-case "toplevel-type-env"
    (check-mf-apply*
     [(toplevel-type-env-ref ((M0 ((x Int)))) M0)
      (M0 ((x Int)))]
     [(toplevel-type-env-ref ((M0 ((x Int))) (M1 ((y Int)))) M1)
      (M1 ((y Int)))])
    (check-exn exn:fail:contract?
      (λ () (term #{toplevel-type-env-ref () M0})))
    (check-mf-apply*
     [(toplevel-type-env-set () M0 ((x Int)))
      ((M0 ((x Int))))]
     [(toplevel-type-env-set ((M0 ((x Int) (y Int)))) M1 ())
      ((M1 ()) (M0 ((x Int) (y Int))))])
    (check-exn exn:fail:contract?
      (λ () (term (toplevel-type-env-set ((M0 ())) M0 ()))))
    (check-mf-apply*
     [(toplevel-type-env-update ((M0 ())) M0 ((x Int)))
      ((M0 ((x Int))))])
    (check-exn exn:fail:contract?
      (λ () (term (toplevel-type-env-update ((M0 ((x Int)))) M1 ())))))

  (test-case "store"
    (check-mf-apply*
     [(store-ref ((x (1))) x)
      (x (1))]
     [(store-ref ((x (1)) (y (2))) y)
      (y (2))])
    (check-exn exn:fail:contract?
      (λ () (term #{store-ref () x})))
    (check-mf-apply*
     [(store-set () x (1 2))
      ((x (1 2)))]
     [(store-set ((x (1)) (y (2))) z (1 2 3))
      ((z (1 2 3)) (x (1)) (y (2)))])
    (check-exn exn:fail:contract?
      (λ () (term (store-set ((x (1))) x (2)))))
    (check-mf-apply*
     [(store-update ((x (2))) x (3))
      ((x (3)))])
    (check-exn exn:fail:contract?
      (λ () (term (store-update ((x (4))) y (4))))))

  (test-case "substitute*"
    (check-mf-apply*
     [(substitute* (+ x y) ((x 1) (y 2)))
      (+ 1 2)]
     [(substitute* (+ a a) ())
      (+ a a)]))

  (test-case "unload-store"
    (check-mf-apply*
     ((unload-store/expression (vector x) ((x (1 2 3))))
      (vector 1 2 3))
     ((unload-store/expression (vector Int x) ((x (1 2 3))))
      (vector Int 1 2 3))
     ((unload-store/expression (vector Int 42) ())
      (vector Int 42))
     ((unload-store/expression (+ 2 2) ())
      (+ 2 2))
     ((unload-store/expression (+ (vector a) (vector b)) ((a (1)) (b (4 3 2))))
      (+ (vector 1) (vector 4 3 2)))))

  (test-case "untyped-context"
    (check-judgment-holds*
     (untyped-context (+ 2 hole) UN)
     (untyped-context (check Int hole) TY)
    )
    (check-not-judgment-holds*
     (untyped-context (+ hole 2) TY)
    )
  )

  (test-case "typed-context"
    (check-judgment-holds*
     (typed-context (+ 2 hole) TY)
     (typed-context (protect Int hole) UN)
    )

    (check-not-judgment-holds*
     (typed-context (+ hole 2) UN)
    )

    (check-exn exn:fail:contract?
      (λ () (judgment-holds (typed-context (check Int hole) UN))))
    (check-exn exn:fail:contract?
      (λ () (judgment-holds (typed-context (protect Int hole) TY))))
  )

  (test-case "mu-fold"
    (check-mf-apply*
     ((mu-fold (μ (α) (→ Int α)))
      (→ Int (μ (α) (→ Int α))))
     ((mu-fold (μ (α) (U Int (Listof α))))
      (U Int (Listof (μ (α) (U Int (Listof α))))))
    )
  )

  (test-case "coerce-sequence"
    (check-mf-apply*
     ((coerce-sequence (U Int Nat))
      (Int Nat))
     ((coerce-sequence Int)
      (Int))))

  (test-case "coerce-arrow-type"
    (check-mf-apply*
     ((coerce-arrow-type (→ Nat Nat))
      (→ Nat Nat))
     ((coerce-arrow-type Nat)
      #f)))

  (test-case "coerce-vector-type"
    (check-mf-apply*
     ((coerce-vector-type (Vectorof Int))
      (Vectorof Int))
     ((coerce-vector-type Nat)
      #false)))

  (test-case "coerce-list-type"
    (check-mf-apply*
     ((coerce-list-type (Listof Int))
      (Listof Int))
     ((coerce-list-type Nat)
      #f)))

  (test-case "not-TST"
    (check-judgment-holds*
     (not-TST Nat))
    (check-not-judgment-holds*
     (not-TST TST)))

  (test-case "same-domain"
    (check-mf-apply*
     ((same-domain ((a) (b) (c)) ((a) (b) (c)))
      #true)
     ((same-domain ((a) (b) (c)) ((b) (a) (c)))
      #true)
     ((same-domain ((a) (b) (c)) ((c)))
      #false)
     ((same-domain ((a 1) (b 2)) ((a Int) (b Nat)))
      #true)))

)
