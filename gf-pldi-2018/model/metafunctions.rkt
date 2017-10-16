#lang mf-apply racket/base

(provide
  set-union*
  env-set
  env-set*
  program-env-ref
  runtime-env-ref
  loc-env-ref
  loc-env-set
  loc-env-update
  type-env-ref
  type-env-set
  type-env-update
  substitute*

  stack-push
  stack-outermost-type

  typed-module
  untyped-module

  unload-store
)

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

(define-metafunction μTR
  program-env-ref : P-ENV x -> MODULE-BINDING
  [(program-env-ref P-ENV x)
   #{env-ref P-ENV x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'program-env-ref "unbound identifier" "id" x "env" (term P-ENV))))])

(define-metafunction μTR
  runtime-env-ref : ρ x any ... -> any
  [(runtime-env-ref ρ x any_fail)
   #{env-ref ρ x any_fail}]
  [(runtime-env-ref ρ x)
   #{env-ref ρ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'runtime-env-ref "unbound identifier" "id" x "env" (term ρ))))])

(define-metafunction μTR
  loc-env-ref : σ x -> any
  [(loc-env-ref σ x)
   #{env-ref σ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'loc-env-ref "unbound identifier" "id" x "store" (term σ))))])

(define-metafunction μTR
  loc-env-set : σ x v* -> σ
  [(loc-env-set σ x v*)
   #{env-set σ (x v*)}
   (where #false #{env-ref σ x #false})]
  [(loc-env-set σ x v*)
   ,(raise-arguments-error 'loc-env-set "identifier already bound in store"
      "id" (term x) "store" (term σ) "the value" (term v*))])

(define-metafunction μTR
  loc-env-update : σ x v* -> σ
  [(loc-env-update σ x v*)
   #{env-update σ (x v*) any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'loc-env-update "unbound identifier, cannot update" "id" x "store" (term σ))))])

(define-metafunction μTR
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   #{env-ref Γ x any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'type-env-ref "unbound identifier" "id" x "type context" (term Γ))))])

(define-metafunction μTR
  type-env-set : Γ x ?τ -> Γ
  [(type-env-set Γ x ?τ)
   #{env-set Γ (x ?τ)}
   (where #false #{env-ref Γ x #false})]
  [(type-env-set Γ x ?τ)
   ,(raise-arguments-error 'type-env-set "identifier already bound in store"
      "id" (term x) "type context" (term Γ) "the type" (term ?τ))])

(define-metafunction μTR
  type-env-update : Γ x ?τ -> Γ
  [(type-env-update Γ x ?τ)
   #{env-update Γ (x ?τ) any_fail}
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'type-env-update "unbound identifier, cannot update" "id" x "type env" (term Γ))))])

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

(define-metafunction μTR
  unload-store : e σ -> e
  [(unload-store e ())
   e]
  [(unload-store e σ)
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
   (where [_ (v ...)] #{loc-env-ref σ x})
   (unload-store-of v σ v_sub) ...
   ---
   (unload-store-of (vector x) σ (vector v_sub ...))]
  [
   (unload-store-of e σ e_sub) ...
   ---
   (unload-store-of (vector e ...) σ (vector e_sub ...))]
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

(define-metafunction μTR
  stack-push : S FRAME -> S
  [(stack-push S FRAME)
   (FRAME S)])

(define-metafunction μTR
  stack-outermost-type : S τ -> τ
  [(stack-outermost-type () τ)
   τ]
  [(stack-outermost-type (FRAME S) _)
   (stack-outermost-type S τ_F)
   (where τ_F #{frame->type FRAME})])

(define-judgment-form μTR
  #:mode (typed-module I I)
  #:contract (typed-module x x*)
  [
   (where (x_left ... x x_right ...) x*)
   ---
   (typed-module x x*)])

(define-judgment-form μTR
  #:mode (untyped-module I I)
  #:contract (untyped-module x x*)
  [
   (side-condition ,(not (member (term x) (term x*))))
   ---
   (untyped-module x x*)])

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

  (test-case "program-env-ref"
    (check-mf-apply*
     [(program-env-ref ((yo ())) yo)
      (yo ())]
     ;; TODO
  ))

  (test-case "runtime-env-ref"
    (check-mf-apply*
     [(runtime-env-ref ((x 3) (y 4)) x)
      (x 3)]
     [(runtime-env-ref ((x 3) (y 4)) y)
      (y 4)])

    (check-exn exn:fail:contract?
      (λ () (term (runtime-env-ref ((x 3)) y)))))

  (test-case "loc-env-ref"
    (check-mf-apply*
     [(loc-env-ref ((x (3))) x)
      (x (3))]
     [(loc-env-ref ((x (3)) (y (4))) y)
      (y (4))])

    (check-exn exn:fail:contract?
      (λ () (term #{loc-env-ref () x}))))

  (test-case "loc-env-set"
    (check-mf-apply*
     [(loc-env-set () x (0))
      ((x (0)))]
     [(loc-env-set ((x (1)) (y (2))) z (3))
      ((z (3)) (x (1)) (y (2)))])

    (check-exn exn:fail:contract?
      (λ () (term (loc-env-set ((x (0))) x (1))))))

  (test-case "loc-env-update"
    (check-mf-apply*
     [(loc-env-update ((x (0))) x (1))
      ((x (1)))])

    (check-exn exn:fail:contract?
      (λ () (term (loc-env-update ((x (0))) y (1))))))

  (test-case "type-env-ref"
    (check-mf-apply*
     [(type-env-ref ((x Int)) x)
      (x Int)]
     [(type-env-ref ((x Int) (y Int)) y)
      (y Int)])

    (check-exn exn:fail:contract?
      (λ () (term #{type-env-ref () x}))))

  (test-case "type-env-set"
    (check-mf-apply*
     [(type-env-set () x Int)
      ((x Int))]
     [(type-env-set ((x Int) (y Int)) z (Vectorof Int))
      ((z (Vectorof Int)) (x Int) (y Int))])

    (check-exn exn:fail:contract?
      (λ () (term (type-env-set ((x Int)) x Int)))))

  (test-case "type-env-update"
    (check-mf-apply*
     [(type-env-update ((x Int)) x Nat)
      ((x Nat))])

    (check-exn exn:fail:contract?
      (λ () (term (type-env-update ((x Int)) y Nat)))))

  (test-case "substitute*"
    (check-mf-apply*
     [(substitute* (+ x y) ((x 1) (y 2)))
      (+ 1 2)]
     [(substitute* (+ a a) ())
      (+ a a)]))

  (test-case "stack-outermost-type"
    (check-mf-apply*
     ((stack-outermost-type () Int)
      Int)
     ((stack-outermost-type () Nat)
      Nat)
     ((stack-outermost-type ((A hole Int) ((B hole Nat) ())) (Vectorof Int))
      Nat)))

  (test-case "typed-module"
    (check-judgment-holds*
     (typed-module M0 (M0 M1 M2))
     (typed-module M2 (M0 M1 M2)))

    (check-judgment-holds*
     (untyped-module M ())
     (untyped-module M0 (M1 M2)))

    (check-not-judgment-holds*
     (typed-module M (M0 M1 M2))
     (typed-module M3 (M0 M1 M2)))

    (check-not-judgment-holds*
     (untyped-module M (M))
     (untyped-module M0 (M1 M0 M2)))
  )

  (test-case "asdfasdfsfafdsf"
    (check-true (redex-match? μTR e (term
      (vector x)
    )))
    (check-true (redex-match? μTR σ (term
      ((x (1 2 3)))))))

  (test-case "unload-store"
    (check-mf-apply*
     ((unload-store (vector x) ((x (1 2 3))))
      (vector 1 2 3))
     ((unload-store (+ 2 2) ())
      (+ 2 2))
     ((unload-store (+ (vector a) (vector b)) ((a (1)) (b (4 3 2))))
      (+ (vector 1) (vector 4 3 2)))))
)
