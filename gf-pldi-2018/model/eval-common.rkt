#lang mf-apply racket/base

;; Common metafunctions for `eval-*` modules

(provide
  eval-untyped-provide
  eval-typed-provide

  assert-below

  term-ref
  term-set

  load-expression
  unload-answer
  unload-answer/store

  local-value-env->provided

  make-answer
  do-ifz/typed
  do-ifz/untyped
  do-arith/typed
  do-arith/untyped
  do-first/typed
  do-first/untyped
  do-rest/typed
  do-rest/untyped
)

(require
  "lang.rkt"
  "typecheck.rkt"
  "metafunctions.rkt"
  redex/reduction-semantics)

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  eval-untyped-provide : ρ UNTYPED-PROVIDE -> ρ
  [(eval-untyped-provide ρ UNTYPED-PROVIDE)
   #{eval-provide ρ UNTYPED-PROVIDE}])

(define-metafunction μTR
  eval-typed-provide : ρ TYPED-PROVIDE -> ρ
  [(eval-typed-provide ρ TYPED-PROVIDE)
   #{eval-provide ρ TYPED-PROVIDE}])

;; eval-provide
;; Filter a runtime environment, remove all identifiers that are not in the
;;  given list of provides.
;; Error if an identifier is provided, but not defined in the runtime environment
(define-metafunction μTR
  eval-provide : ρ PROVIDE -> ρ
  [(eval-provide ρ (provide x_provide ...))
   (#{unsafe-env-ref ρ x_provide any_fail} ...)
   (where any_fail ,(λ (x)
                      (raise-arguments-error 'provide "provided identifier not defined in module"
                       "id" x)))])

(define-metafunction μTR
  assert-below : τ τ -> τ
  [(assert-below τ_0 τ_1)
   τ_0
   (judgment-holds (<: τ_0 τ_1))]
  [(assert-below τ_0 τ_1)
   ,(raise-arguments-error 'assert-below (format "supertype of ~a" (term τ_0))
      "given" (term τ_1))])

(define-metafunction μTR
  term-ref : v* any -> any
  [(term-ref () integer)
   BadIndex]
  [(term-ref (v_first v_rest ...) 0)
   v_first]
  [(term-ref (v_first v_rest ...) natural_k)
   (term-ref (v_rest ...) ,(- (term natural_k) 1))]
  [(term-ref v* _)
   BadIndex])

(define-metafunction μTR
  term-set : v* any any -> any
  [(term-set () natural any)
   BadIndex]
  [(term-set (v_first v_rest ...) 0 any_val)
   (any_val v_rest ...)]
  [(term-set (v_first v_rest ...) natural any_val)
   ,(if (term any_acc)
      (cons (term v_first) (term any_acc))
      (term BadIndex))
   (where any_acc #{term-set (v_rest ...) ,(- (term natural) 1) any_val})]
  [(term-set v* any_index any_val)
   BadIndex])

(define-metafunction μTR
  load-expression : L σ ρ e -> Σ
  [(load-expression L σ ρ e)
   (L σ (substitute* e ρ))])

(define-metafunction μTR
  unload-answer : A -> [σ v]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer Σ)
   (σ v)
   (where (L σ v) Σ)])

(define-metafunction μTR
  unload-answer/store : A -> e
  [(unload-answer/store A)
   e_sub
   (where (σ v) #{unload-answer A})
   (where e_sub #{unload-store/expression v σ})])

(define-metafunction μTR
  local-value-env->provided : ρ PROVIDE -> ρ
  [(local-value-env->provided ρ (provide))
   ()]
  [(local-value-env->provided ρ (provide x_0 x_rest ...))
   (x:v_0 x:v_rest ...)
   (where x:v_0 #{local-value-env-ref ρ x_0})
   (where (x:v_rest ...) #{local-value-env->provided ρ (provide x_rest ...)})])

;; -----------------------------------------------------------------------------

(define-metafunction μTR
  make-answer : L σ E any -> A
  [(make-answer L σ E Error)
   Error]
  [(make-answer L σ E e)
   (L σ (in-hole E e))])

(define-metafunction μTR
  do-ifz/typed : L σ E v e e -> A
  [(do-ifz/typed L σ E v e_0 e_1)
   #{do-ifz L σ E v e_0 e_1}])

(define-metafunction μTR
  do-ifz/untyped : L σ E v e e -> A
  [(do-ifz/untyped L σ E v e_0 e_1)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-ifz/untyped L σ E v e_0 e_1)
   #{do-ifz L σ E v e_0 e_1}])

(define-metafunction μTR
  do-ifz : L σ E v e e -> A
  [(do-ifz L σ E 0 e_0 e_1)
   (L σ (in-hole E e_0))]
  [(do-ifz L σ E integer e_0 e_1)
   (L σ (in-hole E e_1))
   (side-condition (not (zero? (term integer))))])

(define-metafunction μTR
  do-arith/untyped : BINOP L σ E v v -> A
  [(do-arith/untyped _ _ _ _ v _)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped _ _ _ _ _ v)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped BINOP L σ E v_0 v_1)
   #{do-arith BINOP L σ E v_0 v_1}])

(define-metafunction μTR
  do-arith/typed : BINOP L σ E v v -> A
  [(do-arith/typed BINOP L σ E v_0 v_1)
   #{do-arith BINOP L σ E v_0 v_1}])

(define-metafunction μTR
  do-arith : BINOP L σ E v v -> A
  [(do-arith + L σ E integer_0 integer_1)
   (L σ (in-hole E ,(+ (term integer_0) (term integer_1))))]
  [(do-arith - L σ E integer_0 integer_1)
   (L σ (in-hole E ,(- (term integer_0) (term integer_1))))]
  [(do-arith * L σ E integer_0 integer_1)
   (L σ (in-hole E ,(* (term integer_0) (term integer_1))))]
  [(do-arith % L σ E integer_0 integer_1)
   DivisionByZero
   (side-condition (zero? (term integer_1)))]
  [(do-arith % L σ E integer_0 integer_1)
   (L σ (in-hole E ,(quotient (term integer_0) (term integer_1))))
   (side-condition (not (zero? (term integer_1))))])

(define-metafunction μTR
  do-first/untyped : L σ E v -> A
  [(do-first/untyped _ _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-first/untyped L σ E v)
   #{do-first L σ E v}])

(define-metafunction μTR
  do-first/typed : L σ E v -> A
  [(do-first/typed L σ E v)
   #{do-first L σ E v}])

(define-metafunction μTR
  do-first : L σ E v -> A
  [(do-first _ _ _ nil)
   EmptyList]
  [(do-first L σ E (cons v_0 _))
   (L σ (in-hole E v_0))])

(define-metafunction μTR
  do-rest/untyped : L σ E v -> A
  [(do-rest/untyped _ _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-rest/untyped L σ E v)
   #{do-rest L σ E v}])

(define-metafunction μTR
  do-rest/typed : L σ E v -> A
  [(do-rest/typed L σ E v)
   #{do-rest L σ E v}])

(define-metafunction μTR
  do-rest : L σ E v -> A
  [(do-rest _ _ _ nil)
   EmptyList]
  [(do-rest L σ E (cons _ v_1))
   (L σ (in-hole E v_1))])

;; =============================================================================

(module+ test
  (require rackunit redex-abbrevs)

  (test-case "assert-below"
    (check-mf-apply*
     [(assert-below Int Int)
      Int]
     [(assert-below Nat Int)
      Nat])

    (check-exn exn:fail:contract?
      (λ () (term (assert-below Int Nat))))
  )

  (test-case "eval-untyped-provide"
    (check-mf-apply*
     ((eval-untyped-provide ((x 4) (y (vector zzz))) (provide x y))
      ((x 4) (y (vector zzz))))
     ((eval-untyped-provide ((x 4) (y (cons 1 nil))) (provide x))
      ((x 4))))
  )

  (test-case "eval-typed-provide"
    (check-mf-apply*
     ((eval-typed-provide ((x 4) (y (vector qq))) (provide x y))
      ((x 4) (y (vector qq))))
     ((eval-typed-provide ((x 4) (y (cons 1 nil))) (provide x))
      ((x 4))))
  )

  (test-case "eval-provide"
    (check-mf-apply*
      ((eval-provide () (provide))
       ())
      ((eval-provide ((x 4) (y 5)) (provide x y))
        ((x 4) (y 5)))
      ((eval-provide ((x 4) (y 5)) (provide y x))
       ((y 5) (x 4)))
      ((eval-provide ((x 4) (y 5)) (provide y))
       ((y 5)))
      ((eval-provide ((x 4) (y 5)) (provide x y))
       ((x 4) (y 5))))

    (check-exn exn:fail:contract?
      (λ () (term (eval-provide ((x 4)) (provide y))))))

  (test-case "term-ref"
    (check-mf-apply*
     ((term-ref (1) 0)
      1)
     ((term-ref (1 2 3) 0)
      1)
     ((term-ref (1 2 3) 2)
      3)
     ((term-ref (1 2 3) 4)
      BadIndex)
     ((term-ref () 0)
      BadIndex)
     ((term-ref (1) AAA)
      BadIndex)))

  (test-case "term-set"
    (check-mf-apply*
     ((term-set (1) 0 2)
      (2))
     ((term-set (1 2 3) 0 2)
      (2 2 3))
     ((term-set (1 2 3) 2 A)
      (1 2 A))
     ((term-set () 2 2)
      BadIndex)
     ((term-set () q 3)
      BadIndex)))

  (test-case "load-expression"
    (check-mf-apply*
     ((load-expression UN () () (+ 2 2))
      (UN () (+ 2 2)))
     ((load-expression TY ((q (0))) () (+ 2 2))
      (TY ((q (0))) (+ 2 2)))
     ((load-expression UN ((q (0))) ((a 4) (b (vector (Vectorof Integer) q))) (+ a b))
      (UN ((q (0))) (+ 4 (vector (Vectorof Integer) q))))))

  (test-case "unload-answer"
    (check-mf-apply*
     ((unload-answer (UN () 3))
      (() 3)))

    (check-exn exn:fail:contract?
      (λ () (term (unload-answer BadIndex)))))

  (test-case "unload-answer/store"
    (check-mf-apply*
     ((unload-answer/store (UN () 3))
      3)
     ((unload-answer/store (UN ((q (0))) 3))
      3)
     ((unload-answer/store (UN ((q (0))) (vector q)))
      (vector 0))))

  (test-case "local-value-env->provided"
    (check-mf-apply*
     ((local-value-env->provided () (provide))
      ())
     ((local-value-env->provided ((x 66)) (provide x))
      ((x 66)))
     ((local-value-env->provided ((x 1) (y -3)) (provide x y))
      ((x 1) (y -3)))
     ((local-value-env->provided ((x 2) (y -88)) (provide x))
      ((x 2)))
     ((local-value-env->provided ((x 6) (y 5)) (provide y))
      ((y 5))))
  )

  (test-case "make-answer"
    (check-mf-apply*
     ((make-answer UN () hole 2)
      (UN () 2))
     ((make-answer TY () hole (TE 2 "pair?"))
      (TE 2 "pair?"))))

  (test-case "do-ifz/untyped"
    (check-mf-apply*
     ((do-ifz/untyped UN () hole 1 2 3)
      (UN () 3))
     ((do-ifz/untyped UN () hole 0 1 2)
      (UN () 1))))

  (test-case "do-arith/untyped"
    (check-mf-apply*
     ((do-arith/untyped + UN () hole nil 0)
      (TE nil "integer?"))
     ((do-arith/untyped + UN () hole 0 nil)
      (TE nil "integer?"))
     ((do-arith/untyped + UN () hole 3 2)
      (UN () 5))
    )
  )

  (test-case "do-arith/typed"
    (check-mf-apply*
     ((do-arith/typed * TY () hole 7 6)
      (TY () 42))))

  (test-case "do-arith"
    (check-mf-apply*
     ((do-arith + UN () hole 3 3)
      (UN () 6))
     ((do-arith - UN () hole 1 3)
      (UN () -2))
     ((do-arith * UN () hole 3 3)
      (UN () 9))
     ((do-arith % UN () hole 6 3)
      (UN () 2))
     ((do-arith % UN () hole 1 3)
      (UN () 0))
     ((do-arith % UN () hole 1 0)
      DivisionByZero)))

  (test-case "do-first/untyped"
    (check-mf-apply*
     ((do-first/untyped UN () hole 3)
      (TE 3 "pair?"))
     ((do-first/untyped UN () hole (cons 3 nil))
      (UN () 3))))

  (test-case "do-first/typed"
    (check-mf-apply*
     ((do-first/typed TY () hole (cons 3 nil))
      (TY () 3))))

  (test-case "do-first"
    (check-mf-apply*
     ((do-first UN () hole nil)
      EmptyList)
     ((do-first UN () hole (cons 2 nil))
      (UN () 2))
     ((do-first UN () hole (cons 2 (cons 3 nil)))
      (UN () 2))))

  (test-case "do-rest/untyped"
    (check-mf-apply*
     ((do-rest/untyped UN () hole 3)
      (TE 3 "pair?"))
     ((do-rest/untyped UN () hole (cons 3 nil))
      (UN () nil))))

  (test-case "do-rest/typed"
    (check-mf-apply*
     ((do-rest/typed TY () hole (cons 3 nil))
      (TY () nil))))

  (test-case "do-rest"
    (check-mf-apply*
     ((do-rest UN () hole nil)
      EmptyList)
     ((do-rest UN () hole (cons 2 nil))
      (UN () nil))
     ((do-rest UN () hole (cons 2 (cons 3 nil)))
      (UN () (cons 3 nil)))))

)
