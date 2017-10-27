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
  do-ref
  do-set
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
  load-expression : σ ρ e -> Σ
  [(load-expression σ ρ e)
   (σ (substitute* e ρ))])

(define-metafunction μTR
  unload-answer : A -> [σ v]
  [(unload-answer Error)
   ,(raise-arguments-error 'unload-answer "evaluation error" "message" (term Error))]
  [(unload-answer (σ v))
   (σ v)])

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
  make-answer : σ E any -> A
  [(make-answer σ E Error)
   Error]
  [(make-answer σ E e)
   (σ (in-hole E e))])

(define-metafunction μTR
  do-ifz/typed : σ E v e e -> A
  [(do-ifz/typed σ E v e_0 e_1)
   #{do-ifz σ E v e_0 e_1}])

(define-metafunction μTR
  do-ifz/untyped : σ E v e e -> A
  [(do-ifz/untyped σ E v e_0 e_1)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-ifz/untyped σ E v e_0 e_1)
   #{do-ifz σ E v e_0 e_1}])

(define-metafunction μTR
  do-ifz : σ E v e e -> A
  [(do-ifz σ E 0 e_0 e_1)
   (σ (in-hole E e_0))]
  [(do-ifz σ E integer e_0 e_1)
   (σ (in-hole E e_1))
   (side-condition (not (zero? (term integer))))])

(define-metafunction μTR
  do-arith/untyped : BINOP σ E v v -> A
  [(do-arith/untyped _ _ _ v _)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped _ _ _ _ v)
   (TE v "integer?")
   (side-condition (not (integer? (term v))))]
  [(do-arith/untyped BINOP σ E v_0 v_1)
   #{do-arith BINOP σ E v_0 v_1}])

(define-metafunction μTR
  do-arith/typed : BINOP σ E v v -> A
  [(do-arith/typed BINOP σ E v_0 v_1)
   #{do-arith BINOP σ E v_0 v_1}])

(define-metafunction μTR
  do-arith : BINOP σ E v v -> A
  [(do-arith + σ E integer_0 integer_1)
   (σ (in-hole E ,(+ (term integer_0) (term integer_1))))]
  [(do-arith - σ E integer_0 integer_1)
   (σ (in-hole E ,(- (term integer_0) (term integer_1))))]
  [(do-arith * σ E integer_0 integer_1)
   (σ (in-hole E ,(* (term integer_0) (term integer_1))))]
  [(do-arith % σ E integer_0 integer_1)
   DivisionByZero
   (side-condition (zero? (term integer_1)))]
  [(do-arith % σ E integer_0 integer_1)
   (σ (in-hole E ,(quotient (term integer_0) (term integer_1))))
   (side-condition (not (zero? (term integer_1))))])

(define-metafunction μTR
  do-first/untyped : σ E v -> A
  [(do-first/untyped _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-first/untyped σ E v)
   #{do-first σ E v}])

(define-metafunction μTR
  do-first/typed : σ E v -> A
  [(do-first/typed σ E v)
   #{do-first σ E v}])

(define-metafunction μTR
  do-first : σ E v -> A
  [(do-first _ _ nil)
   EmptyList]
  [(do-first σ E (cons v_0 _))
   (σ (in-hole E v_0))])

(define-metafunction μTR
  do-rest/untyped : σ E v -> A
  [(do-rest/untyped _ _ v)
   (TE v "pair?")
   (judgment-holds (not-list-value v))]
  [(do-rest/untyped σ E v)
   #{do-rest σ E v}])

(define-metafunction μTR
  do-rest/typed : σ E v -> A
  [(do-rest/typed σ E v)
   #{do-rest σ E v}])

(define-metafunction μTR
  do-rest : σ E v -> A
  [(do-rest _ _ nil)
   EmptyList]
  [(do-rest σ E (cons _ v_1))
   (σ (in-hole E v_1))])

(define-metafunction μTR
  do-ref : σ E v v -> A
  [(do-ref σ E (vector loc) integer_index)
   #{make-answer σ E #{term-ref v* integer_index}}
   (where (_ v*) #{store-ref σ loc})]
  [(do-ref σ E (vector _ loc) integer_index)
   #{make-answer σ E #{term-ref v* integer_index}}
   (where (_ v*) #{store-ref σ loc})])

(define-metafunction μTR
  do-set : σ E v v v -> A
  [(do-set σ E (vector loc) v_1 v_2)
   ,(if (redex-match? μTR Error (term any_set))
      (term any_set)
      (term (#{store-update σ loc any_set} (in-hole E v_2))))
   (where (_ v*) #{store-ref σ loc})
   (where any_set #{term-set v* v_1 v_2})]
  [(do-set σ E (vector _ loc) v_1 v_2)
   ,(if (redex-match? μTR Error (term any_set))
      (term any_set)
      (term (#{store-update σ loc any_set} (in-hole E v_2))))
   (where (_ v*) #{store-ref σ loc})
   (where any_set #{term-set v* v_1 v_2})])

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
     ((load-expression () () (+ 2 2))
      (() (+ 2 2)))
     ((load-expression ((q (0))) () (+ 2 2))
      (((q (0))) (+ 2 2)))
     ((load-expression ((q (0))) ((a 4) (b (vector (Vectorof Integer) q))) (+ a b))
      (((q (0))) (+ 4 (vector (Vectorof Integer) q))))
     ((load-expression ((q (0))) ((a 4) (b (vector q))) (+ a b))
      (((q (0))) (+ 4 (vector q))))))

  (test-case "unload-answer"
    (check-mf-apply*
     ((unload-answer (() 3))
      (() 3)))

    (check-exn exn:fail:contract?
      (λ () (term (unload-answer BadIndex)))))

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
     ((make-answer () hole 2)
      (() 2))
     ((make-answer () hole (TE 2 "pair?"))
      (TE 2 "pair?"))
     ((make-answer ((qq (1))) hole (mon-vector (Vectorof Nat) (vector qq)))
      (((qq (1))) (mon-vector (Vectorof Nat) (vector qq))))
    ))

  (test-case "do-ifz/untyped"
    (check-mf-apply*
     ((do-ifz/untyped () hole 1 2 3)
      (() 3))
     ((do-ifz/untyped () hole 0 1 2)
      (() 1))))

  (test-case "do-arith/untyped"
    (check-mf-apply*
     ((do-arith/untyped + () hole nil 0)
      (TE nil "integer?"))
     ((do-arith/untyped + () hole 0 nil)
      (TE nil "integer?"))
     ((do-arith/untyped + () hole 3 2)
      (() 5))
    )
  )

  (test-case "do-arith/typed"
    (check-mf-apply*
     ((do-arith/typed * () hole 7 6)
      (() 42))))

  (test-case "do-arith"
    (check-mf-apply*
     ((do-arith + () hole 3 3)
      (() 6))
     ((do-arith - () hole 1 3)
      (() -2))
     ((do-arith * () hole 3 3)
      (() 9))
     ((do-arith % () hole 6 3)
      (() 2))
     ((do-arith % () hole 1 3)
      (() 0))
     ((do-arith % () hole 1 0)
      DivisionByZero)))

  (test-case "do-first/untyped"
    (check-mf-apply*
     ((do-first/untyped () hole 3)
      (TE 3 "pair?"))
     ((do-first/untyped () hole (cons 3 nil))
      (() 3))))

  (test-case "do-first/typed"
    (check-mf-apply*
     ((do-first/typed () hole (cons 3 nil))
      (() 3))))

  (test-case "do-first"
    (check-mf-apply*
     ((do-first () hole nil)
      EmptyList)
     ((do-first () hole (cons 2 nil))
      (() 2))
     ((do-first () hole (cons 2 (cons 3 nil)))
      (() 2))))

  (test-case "do-rest/untyped"
    (check-mf-apply*
     ((do-rest/untyped () hole 3)
      (TE 3 "pair?"))
     ((do-rest/untyped () hole (cons 3 nil))
      (() nil))))

  (test-case "do-rest/typed"
    (check-mf-apply*
     ((do-rest/typed () hole (cons 3 nil))
      (() nil))))

  (test-case "do-rest"
    (check-mf-apply*
     ((do-rest () hole nil)
      EmptyList)
     ((do-rest () hole (cons 2 nil))
      (() nil))
     ((do-rest () hole (cons 2 (cons 3 nil)))
      (() (cons 3 nil)))))

  (test-case "do-ref"
    (check-mf-apply*
     ((do-ref ((qq (2))) hole (vector qq) 0)
      (((qq (2))) 2))))

  (test-case "do-set"
    (check-mf-apply*
     ((do-set ((qq (5))) hole (vector qq) 0 1)
      (((qq (1))) 1))
     ((do-set ((qq (5))) hole (vector (Vectorof Int) qq) 0 1)
      (((qq (1))) 1))
    )
  )

)
