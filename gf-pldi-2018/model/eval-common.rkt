#lang mf-apply racket/base

;; Common metafunctions for `eval-*` modules

(provide
  eval-untyped-provide
  eval-typed-provide

  assert-below

  term-ref
  term-set
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

)
