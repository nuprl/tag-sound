#lang typed/racket #:locally-defensive

;; Unsupported: type-constructor checks for class, interface, and object types

(define-type C% (Class (f (-> Integer Integer))))

(define c% : C%
  (class object%
    (super-new)
    (define/public (f x) (+ x 1))))

(: g (-> (Vector (Instance C%)) Integer))
(define (g vo)
  (define o (vector-ref vo 0))
  (send o f (send o f 2)))

(g (vector (new c%)))
