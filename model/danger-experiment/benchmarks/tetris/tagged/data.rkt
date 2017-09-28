#lang typed/racket

(struct: posn ([x : Real]
               [y : Real]))
(struct: block ([x : Real]
                [y : Real]
                [color : Symbol]))
(struct: tetra ([center : posn]
                [blocks : (Listof block)]))
(struct: world ([tetra : tetra]
                [blocks : (Listof (Option block))]))

(: posn=? (-> (Option posn) (Option posn) Boolean))
(define (posn=? p1 p2)
  (assert p1 posn?)
  (assert p2 posn?)
  (and (= (posn-x p1) (posn-x p2))
       (= (posn-y p1) (posn-y p2))))

(provide
 (struct-out posn)
 (struct-out block)
 (struct-out tetra)
 (struct-out world)
 posn=?)
