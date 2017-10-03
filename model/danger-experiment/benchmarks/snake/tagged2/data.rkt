#lang typed/racket

(struct: snake ([dir  : (Option Dir)]
                [segs : (Option (NEListof (Option Posn)))]))
(struct: world ([snake : (Option Snake)]
                [food  : (Option Posn)]))

(struct: posn ([x : (Option Real)]
               [y : (Option Real)]))

(define-type Posn  posn)
(define-type (NEListof A) (Pairof A (Listof A)))
(define-type Snake snake)
(define-type Dir (U "up" "down" "left" "right"))

(: posn=? (-> (Option posn) (Option posn) Boolean))
(define (posn=? p1 p2)
  (assert p1 posn?)
  (assert p2 posn?)
  (and (= (assert (posn-x p1) real?) (assert (posn-x p2) real?))
       (= (assert (posn-y p1) real?) (assert (posn-y p2) real?))))

(provide
 posn=?
 [struct-out posn]
 [struct-out snake]
 [struct-out world])
