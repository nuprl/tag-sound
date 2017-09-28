#lang typed/racket

(require "base-types.rkt")
(require "data.rkt")

;; Determines if two blocks are the same (ignoring color).
(: block=? (-> (Option Block) (Option Block) Boolean))
(define (block=? b1 b2)
  (assert b1 block?)
  (assert b2 block?)
  (and (= (block-x b1) (block-x b2))
       (= (block-y b1) (block-y b2))))

(: block-move (-> (Option Real) (Option Real) (Option Block) Block))
(define (block-move dx dy b)
  (assert b block?)
  (assert dx real?)
  (assert dy real?)
  (block (+ dx (block-x b))
         (+ dy (block-y b))
         (block-color b)))

;; Rotate the block 90 counterclockwise around the posn.
(: block-rotate-ccw (-> (Option Posn) (Option Block) Block))
(define (block-rotate-ccw c b)
  (assert c posn?)
  (assert b block?)
  (block (+ (posn-x c) (- (posn-y c) (block-y b)))
         (+ (posn-y c) (- (block-x b) (posn-x c)))
         (block-color b)))

;; Rotate the block 90 clockwise around the posn.
(: block-rotate-cw (-> (Option Posn) (Option Block) Block))
(define (block-rotate-cw c b)
  (assert c posn?)
  (assert b block?)
  (block-rotate-ccw c (block-rotate-ccw c (block-rotate-ccw c b))))

(provide
 block-rotate-ccw
 block-rotate-cw
 block=?
 block-move)
