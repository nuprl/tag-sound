#lang typed/racket

(require
  "base-types.rkt"
  "bset.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tetras

;; Move the Tetra by the given X & Y displacement.
(: tetra-move (-> (Option Real) (Option Real) (Option Tetra) Tetra))
(define (tetra-move dx dy t)
  (assert dx real?)
  (assert dy real?)
  (assert t tetra?)
  (tetra (posn (+ dx (posn-x (tetra-center t)))
               (+ dy (posn-y (tetra-center t))))
         (blocks-move dx dy (tetra-blocks t))))

;; Rotate the tetra 90 degrees counterclockwise around its center.
(: tetra-rotate-ccw (-> (Option Tetra) Tetra))
(define (tetra-rotate-ccw t)
  (assert t tetra?)
  (tetra (tetra-center t)
         (blocks-rotate-ccw (tetra-center t)
                            (tetra-blocks t))))

;; Rotate the tetra 90 degrees clockwise around its center.
(: tetra-rotate-cw (-> (Option Tetra) Tetra))
(define (tetra-rotate-cw t)
  (assert t tetra?)
  (tetra (tetra-center t)
         (blocks-rotate-cw (tetra-center t)
                           (tetra-blocks t))))

;; Is the tetra on any of the blocks?
(: tetra-overlaps-blocks? (-> (Option Tetra) (Option DangerBSet) Boolean))
(define (tetra-overlaps-blocks? t bs)
  (assert t tetra?)
  (not (empty? (blocks-intersect (tetra-blocks t) bs))))

;; Change the color of the given tetra.
(: tetra-change-color (-> (Option Tetra) (Option Color) Tetra))
(define (tetra-change-color t c)
  (assert t tetra?)
  (tetra (tetra-center t)
         (blocks-change-color (tetra-blocks t) c)))

(: build-tetra-blocks (-> (Option Color) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) (Option Real) Tetra))
(define (build-tetra-blocks color xc yc x1 y1 x2 y2 x3 y3 x4 y4)
  (assert color symbol?)
  (assert xc real?)
  (assert yc real?)
  (assert x1 real?)
  (assert y1 real?)
  (assert x2 real?)
  (assert y2 real?)
  (assert x3 real?)
  (assert y3 real?)
  (assert x4 real?)
  (assert y4 real?)
  (tetra-move 3 0
              (tetra (posn xc yc)
                     (list (block x1 y1 color)
                           (block x2 y2 color)
                           (block x3 y3 color)
                           (block x4 y4 color)))))

(provide
 tetra-move
 tetra-rotate-ccw
 tetra-rotate-cw
 tetra-overlaps-blocks?
 build-tetra-blocks
 tetra-change-color)

