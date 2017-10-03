#lang typed/racket

(require
  "data-adaptor.rkt"
  "const.rkt"
  "data.rkt"
)

;; Is the snake colliding with any of the walls?
(: snake-wall-collide? : (-> (Option Snake) Boolean))
(define (snake-wall-collide? snk)
  (head-collide? (assert (car (assert (snake-segs (assert snk snake?)) pair?)) posn?)))

(: head-collide? : (Posn . -> . Boolean))
(define (head-collide? p)
  (assert p posn?)
  (or (<= (assert (posn-x p) real?) 0)
      (>= (assert (posn-x p) real?) BOARD-WIDTH)
      (<= (assert (posn-y p) real?) 0)
      (>= (assert (posn-y p) real?) BOARD-HEIGHT)))

(: snake-self-collide? : (-> (Option Snake) Boolean))
(define (snake-self-collide? snk)
  (if (snake? snk) (let ()
      (segs-self-collide? (assert (car (assert (snake-segs snk) pair?)) posn?)
                          (cdr (assert (snake-segs snk) pair?))))
    (error 'dynamic-typecheck)))

(: segs-self-collide? : (Posn (Listof (Option Posn)) . -> . Boolean))
(define (segs-self-collide? h segs)
  (cond [(empty? segs) #f]
        [else (or (posn=? (assert (car segs) posn?) h)
                  (segs-self-collide? h (cdr segs)))]))
(provide
 snake-wall-collide?
 snake-self-collide?)
