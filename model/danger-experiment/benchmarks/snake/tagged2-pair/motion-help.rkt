#lang typed/racket ;; 35 34 24 23

(require
  "data-adaptor.rkt"
  "cut-tail.rkt")

;; next-head : Posn Direction -> Posn
;; Compute next position for head.
(: next-head : (Posn Dir . -> . Posn))
(define (next-head seg dir)
  (cond [(equal? "right" dir) (posn (add1 (assert (posn-x seg) real?)) (assert (posn-y seg) real?))]
        [(equal? "left" dir)  (posn (sub1 (assert (posn-x seg) real?)) (assert (posn-y seg) real?))]
        [(equal? "down" dir)  (posn (assert (posn-x seg) real?) (sub1 (assert (posn-y seg) real?)))]
        [else                 (posn (assert (posn-x seg) real?) (add1 (assert (posn-y seg) real?)))]))

;; snake-slither : Snake -> Snake
;; move the snake one step
(: snake-slither : ((Option Snake) . -> . Snake))
(define (snake-slither snk)
  (assert snk snake?)
  (let ([d (assert (snake-dir snk) string?)])
    (snake d
           (cons (next-head (assert (car (assert (snake-segs snk) pair?)) posn?)
                            d)
                 (cut-tail (snake-segs snk))))))

;; snake-grow : Snake -> Snake
;; Grow the snake one segment.
(: snake-grow : ((Option Snake) . -> . Snake))
(define (snake-grow snk)
  (assert snk snake?)
  (let ([d (assert (snake-dir snk) string?)])
    (snake d
           (cons (next-head (assert (car (assert (snake-segs snk) pair?)) posn?)
                            d)
                 (assert (snake-segs snk) pair?)))))

(provide
 snake-slither
 snake-grow)
