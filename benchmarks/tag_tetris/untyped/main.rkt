#lang racket

(require "aux.rkt" "world.rkt" "bset.rkt" "data.rkt")

(define (world0)
  (world (list-pick-random tetras) empty))

(define (replay w0 hist)
  (for/fold ([w w0]) ([e hist])
    (match e
      [`(on-key ,ke) (world-key-move w ke)]
      [`(on-tick) (next-world w)]
      [`(stop-when)
       (λ (w) (blocks-overflow? (world-blocks w))) ;; Unused in original code https://github.com/philnguyen/soft-contract/blob/master/benchmark-contract-overhead/tetris.rkt#L959
       w]))
  (void))

(define DATA (with-input-from-file "../base/tetris-hist.rktd" read))
(define LOOPS 2)

(define (main raw)
  (define w0 (world0))
  (if (list? raw)
    (for ((_i (in-range LOOPS)))
      (replay w0 raw))
    (error "bad input")))

(time (main DATA))
