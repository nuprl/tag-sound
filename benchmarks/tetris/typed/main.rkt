#lang typed/racket

(require "base-types.rkt")
(require require-typed-check)
(require/typed/check "aux.rkt"
  [list-pick-random (-> (Listof Tetra) Tetra)]
  [tetras (Listof Tetra)])
(require/typed/check "bset.rkt"
   [blocks-overflow? (-> BSet Boolean)])
(require/typed/check "world.rkt"
  [world-key-move (-> World String World)]
  [next-world (-> World World)])

(define (world0)
  (world (list-pick-random tetras) empty))

(: replay : World (Listof Any) -> Void)
(define (replay w0 hist)
  (for/fold ([w : World w0])
            ([e hist])
    (match e
      [`(on-key ,(? string? ke)) (world-key-move w ke)]
      [`(on-tick) (next-world w)]
      [`(stop-when)
       (λ ([w : World]) (blocks-overflow? (world-blocks w))) ;; Unused in original code https://github.com/philnguyen/soft-contract/blob/master/benchmark-contract-overhead/tetris.rkt#L959
       w]))
  (void))


(define DATA (with-input-from-file "../base/tetris-hist.rktd" read))
(define LOOPS 2)

(: main (-> Any Void))
(define (main raw)
  (define w0 (world0))
  (if (list? raw)
    (for ((_i (in-range LOOPS)))
      (replay w0 raw))
    (error "bad input")))

(time (main DATA))
