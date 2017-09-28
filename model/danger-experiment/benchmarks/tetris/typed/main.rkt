#lang typed/racket

(require
  "base-types.rkt"
  "aux.rkt"
  "bset.rkt"
  "world.rkt")

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


(define SMALL_TEST "../base/tetris-hist-small.rktd")
(define LARGE_TEST "../base/tetris-hist-large.rktd")

(: main (-> String Void))
(define (main filename)
  (define w0 (world0))
  (define raw (with-input-from-file filename read))
  (if (list? raw)
    (replay w0 (reverse raw))
    (error "bad input")))

;; (time (main SMALL_TEST)) ; 0ms
(time (main LARGE_TEST)) ; 417ms
