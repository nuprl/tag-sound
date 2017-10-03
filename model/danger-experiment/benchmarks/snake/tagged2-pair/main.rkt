#lang typed/racket

(require
  "data-adaptor.rkt"
  "const.rkt"
  "motion.rkt"
  "handlers.rkt")

(: replay : World (Listof Any) -> Void)
(define (replay w0 hist)
  (reset!)
  (let loop ((w : World w0)
             (h : (Listof Any) hist))
    (if (empty? h)
        w
        (let ()
          (loop
           (match (car h)
             [`(on-key ,(? string? ke))
              (handle-key w ke)]
             [`(on-tick)
              (world->world w)]
             [`(stop-when)
              (game-over? w)
              w])
           (cdr h)))))
  (void))

(define SMALL_TEST "../base/snake-hist-small.rktd")
(define LARGE_TEST "../base/snake-hist-large.rktd")

(: main (-> String Void))
(define (main filename)
  (define w0 (WORLD))
  (define raw-hist (with-input-from-file filename read))
  (cond [(list? raw-hist)
         (define hist (reverse raw-hist))
         (for ([i (in-range 100)])
           (replay w0 hist))]
        [else
         (error "bad input")]))

;; (time (main SMALL_TEST)) ; 66ms
(time (main LARGE_TEST)) ; 340ms
