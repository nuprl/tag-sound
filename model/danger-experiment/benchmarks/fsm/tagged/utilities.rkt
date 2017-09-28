#lang typed/racket

;; Utility Functions

(define-type Probability Nonnegative-Real)
;; constraint [0,1]

(provide
 ;Probability
 ;; ---
 sum
 relative-average
 choose-randomly)

 (: sum (-> (Option [Listof (Option Real)]) Real))
 (: relative-average (-> (Option [Listof (Option Real)]) (Option Real) Real))
 (: choose-randomly
  (-> (Option [Listof (Option Probability)]) (Option Natural) [#:random (Option (U False Real))] [Listof Natural]))

;; =============================================================================

(define (sum l)
  (assert l list?)
  (for/fold ([acc : Real 0])
            ([x (in-list l)])
    (+ acc (assert x real?))))


(define (relative-average l w)
  (exact->inexact
   (/ (sum l)
      (assert w real?) (length (assert l list?)))))

;; -----------------------------------------------------------------------------

(define (choose-randomly probabilities speed #:random (q #false))
  (define %s (accumulated-%s probabilities))
  (for/list ([n (in-range (assert speed exact-nonnegative-integer?))])
    [define r (if q (assert q real?) (random))]
    ;; population is non-empty so there will be some i such that ...
    (let loop : Natural ([%s : [Listof Real] %s])
      (cond
        [(< r (first %s)) 0]
        [else (add1 (loop (rest %s)))]))
    #;
    (for/last ([p (in-naturals)] [% (in-list %s)] #:final (< r %)) p)))

(: accumulated-%s (-> (Option [Listof (Option Probability)]) [Listof Real]))
;; [Listof Probability] -> [Listof Probability]
;; calculate the accumulated probabilities 

(define (accumulated-%s probabilities)
  (define total (sum probabilities))
  (let relative->absolute : [Listof Real]
    ([payoffs : [Listof (Option Real)] (assert probabilities list?)][so-far : Real #i0.0])
    (cond
      [(empty? payoffs) '()]
      [else (define nxt (+ so-far (assert (first payoffs) real?)))
            ({inst cons Real Real}
             (/ nxt total) (relative->absolute (rest payoffs) nxt))])))
