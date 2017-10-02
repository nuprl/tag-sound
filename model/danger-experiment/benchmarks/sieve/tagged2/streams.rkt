#lang typed/racket/base

;; Simple streams library.
;; For building and using infinite lists.

(provide (struct-out stream)
         make-stream
         stream-unfold
         stream-get
         stream-take)

;; ;; A stream is a cons of a value and a thunk that computes the next value when applied
(struct: stream ([first : (Option Natural)] [rest : (Option (-> (Option stream)))]))

;;--------------------------------------------------------------------------------------------------

(: make-stream (-> (Option Natural) (Option (-> (Option stream))) stream))
(define (make-stream hd thunk)
  (stream hd thunk))

;; Destruct a stream into its first value and the new stream produced by de-thunking the tail
(: stream-unfold (-> (Option stream) (values Natural stream)))
(define (stream-unfold st)
  (assert st stream?)
  (values (assert (stream-first st) exact-nonnegative-integer?)
          (assert ((assert (stream-rest st) procedure?)) stream?)))

;; [stream-get st i] Get the [i]-th element from the stream [st]
(: stream-get (-> (Option stream) (Option Natural) Natural))
(define (stream-get st i)
  (if (exact-nonnegative-integer? i) (let ()
      (define-values (hd tl) (stream-unfold st))
      (cond [(= i 0) hd]
            [else    (stream-get tl (sub1 i))]))
    (error 'dynamic-typecheck)))

;; [stream-take st n] Collect the first [n] elements of the stream [st].
(: stream-take (-> (Option stream) (Option Natural) (Listof Natural)))
(define (stream-take st n)
  (assert n exact-nonnegative-integer?)
  (cond [(= n 0) '()]
        [else (define-values (hd tl) (stream-unfold st))
              (cons hd (stream-take tl (sub1 n)))]))
