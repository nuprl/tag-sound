#lang racket/base

(provide
  make--->*
  stuck?
  safe-step*
)

(require
  redex/reduction-semantics)

;; -----------------------------------------------------------------------------

(define (stuck? r t)
  (null? (apply-reduction-relation r t)))

(define (safe-step* A ty done? check-invariant step)
  (let loop ([A A])
    (cond
     [(done? A)
      A]
     [else
      (check-invariant A ty)
      (define A* (apply-reduction-relation step A))
      (cond
       [(null? A*)
        A]
       [(null? (cdr A*))
        (loop (car A*))]
       [else
        (raise-arguments-error 'safe-step* "step is non-deterministic for expression"
          "e" A
          "answers" A*)])])))

(define (make--->* --->)
  (define error-name (string->symbol (format "~a*" (object-name --->))))
  (lambda (t)
    (define v* (apply-reduction-relation* ---> t))
    (cond
     [(null? v*)
      (raise-user-error error-name "no result for ~a" t)]
     [(null? (cdr v*))
      (car v*)]
     [else
      (raise-user-error error-name "multiple results ~a --->* ~a" t v*)])))

