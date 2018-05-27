#lang typed/racket/base #:locally-defensive

;; Test that nested elimination forms get checked

(define (f)
  (car (car '((1)))))
