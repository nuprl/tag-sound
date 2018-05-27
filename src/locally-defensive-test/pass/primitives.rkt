#lang typed/racket #:locally-defensive

;; Test trusted primitives

(rest '(1 2 3))
(apply + '(1 2 3))

(struct foo ())
(foo? 4)
