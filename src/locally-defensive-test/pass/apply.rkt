#lang typed/racket/base #:locally-defensive

;; Test that `(apply f ...)`  does not check its result when `f` is a
;;  trusted function

(void (apply string-append '("one" "two" "three")))
