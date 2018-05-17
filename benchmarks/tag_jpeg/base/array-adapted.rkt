#lang racket/base

;; Untyped interface to the typed math library

;; Locally-defensive files MUST require this version of the math library, to
;;  ensure that TYPED RACKET is protected against locally-defensive values

(require (prefix-in m. (only-in "math/array.rkt"
    for/array
    array-shape
    build-array
    in-array)))

(define array-shape m.array-shape)
(define build-array m.build-array)
(define in-array m.in-array)

(provide (rename-out (m.for/array for/array)) array-shape build-array in-array)
