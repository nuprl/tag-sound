#lang typed/racket/base

(provide
  Indexes
  In-Indexes
  Weighted-Signal
  Drum-Symbol
  Pattern
  (struct-out Array)
  (struct-out Settable-Array)
  (struct-out Mutable-Array))

(require "data.rkt")

(define-type Indexes (Vectorof (Option Integer)))
(define-type In-Indexes Indexes)

;; From mix: A Weighted-Signal is a (List (Option (Array (Option Float))) (Option Real))
(define-type Weighted-Signal (List (Option Array) (Option Real)))

;; drum patterns are simply lists with either O (bass drum), X (snare) or
;; #f (pause)
(define-type Drum-Symbol (U 'O 'X #f))
(define-type Pattern (Listof (Option Drum-Symbol)))
