#lang at-exp racket/base

;; Definitions for writing 21st-century proofs.
;;    https://lamport.azurewebsites.net/pubs/proof.pdf

(provide
)

(require
  scribble/core
)

;; =============================================================================

(define THE-NUMBERER
  (mcons 0 0))

(define (num+)
  (define old (mcdr THE-NUMBERER))
  (set-mcdr! THE-NUMBERER (+ old 1))
  (void))

(define (num++)
  (define old (mcar THE-NUMBERER))
  (set-mcar! THE-NUMBERER (+ old 1))
  (set-mcdr! THE-NUMBERER 0)
  (void))

