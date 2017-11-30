#lang at-exp racket/base

;; Definitions for writing 21st-century proofs.
;;    https://lamport.azurewebsites.net/pubs/proof.pdf

(provide
  tr-definition
  tr-ref
)

(require
  scribble/core
  scribble/base
  (only-in scribble/manual
    defidform
    deftech
    tech)
  (only-in scribble/decode
    make-splice)
  ;scribble/struct
)

;; =============================================================================

(define UID
  (mcons 0 0))

(define (UID+)
  (define old (mcdr UID))
  (set-mcdr! UID (+ old 1))
  (void))

(define (UID++)
  (define old (mcar UID))
  (set-mcar! UID (+ old 1))
  (set-mcdr! UID 0)
  (void))

(define (next-UID)
  (begin0
    (format "~a.~a" (mcar UID) (mcdr UID))
    (UID+)))

;; -----------------------------------------------------------------------------

(define-logger techreport)

;; -----------------------------------------------------------------------------

(define boxed-style
  (make-style 'boxed '()))

(define (exact str*)
  (make-element (make-style "relax" '(exact-chars)) str*))

(define smallskip
  @exact{\smallskip})

;; -----------------------------------------------------------------------------

(define (tr-definition name-elem
                       #:key [key-str #f]
                       . content*)
  (unless key-str
    (log-techreport-warning "missing key for definition ~a" name-elem))
  (define uid (next-UID))
  (nested
    (list
      @para{@linebreak[]
            @bold{Definition @|uid|} : @deftech[#:key (or key-str "") name-elem]
            @|smallskip|}
      (make-table
        boxed-style
        (list (list (nested content*))))
      @para[@linebreak[]])))

(define (tr-ref tag)
  (tech #:key tag tag))
