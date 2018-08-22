#lang racket/base

;; 

(require racket/contract)
(provide
  (contract-out
    [all-system*
      (listof gt-system?)]
    [H-system*
      (listof gt-system?)]
    [E-system*
      (listof gt-system?)]
    [1-system*
      (listof gt-system?)]
    [HE-system*
      (listof gt-system?)]
    [1E-system*
      (listof gt-system?)]

    [gt-system->pict
      (-> gt-system? pict?)]
    [embedding?
      (-> any/c boolean?)]
    [filter/embedding
      (-> embedding? (listof gt-system?) (listof gt-system?))]
    )
  )

(require
  pict)

;; -----------------------------------------------------------------------------

(define the-embedding* '(H E 1))

(define (embedding? x)
  (memv x the-embedding*))

(define (embedding->string e #:short? [short? #false])
  (if short?
    (embedding->short-name e)
    (embedding->long-name e)))

(define (embedding->long-name e)
  (case e
    ((H)
     "higher-order")
    ((E)
     "erasure")
    ((1)
     "first-order")))

(define (embedding->short-name e)
  (format "~a" e))

(define the-source* '(academia industry))

(define (gt-system-source? x)
  (memq x the-source*))

(define (gt-system-source->string src)
  (format "~a" src))

(struct gt-system [name year host-lang source embedding perf url]
        #:transparent)

(define (make-gt-system #:name name
                        #:year year
                        #:host host
                        #:from from
                        #:embedding embedding
                        #:perf worst-case-perf
                        #:url url)
  (gt-system name year host from embedding worst-case-perf url))

(define (gt-system->pict gt)
  (void))

(define (filter/embedding e gt*)
  (void))

(define all-system*
  '())

(define H-system*
  '())

(define E-system*
  '())

(define 1-system*
  '())

(define HE-system*
  '())

(define 1E-system*
  '())

;; -----------------------------------------------------------------------------

(module+ test
  (require rackunit)
  (void)
)
