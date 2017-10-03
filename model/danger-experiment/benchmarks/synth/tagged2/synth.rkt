#lang typed/racket/base

(provide
  fs
  sawtooth-wave
  seconds->samples
  emit)

(require
         "typed-data.rkt"
         (only-in racket/unsafe/ops unsafe-fx+ unsafe-fx<)
         (only-in racket/math exact-floor)
  "array-utils.rkt"
  "array-struct.rkt"
)

;; --- from array-sequence.rkt

(require (for-syntax racket/base syntax/parse))
(define-sequence-syntax in-array
  (λ () #'in-array)
  (λ (stx)
    (syntax-case stx ()
      [[(x) (_ arr-expr)]
       (syntax/loc stx
         [(x)
          (:do-in
           ([(ds size dims js proc)
             (let: ([arr : Array  arr-expr])
               (cond [(array? arr)
                      (define ds (assert (array-shape arr) vector?))
                      (define dims (vector-length ds))
                      (define size (array-size arr))
                      (define proc (assert (unsafe-array-proc arr) procedure?))
                      (define: js : Indexes (make-vector dims 0))
                      (values ds size dims js proc)]
                     [else
                      (raise-argument-error 'in-array "Array" arr)]))])
           (void)
           ([j 0])
           (unsafe-fx< j (assert size integer?))
           ([(x)  (proc js)])
           #true
           #true
           [(begin (next-indexes! ds dims js)
                   (unsafe-fx+ j 1))])])]
      [[_ clause] (raise-syntax-error 'in-array "expected (in-array <Array>)" #'clause #'clause)])))

;; -- synth

;; TODO this slows down a bit, it seems, but improves memory use
(array-strictness #f)

(: fs Natural)
(define fs 44100)
(: bits-per-sample Natural)
(define bits-per-sample 16)

;; Wow this is too much work
(: freq->sample-period (-> Float Integer))
(define (freq->sample-period freq)
  (: res Exact-Rational)
  (define res (inexact->exact (round (/ fs freq))))
  (if (index? res) res (error "not index")))

(: seconds->samples (-> (Option Float) Integer))
(define (seconds->samples s)
  (: res Exact-Rational)
  (define res (inexact->exact (round (* (assert s real?) fs))))
  (if (index? res) res (error "not index")))

;; --- Oscillators

;; array functions receive a vector of indices
(define-syntax-rule (array-lambda (i) body ...)
  (lambda ([i* : (Option (Vectorof (Option Integer)))])
    (let: ([i : (Option Integer) (vector-ref (assert i* vector?) 0)]) body ...)))

(: make-sawtooth-wave (-> Float (-> (Option Float) (-> (Option Indexes) Float))))
(define ((make-sawtooth-wave coeff) freq)
  (: sample-period Integer)
  (define sample-period (freq->sample-period (assert freq real?)))
  (: sample-period/2 Integer)
  (define sample-period/2 (quotient sample-period 2))
  (array-lambda (x)
    ;; gradually goes from -1 to 1 over the whole cycle
    (: x* Float)
    (define x* (exact->inexact (modulo (assert x integer?) sample-period)))
    (* coeff (- (/ x* sample-period/2) 1.0))))

(: sawtooth-wave (-> (Option Float) (-> (Option Indexes) Float)))
(define sawtooth-wave         (make-sawtooth-wave 1.0))

;; --- Emit

;; assumes array of floats in [-1.0,1.0]
;; assumes gain in [0,1], which determines how loud the output is
(: signal->integer-sequence (-> Array [#:gain Float] (Vectorof Integer)))
(define (signal->integer-sequence signal #:gain [gain 1])
  (for/vector : (Vectorof Integer) #:length (assert (array-size signal) integer?)
              ([sample : (Option Float) (in-array signal)])
    (max 0 (min (sub1 (expt 2 bits-per-sample)) ; clamp
                (exact-floor
                 (* gain
                    (* (+ (assert sample real?) 1.0) ; center at 1, instead of 0
                       (expt 2 (sub1 bits-per-sample)))))))))

;; `emit` used to write a file.
;; For now, it just converts a signal to a sequence.
(: emit (-> (Option Array) (Vectorof Integer)))
(define (emit signal)
  (signal->integer-sequence (assert signal array?) #:gain 0.3))

