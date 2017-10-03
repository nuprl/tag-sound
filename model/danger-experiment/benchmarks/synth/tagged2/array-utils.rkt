#lang typed/racket/base

(require
  (only-in racket/performance-hint begin-encourage-inline)
  (for-syntax racket/base)
  (only-in racket/fixnum fx* fx+)
  "typed-data.rkt")

(provide
array-shape-size
check-array-shape
check-array-shape-size
make-thread-local-indexes
next-indexes!
unsafe-array-index->value-index
unsafe-vector-insert
unsafe-vector-remove
vector-copy-all
)

(begin-encourage-inline
  
  (: vector->supertype-vector (All (A B) ((Vectorof A) -> (Vectorof (U A B)))))
  (define (vector->supertype-vector js)
    (define dims (vector-length js))
    (cond [(= dims 0)  (vector)]
          [else  (define: new-js : (Vectorof (U A B)) (make-vector dims (vector-ref js 0)))
                 (let loop ([#{i : Integer} 1])
                   (cond [(i . < . dims)  (vector-set! new-js i (vector-ref js i))
                                          (loop (+ i 1))]
                         [else  new-js]))]))
  
  (: vector-copy-all (All (A) ((Option (Vectorof A)) -> (Vectorof A))))
  (define (vector-copy-all js)
    ((inst vector->supertype-vector A A) (assert js vector?)))
  
  (: array-shape-size ((Option Indexes) -> Integer))
  (define (array-shape-size ds)
    (if (vector? ds) (let ()
        (define dims (vector-length ds))
        (let loop ([#{i : Integer} 0] [#{n : Integer} 1])
          (cond [(i . < . dims)  (define d (assert (vector-ref ds i) integer?))
                                 (loop (+ i 1) (* n d))]
                [else  n])))
      (error 'dynamic-typecheck)))
  
  (: check-array-shape-size ((Option Symbol) (Option Indexes) -> Integer))
  (define (check-array-shape-size name ds)
    (define size (array-shape-size ds))
    (cond [(index? size)  size]
          [else  (error (assert name symbol?) "array size ~e (for shape ~e) is too large (is not an Index)" size ds)]))
  
  (: check-array-shape ((Option (Vectorof (Option Integer))) (Option (-> Nothing)) -> Indexes))
  (define (check-array-shape ds fail)
    (if (vector? ds) (let ()
        (define dims (vector-length ds))
        (define: new-ds : Indexes (make-vector dims 0))
        (let loop ([#{i : Integer} 0])
          (cond [(i . < . dims)
                 (define di (vector-ref ds i))
                 (cond [(index? di)  (vector-set! new-ds i di)
                                     (loop (+ i 1))]
                       [else  ((assert fail procedure?))])]
                [else  new-ds])))
      (error 'dynamic-typecheck)))
  
  (: unsafe-array-index->value-index ((Option Indexes) (Option Indexes) -> Integer))
  (define (unsafe-array-index->value-index ds js)
    (if (and (vector? js) (vector? ds)) (let ()
        (define dims (vector-length ds))
        (let loop ([#{i : Integer} 0] [#{j : Integer} 0])
          (cond [(i . < . dims)
                 (define di (assert (vector-ref ds i) integer?))
                 (define ji (assert (vector-ref js i) integer?))
                 (loop (+ i 1) (fx+ ji (fx* di j)))]
                [else  j])))
      (error 'dynamic-typecheck)))
  
  )  ; begin-encourage-inline

(: raise-array-index-error (Symbol Indexes In-Indexes -> Nothing))
(define (raise-array-index-error name ds js)
  (error name "expected indexes for shape ~e; given ~e"
         (vector->list ds) js))

(: array-index->value-index (Symbol Indexes In-Indexes -> Integer))
(define (array-index->value-index name ds js)
  (define (raise-index-error) (raise-array-index-error name ds js))
  (define dims (vector-length ds))
  (unless (= dims (vector-length js)) (raise-index-error))
  (let loop ([#{i : Integer} 0] [#{j : Integer}  0])
    (cond [(i . < . dims)
           (define di (assert (vector-ref ds i) integer?))
           (define ji (vector-ref js i))
           (cond [(and (exact-integer? ji) (0 . <= . ji) (ji . < . di))
                  (loop (+ i 1) (fx+ ji (fx* di j)))]
                 [else  (raise-index-error)])]
          [else  j])))

(: check-array-indexes (Symbol Indexes In-Indexes -> Indexes))
(define (check-array-indexes name ds js)
  (assert js vector?)
  (assert ds vector?)
  (define (raise-index-error) (raise-array-index-error name ds js))
  (define dims (vector-length ds))
  (unless (= dims (vector-length js)) (raise-index-error))
  (define: new-js : Indexes (make-vector dims 0))
  (let loop ([#{i : Integer} 0])
    (cond [(i . < . dims)
           (define di (assert (vector-ref ds i) integer?))
           (define ji (vector-ref js i))
           (cond [(and (exact-integer? ji) (0 . <= . ji) (ji . < . di))
                  (vector-set! new-js i ji)
                  (loop (+ i 1))]
                 [else  (raise-index-error)])]
          [else  new-js])))

(: unsafe-vector-remove (All (I) ((Option (Vectorof I)) (Option Integer) -> (Vectorof I))))
(define (unsafe-vector-remove vec k)
  (if (vector? vec) (let ()
      (define n (vector-length vec))
      (define n-1 (sub1 n))
      (cond
        [(not (index? n-1)) (error 'unsafe-vector-remove "internal error")]
        [else
         (if (integer? k) (let ()
             (define: new-vec : (Vectorof I) (make-vector n-1 (assert (vector-ref vec 0) integer?)))
             (let loop ([#{i : Integer} 0])
               (when (i . < . k)
                 (vector-set! new-vec i (vector-ref vec i))
                 (loop (+ i 1))))
             (let loop ([#{i : Integer} k])
               (cond [(i . < . n-1)
                      (vector-set! new-vec i (vector-ref vec (+ i 1)))
                      (loop (+ i 1))]
                     [else  new-vec])))
            (error 'dynamic-typecheck))]))
    (error 'dynamic-typecheck)))

(: unsafe-vector-insert (All (I) ((Option (Vectorof I)) (Option Integer) I -> (Vectorof I))))
(define (unsafe-vector-insert vec k v)
  (if (vector? vec) (let ()
      (define n (vector-length vec))
      (define: dst-vec : (Vectorof I) (make-vector (+ n 1) v))
      (assert k integer?)
      (let loop ([#{i : Integer} 0])
        (when (i . < . k)
          (vector-set! dst-vec i (vector-ref vec i))
          (loop (+ i 1))))
      (let loop ([#{i : Integer} k])
        (when (i . < . n)
          (let ([i+1  (+ i 1)])
            (vector-set! dst-vec i+1 (vector-ref vec i))
            (loop i+1))))
      dst-vec)
    (error 'dynamic-typecheck)))

(: make-thread-local-indexes ((Option Integer) -> (-> Indexes)))
(define (make-thread-local-indexes dims)
  (assert dims integer?)
  (let: ([val : (Thread-Cellof (U #f Indexes)) (make-thread-cell #f)])
    (λ () (or (thread-cell-ref val)
              (let: ([v : Indexes  (make-vector dims 0)])
                (thread-cell-set! val v)
                v)))))

(: next-indexes! ((Option Indexes) (Option Integer) (Option Indexes) -> Void))
;; Sets js to the next vector of indexes, in row-major order
(define (next-indexes! ds dims js)
  (assert js vector?)
  (assert dims integer?)
  (assert ds vector?)
  (let loop ([#{k : Integer}  dims])
    (unless (zero? k)
      (let ([k  (- k 1)])
        (define jk (assert (vector-ref js k) integer?))
        (define dk (vector-ref ds k))
        (let ([jk  (+ jk 1)])
          (cond [(jk . >= . (assert dk integer?))
                 (vector-set! js k 0)
                 (loop k)]
                [else
                 (vector-set! js k jk)]))))))
