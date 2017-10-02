#lang typed/racket/base

(require "typed-data.rkt")

;; Label implementation.  Labels are like strings, but also allow for
;; efficient shared slicing.
;;
;; TODO later: see if we can generalize labels to be more than just
;; text strings.  It might be useful to have them as arbitrary
;; elements, perhaps as vectors?

;; label-element? object -> true
;; Every value is considered to be a possible label-element.
(: label-element? (-> Any Boolean))
(define (label-element? obj) #t)

;; When comparing label elements, we use equal?.
(: label-element-equal? (-> Any Any Boolean))
(define label-element-equal? equal?)

(define natural? exact-nonnegative-integer?)

(provide
        (rename-out [ext:make-label make-label])
        label-element?
        label-element-equal?
        string->label
        string->label/with-sentinel
        vector->label
        vector->label/with-sentinel
        label->string
        label->string/removing-sentinel
        label->vector
        label-length
        label-ref
        sublabel
        sublabel!
        label-prefix?
        label-equal?
        label-empty?
        label-copy
        label-ref-at-end?
        label-source-id
        label-same-source?
        label-source-eq?)


;;make-label: label-element -> label
;;Constructs a new label from either a string or a vector of things.
(: ext:make-label (-> (Option (U String (Vectorof (Option (U Char Symbol))))) Label))
(define (ext:make-label label-element)
 (cond ((string? label-element) (string->label label-element))
       ((vector? label-element) (vector->label label-element))
       (else
        (error 'make-label "Don't know how to make label from ~S" label-element))))

(: make-sentinel (-> Symbol))
(define (make-sentinel)
 (gensym 'sentinel))

(: sentinel? (-> Any Boolean))
(define (sentinel? datum)
 (symbol? datum))

;; vector->label vector
;; Constructs a new label from the input vector.
(: vector->label (-> (Option (Vectorof (Option (U Char Symbol)))) label))
(define (vector->label vector)
  (assert vector vector?)
  (make-label (vector->immutable-vector vector)
              0 (vector-length vector)))


;; vector->label vector
;; Constructs a new label from the input vector, with a sentinel
;; symbol at the end.
(: vector->label/with-sentinel (-> (Option (Vectorof (Option Char))) label))
(define (vector->label/with-sentinel vector)
  (if (vector? vector)
    (let ()
      (: N Index)
      (define N (vector-length vector))
      (: V (Vectorof (Option (U Char Symbol))))
      (define V (make-vector (add1 N) (make-sentinel)))
      (let loop ((i 0))
        (if (< i N)
            (begin (vector-set! V i (vector-ref vector i))
                   (loop (add1 i)))
            (vector->label V))))
    (error 'dynamic-typecheck)))


;;string->label: string -> label
;;Constructs a new label from the input string.
(: string->label (-> (Option String) label))
(define (string->label str)
  (vector->label (list->vector (string->list (assert str string?)))))


;; string->label/with-sentinel: string -> label
;; Constructs a new label from the input string, attaching a unique
;; sentinel symbol at the end of the label.
;;
;; Note: this label can not be converted in whole back to a string:
;; the sentinel character interferes with string concatenation
(: string->label/with-sentinel (-> (Option String) label))
(define (string->label/with-sentinel str)
  (vector->label/with-sentinel (list->vector (string->list (assert str string?)))))

;; label-length: label -> number?
;; Returns the length of the label.
(: label-length (-> (Option label) Index))
(define (label-length label)
  (if (label? label)
    (let ()
      (define len (- (assert (label-j label) natural?) (assert (label-i label) natural?)))
      (unless (index? len) (error "label-length"))
      len)
    (error 'dynamic-typecheck)))


; label-ref: label number? -> char
; Returns the kth element in the label.
(: label-ref (-> (Option label) (Option Integer) (U Symbol Char)))
(define (label-ref label k)
  (assert label label?)
  (unless (index? k) (error "label ref INDEX"))
  (assert (vector-ref (assert (label-datum label) vector?) (+ k (assert (label-i label) natural?)))))

;; sublabel: label number number -> label
;; Gets a slice of the label on the half-open interval [i, j)
(: sublabel (case-> (-> (Option label) (Option Index) label)
                    (-> (Option label) (Option Index) (Option Index) label)))
(define sublabel
  (case-lambda
    ((label i)
     (sublabel label i (label-length label)))
    ((label i j)
     (assert i index?)
     (assert j index?)
     (unless (<= i j)
       (error 'sublabel "illegal sublabel [~a, ~a]" i j))
     (assert label label?)
     (make-label (label-datum label)
                 (+ i (assert (label-i label) exact-nonnegative-integer?))
                 (+ j (assert (label-i label) exact-nonnegative-integer?))))))

;; sublabel!: label number number -> void
;; destructively sets the input label to sublabel.
(: sublabel! (case-> (-> (Option label) (Option Index) Void)
                     (-> (Option label) (Option Index) (Option Index) Void)))
(define sublabel!
  (case-lambda
    ((label i)
     (sublabel! label i (label-length label)))
    ((label i j)
     (begin
       (assert i index?)
       (assert j index?)
       (assert label label?)
       ;; order dependent code ahead!
       (set-label-j! label (+ j (assert (label-i label) exact-nonnegative-integer?)))
       (set-label-i! label (+ i (assert (label-i label) exact-nonnegative-integer?)))
       (void)))))


;; label-prefix?: label label -> boolean
;; Returns true if the first label is a prefix of the second label
(: label-prefix? (-> (Option label) (Option label) Boolean))
(define (label-prefix? prefix other-label)
  (let ((m (label-length prefix))
        (n (label-length other-label)))
    (if (> m n)                       ; <- optimization: prefixes
					; can't be longer.
        #f
        (let loop ((k 0))
          (if (= k m)
              #t
              (and (index? k)
                   (equal? (label-ref prefix k) (label-ref other-label k))
                   (loop (add1 k))))))))


;; label-equal?: label label -> boolean
;; Returns true if the two labels are equal.
(: label-equal? (-> (Option label) (Option label) Boolean))
(define (label-equal? l1 l2)
  (and (= (label-length l1) (label-length l2))
       (label-prefix? l1 l2)))


;; label-empty?: label -> boolean
;; Returns true if the label is considered empty
(: label-empty? (-> (Option label) Boolean))
(define (label-empty? label)
  (assert label label?)
  (>= (assert (label-i label) exact-nonnegative-integer?)
      (assert (label-j label) exact-nonnegative-integer?)))


;; label->string: label -> string
;; Extracts the string that the label represents.
;; Precondition: the label must have originally come from a string.
;; Note: this operation is expensive: don't use it except for debugging.
(: label->string (-> (Option label) String))
(define (label->string label)
  (: V (Vectorof (U Char Symbol)))
  (define V (label->vector label))
  (: L (Listof Char))
  (define L (for/list : (Listof Char)
                      ([c : (U Char Symbol) (in-vector V)])
              (unless (char? c) (error "label->string invariant broken"))
              c))
  (list->string L))

(: label->string/removing-sentinel (-> (Option label) String))
(define (label->string/removing-sentinel label)
  (let* ([ln (label-length label)]
         [N (if (and (> ln 0) (sentinel? (label-ref label (sub1 ln))))
                (sub1 ln)
                ln)])
    (build-string N (lambda ([i : Integer])
                      (unless (index? i) (error "label->string 1"))
                      (let ([val (label-ref label i)])
                        (unless (char? val) (error "label->string 2"))
                        val)))))

;; label->vector: label -> vector
;; Extracts the vector that the label represents.
;; Note: this operation is expensive: don't use it except for debugging.
(: label->vector (-> (Option label) (Vectorof (U Char Symbol))))
(define (label->vector label)
  (: N Integer)
  (define N (label-length label))
  (: buffer (Vectorof (U Char Symbol)))
  (define buffer (make-vector N 'X));;'X is a placeholder
    (let loop ((i 0))
      (if (and (< i N) (index? i))
          (begin
            (let ((v (label-ref label i)))
              (if (or (char? v) (symbol? v))
                (vector-set! buffer i v)
                (error 'dynamic-typecheck)))
           (loop (add1 i)))
          (vector->immutable-vector buffer))))


;; label-copy: label->label
;; Returns a copy of the label.
(: label-copy (-> (Option label) label))
(define (label-copy label)
  (assert label label?)
  (make-label (label-datum label) (label-i label) (label-j label)))


;; label-ref-at-end?: label number -> boolean
(: label-ref-at-end? (-> (Option label) (Option Integer) Boolean))
(define (label-ref-at-end? label offset)
  (= (assert offset integer?) (label-length label)))


;; label-source-id: label -> number
(: label-source-id (-> (Option label) Integer))
(define (label-source-id label)
  (eq-hash-code (label-datum (assert label label?))))

;; label-same-source?: label label -> boolean
(: label-same-source? (-> (Option label) (Option label) Boolean))
(define (label-same-source? label-1 label-2)
  (eq? (label-datum (assert label-1 label?)) (label-datum (assert label-2 label?))))

;; --- from suffixtree.rkt
(define label-source-eq? label-same-source?)
