#lang racket/base

(provide
  TR-DATA*
  TAG-DATA*
  tag-color-sample
  tr-color-sample
  NUM-TR
  X-MAX
  overhead-plot*)

(require
  file/glob
  gtp-plot/plot
  gtp-plot/typed-racket-info
  with-cache
  racket/runtime-path
  pict
  gtp-plot/util
  (only-in racket/string
    string-prefix?)
  (only-in racket/draw
    make-color)
  (only-in plot/utils
    ->brush-color
    ->pen-color)
  (only-in racket/path
    file-name-from-path)
  (only-in racket/math
    exact-floor))

(module+ test
  (require rackunit))

;; =============================================================================

(define-runtime-path CWD ".")

(define RKT-VERSION "6.10.1")
(define TAG-VERSION "v0.12")
(define PLOT-HEIGHT 80)
(define OVERHEADS-HSPACE 30)
(define OVERHEADS-VSPACE 6)
(define OVERHEADS-WIDTH 600)
(define NUM-COLUMNS 3)
(define X-MAX 10)
(define CACHE-DIR "cache")
(define START-COLOR 3)

(define BM-NAME* '(
  fsm gregor kcfa morsecode sieve snake suffixtree synth tetris zombie))

(define (color-sample i)
  (define border-color (apply make-color (->pen-color i)))
  (define fill-color (apply make-color (->brush-color i)))
  (filled-rounded-rectangle 8 8 #:color fill-color #:border-color border-color #:border-width 1))

(define tr-color-sample
  (color-sample START-COLOR))

(define tag-color-sample
  (color-sample (+ 1 START-COLOR)))

;; -----------------------------------------------------------------------------

(define (glob-first pattern)
  (define r* (glob pattern))
  (cond
   [(null? r*)
    (raise-arguments-error 'glob "no matches" "pattern" pattern)]
   [(not (null? (cdr r*)))
    (raise-arguments-error 'glob "multiple matches" "pattern" pattern "matches" r*)]
   [else
    (car r*)]))

(define (sort-by-size fname*)
  (map car (sort (map cons fname* (map line-count fname*)) < #:key cdr)))

(define (line-count fname)
  (with-input-from-file fname
    (λ ()
      (for/sum ((ln (in-lines))) 1))))

(define (data-files name->pattern)
  (sort-by-size
    (for/list ([name (in-list BM-NAME*)])
      (glob-first (name->pattern name)))))

(define TR-DATA*
  (let ([name->pattern (lambda (name) (build-path CWD ".." "data" RKT-VERSION (format "~a-*.rktd" name)))])
    (data-files name->pattern)))

(define TAG-DATA*
  (let ([name->pattern (lambda (name) (build-path CWD ".." "data" TAG-VERSION (format "tag_~a-*.rktd" name)))])
    (data-files name->pattern)))

(define NUM-TAG
  (number->string (length TAG-DATA*)))

(define NUM-TR
  (number->string (length TR-DATA*)))

(define (overhead-plot* x*)
  (define W (exact-floor (/ (- OVERHEADS-WIDTH OVERHEADS-HSPACE) NUM-COLUMNS)))
  (define plot*
    (parameterize ([*OVERHEAD-SHOW-RATIO* #f]
                   [*OVERHEAD-PLOT-HEIGHT* PLOT-HEIGHT]
                   [*OVERHEAD-LINE-COLOR* START-COLOR]
                   [*OVERHEAD-MAX* X-MAX]
                   [*OVERHEAD-PLOT-WIDTH* W]
                   [*LEGEND-VSPACE* 2]
                   [*LEGEND-HSPACE* 4]
                   [*LEGEND?* #false]
                   [*FONT-SIZE* 8]
                   [*current-cache-directory* (build-path CWD CACHE-DIR)]
                   [*current-cache-keys* (list (λ () (list X-MAX OVERHEADS-WIDTH PLOT-HEIGHT OVERHEADS-VSPACE OVERHEADS-HSPACE)))]
                   [*with-cache-fasl?* #f])
      (for/list ([x (in-list x*)])
        (define filename (data->filename x))
        (with-cache (cachefile filename)
          (λ ()
            (log-gtp-plot-info "rendering ~a" filename)
            (collect-garbage 'major)
            (data->plot x))))))
  (define col*
    (map (λ (p*) (apply vl-append OVERHEADS-VSPACE p*))
         (columnize plot* NUM-COLUMNS)))
  (apply ht-append OVERHEADS-HSPACE col*))

(define (data->filename x)
  (cond
   [(path-string? x)
    (format "tr-~a.rktd" (filename->prefix x))]
   [(pair? x)
    (define tr (car x))
    (define tag (cdr x))
    (define tr-prefix (filename->prefix tr))
    (define tag-prefix (filename->prefix tag))
    (unless (string-prefix? tag-prefix "tag_")
      (raise-arguments-error 'data->filename "expected a tagged racket filename"
        "filename" tag))
    (unless (equal? tr-prefix (substring tag-prefix 4))
      (raise-arguments-error 'data->filename "datasets have mis-matched prefix"
        "data 0" tr
        "prefix 0" tr-prefix
        "data 1" tag
        "prefix 1" tag-prefix))
    (format "tr-vs-tag-~a.rktd" tr-prefix)]
   [else
    (raise-argument-error 'data->filename "unrecognized data format" x)]))

(define (filename->prefix ps)
  (list->string
    (for/list ([c (in-string (path-string->string (file-name-from-path ps)))]
               #:break (memq c '(#\- #\.)))
      c)))

(define (data->plot x)
  (cond
   [(path-string? x)
    (overhead-plot (make-typed-racket-info x))]
   [(pair? x)
    (overhead-plot (list (make-typed-racket-info (car x)) (make-typed-racket-info (cdr x))))]
   [else
    (raise-argument-error 'data->plot "unrecognized data format" x)]))

;; =============================================================================

(module+ test
  (test-case "tag/type data matches"
    (check-equal? NUM-TAG NUM-TR))
)
