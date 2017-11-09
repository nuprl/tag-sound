#lang racket/base

;; Defines datasets,
;;  exports functions for building plots.

;; Most of the actual plotting is done in the `gtp-plot` library,
;;  this is just a front-end that sets the right parameters for this paper.

(provide
  TR-DATA*
  TAG-DATA*
  tag-color-sample
  tr-color-sample
  NUM-TR
  X-MAX
  overhead-plot*
  models-roadmap)

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
(define NUM-SAMPLES 200)
(define TAG-VERSION "v0.12")
(define OVERHEADS-HEIGHT 800)
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
  (parameterize ([*OVERHEAD-SHOW-RATIO* #f]
                 [*OVERHEAD-SAMPLES* NUM-SAMPLES]
                 [*OVERHEAD-LINE-COLOR* START-COLOR]
                 [*OVERHEAD-MAX* X-MAX]
                 [*GRID-X* OVERHEADS-WIDTH]
                 [*GRID-Y* OVERHEADS-HEIGHT]
                 [*GRID-X-SKIP* OVERHEADS-HSPACE]
                 [*GRID-Y-SKIP* OVERHEADS-VSPACE]
                 [*GRID-NUM-COLUMNS* NUM-COLUMNS]
                 [*LEGEND?* #false]
                 [*FONT-SIZE* 8]
                 [*with-cache-fasl?* #f]
                 [*current-cache-keys* (list *GRID-X* *GRID-Y* *OVERHEAD-MAX*)]
                 [*current-cache-directory* (build-path CWD CACHE-DIR)])
    (define (make-overhead-plot/cache x)
      (define filename (data->filename x))
      (with-cache (cachefile filename)
        (λ ()
          (data->plot x))))
    (grid-plot make-overhead-plot/cache x*)))

(define (data->filename x)
  (cond
   [(path-string? x)
    (format "tr-~a.rktd" (filename->prefix x))]
   [(pair? x)
    (define tr (car x))
    (define tag (cadr x))
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
    (overhead-plot (map make-typed-racket-info x))]
   [else
    (raise-argument-error 'data->plot "unrecognized data format" x)]))

(define (models-roadmap #:D dyn-name
                        #:S sta-name
                        #:M mixed-name
                        #:E erased-name
                        #:N natural-name
                        #:L delayed-name
                        #:F forgetful-name
                        #:K tagged-name)
  (define (name->pict str)
    (text str (cons 'bold '())))
  (define D (name->pict dyn-name))
  (define S (name->pict sta-name))
  (define M (name->pict mixed-name))
  (define E (name->pict erased-name))
  (define N (name->pict natural-name))
  (define L (name->pict delayed-name))
  (define F (name->pict forgetful-name))
  (define K (name->pict tagged-name))
  (define empty (blank 0 0))
  (define tree
    (vc-append 8
      (hb-append 20 D S)
      M
      (hb-append 35 N E)
      (hb-append 10 empty L)
      (hb-append 10 empty F)
      K))
  empty)


;; =============================================================================

(module+ test
  (test-case "tag/type data matches"
    (check-equal? NUM-TAG NUM-TR))
)
