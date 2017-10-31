#lang racket/base

(provide
  TR-DATA*
  overhead-plot*)

(require
  file/glob
  gtp-plot/plot
  gtp-plot/typed-racket-info
  with-cache
  racket/runtime-path
  pict
  gtp-plot/util
  (only-in racket/path
    file-name-from-path)
  (only-in racket/math
    exact-floor))

;; =============================================================================

(define-runtime-path CWD ".")

(define RKT-VERSION "6.10.1")
(define PLOT-HEIGHT 80)
(define OVERHEADS-HSPACE 30)
(define OVERHEADS-VSPACE 6)
(define OVERHEADS-WIDTH 600)
(define NUM-COLUMNS 3)
(define CACHE-DIR "cache")

(define BM-NAME* '(
  fsm gregor kcfa morsecode sieve snake suffixtree synth tetris zombie))

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

(define TR-DATA*
  (sort-by-size
    (for/list ([name (in-list BM-NAME*)])
      (glob-first (build-path CWD ".." "data" RKT-VERSION (format "~a-*.rktd" name))))))

(define (overhead-plot* x*)
  (define W (exact-floor (/ (- OVERHEADS-WIDTH OVERHEADS-HSPACE) NUM-COLUMNS)))
  (define plot*
    (parameterize ([*OVERHEAD-SHOW-RATIO* #f]
                   [*OVERHEAD-PLOT-HEIGHT* PLOT-HEIGHT]
                   [*OVERHEAD-MAX* 10]
                   [*OVERHEAD-PLOT-WIDTH* W]
                   [*LEGEND-VSPACE* 2]
                   [*LEGEND-HSPACE* 4]
                   [*FONT-SIZE* 8]
                   [*current-cache-directory* (build-path CWD CACHE-DIR)]
                   [*current-cache-keys* (list (λ () (list OVERHEADS-WIDTH PLOT-HEIGHT OVERHEADS-VSPACE OVERHEADS-HSPACE)))]
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
   [else
    (raise-argument-error 'data->plot "unrecognized data format" x)]))
