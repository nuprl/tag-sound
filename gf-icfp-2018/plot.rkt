#lang racket/base

;; Defines datasets,
;;  exports functions for building plots.

;; Most of the actual plotting is done in the `gtp-plot` library,
;;  this is just a front-end that sets the right parameters for this paper.

(provide
  BM-NAME*
  TR-DATA*
  TAG-DATA*
  tag-color-sample
  tr-color-sample
  NUM-TR
  NUM-ITERS
  X-MAX
  TR
  LD-Racket
  overhead-plot*
  exact-plot*
  models-roadmap
  render-max-overhead
  make-ratios-table
  make-max-table
  render-ratios-table
  render-max-table
  fishtank-pict
  fishtank/biohazard
  fishtank/biohazard/natural
  fishtank/biohazard/erasure
  fishtank/biohazard/locally-defensive
  RED-SNAPPER-RATIO)

(require
  file/glob
  gtp-plot/plot
  gtp-plot/typed-racket-info
  (only-in scribble/manual
    centered
    tabular
    bold
    tt
    hspace)
  (only-in gtp-plot/performance-info
    typed/baseline-ratio
    max-overhead)
  with-cache
  racket/runtime-path
  (only-in racket/format ~r)
  pict
  gtp-plot/util
  (only-in gtp-plot/system
    md5sum)
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
    exact-round
    exact-floor))

(module+ test
  (require rackunit))

;; =============================================================================

(define-runtime-path CWD ".")

(define RKT-VERSION "6.10.1")
(define NUM-SAMPLES 200)
(define TAG-VERSION "v0.14")
(define OVERHEADS-HEIGHT 670)
(define OVERHEADS-HSPACE 30)
(define OVERHEADS-VSPACE 6)
(define OVERHEADS-WIDTH 600)
(define NUM-COLUMNS 2)
(define X-MAX 10)
(define CACHE-DIR "cache")
(define LD-Racket "Locally-Defensive Racket")
(define TR "Typed Racket")


(define START-COLOR 3)

(define ((my-color-converter kind) i)
  (case kind
   [(brush)
    (->brush-color (if (= i START-COLOR) "CornflowerBlue" i))]
   [(pen)
    (->pen-color i)]
   [else
    (raise-argument-error 'my-color-converter "unknown kind" 0 kind i)]))

(define BM-NAME* '(
  fsm kcfa morsecode sieve snake suffixtree synth tetris zombie))

(define color-sample
  (let ([->pen (my-color-converter 'pen)]
        [->brush (my-color-converter 'brush)])
    (lambda (i)
      (define border-color (apply make-color (->pen i)))
      (define fill-color (apply make-color (->brush i)))
      (filled-rounded-rectangle 8 8 #:color fill-color #:border-color border-color #:border-width 1))))

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

(define NUM-ITERS
  ;; TODO
  8)

(define (make-plot* make-f x* [extra-tag #f])
  (define base-cache-keys (list *GRID-X* *GRID-Y* *OVERHEAD-MAX*))
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
                 [*LEGEND-VSPACE* 4]
                 [*FONT-SIZE* 8]
                 [*BRUSH-COLOR-CONVERTER* (my-color-converter 'brush)]
                 [*PEN-COLOR-CONVERTER* (my-color-converter 'pen)]
                 [*with-cache-fasl?* #f]
                 [*current-cache-directory* (build-path CWD CACHE-DIR)])
    (define (make-overhead-plot/cache x)
      (define filename (data->cache-tag x extra-tag))
      (define current-md5 (data->md5sum x))
      (parameterize ([*current-cache-keys* (cons (λ () current-md5) base-cache-keys)])
        (with-cache (cachefile filename)
          (λ ()
            (make-f x)))))
    (grid-plot make-overhead-plot/cache x*)))

(define (overhead-plot* x*)
  (make-plot* data->plot x*))

(define (exact-plot* x*)
  (parameterize ([*OVERHEAD-FREEZE-BODY* #true]
                 [*POINT-COLOR* START-COLOR])
    (make-plot* data->exact-plot x* "exact")))

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

(define (data->md5sum x)
  (cond
   [(path-string? x)
    (md5sum x)]
   [(pair? x)
    (map md5sum x)]
   [else
    (raise-argument-error 'data->md5sum "unrecognized data format" x)]))

(define (data->cache-tag data [prefix #false])
  (define base-tag (data->filename data))
  (if prefix
    (string-append prefix "-" base-tag)
    base-tag))

(define (data->plot x)
  (cond
   [(path-string? x)
    (overhead-plot (make-typed-racket-info x))]
   [(pair? x)
    (overhead-plot (map make-typed-racket-info x))]
   [else
    (raise-argument-error 'data->plot "unrecognized data format" x)]))

(define (data->exact-plot x)
  (cond
   [(path-string? x)
    (exact-runtime-plot (make-typed-racket-info x))]
   [(pair? x)
    (exact-runtime-plot (map make-typed-racket-info x))]
   [else
    (raise-argument-error 'data->exact-plot "unrecognized data format" x)]))

(define (data->typed/baseline-ratio x)
  (cond
    [(path-string? x)
     (typed/baseline-ratio (make-typed-racket-info x))]
    [else
     (raise-argument-error 'data->typed/baseline-ratio "unrecognized data format" x)]))

(define (data->max-overhead x)
  (cond
    [(path-string? x)
     (max-overhead (make-typed-racket-info x))]
    [else
     (raise-argument-error 'data->max-overhead "unrecognized data format" x)]))

(define (models-roadmap #:D dyn-name
                        #:S sta-name
                        #:M mixed-name
                        #:E erased-name
                        #:N natural-name
                        #:L delayed-name
                        #:F forgetful-name
                        #:K tagged-name)
  (define arrow-size 4)
  (define (name->pict str)
    (text str (cons 'bold '()) 10))
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
      (ht-append 20 D S)
      M
      (ht-append 35
        E
        (vc-append 8 N L F))
      K))
  (define arrow-spec*
    (list (cons D M)
          (cons S M)
          (cons M N)
          (cons M E)
          (cons N L)
          (cons L F)
          (cons M K)))
  (for/fold ([acc tree])
            ([src+dst (in-list arrow-spec*)])
    (pin-arrow-line arrow-size acc
      (car src+dst) cb-find
      (cdr src+dst) ct-find)))

(define (render-max-overhead kind bm-name #:precision [psc #f])
  (unless (valid-embedding? kind)
    (raise-argument-error 'max-overhead "valid-embedding?" 0 kind bm-name))
  (unless (memq bm-name BM-NAME*)
    (raise-argument-error 'max-overhead "benchmark-name?" 1 kind bm-name))
  (define rktd
    (case kind
     [(typed)
      (find-rktd TR-DATA* bm-name)]
     [(tagged)
      (find-rktd TAG-DATA* bm-name)]
     [else
      (error 'impossible)]))
  (define pi (make-typed-racket-info rktd))
  (define o (max-overhead pi))
  (define rounded
    (if psc
      (~r o #:precision psc)
      (number->string (exact-round o))))
  (string-append rounded "x"))

(define (valid-embedding? k)
  (memq k '(typed tagged)))

(define (find-rktd rktd* bm-name)
  (define str (symbol->string bm-name))
  (let loop ([r* rktd*])
    (cond
     [(null? r*)
      (raise-arguments-error 'find-rktd "failed to find matching data file"
        "benchmark" bm-name
        "data files" rktd*)]
     [(regexp-match? str (car r*))
      (car r*)]
     [else
      (loop (cdr r*))])))

(define (make-ratios-table . data**)
  (make-data-table data->typed/baseline-ratio data** "ratio-table"))

(define (make-max-table . data**)
  (make-data-table data->max-overhead data** "max-table"))

(define (make-data-table data->number data** key)
  (define md5*
    (for*/list ([data* (in-list data**)]
                [data (in-list data*)])
      (md5sum data)))
  (parameterize ([*with-cache-fasl?* #false]
                 [*current-cache-directory* (build-path CWD CACHE-DIR)])
    (with-cache (cachefile (string-append key ".rktd"))
      (λ ()
        (define col0 (map filename->prefix (car data**)))
        (define col*
          (for/list ([data* (in-list data**)])
            (for/list ([data (in-list data*)])
              (rnd (data->number data)))))
        (cons col0 col*)))))

(define (render-table-name str)
  (define short-str
    (if (< (string-length str) 5)
      str
      (string-append (substring str 0 3) ".")))
  (tt short-str))

(define (list-transpose col*)
  (cond
    [(andmap null? col*)
     '()]
    [(ormap null? col*)
     (raise-argument-error 'list-transpose "list of equal-length lists" col*)]
    [else
     (define r (map car col*))
     (cons r (list-transpose (map cdr col*)))]))

(define RATIOS-TITLE*
  (map bold
       #;(list "Benchmark" TR LD-Racket)
       (list "Benchmark" "TR" "LD")))

(define (render-numbers-table rt)
  (centered
    (tabular
      #:sep (hspace 2)
      #:style 'block
      #:row-properties '(left right)
      #:column-properties '(right)
      (map cons RATIOS-TITLE* (cons (map render-table-name (car rt)) (cdr rt))))))

(define render-ratios-table render-numbers-table)
(define render-max-table render-numbers-table)

;; --- FISH

(define fishtank-scene
  (let ()
    (define W 200)
    (define H 60)
    (filled-rectangle W H #:color "CornflowerBlue" #:border-color "Black")))

(define RED-SNAPPER-RATIO 1/6)

(define (red-snapper W)
  (standard-fish W (* W RED-SNAPPER-RATIO) #:color "OrangeRed"))

(define (red-egg d)
  (filled-ellipse d d #:color "white" #:border-color "black"))

(define fishtank-pict
  (lt-superimpose
    (lb-superimpose
      fishtank-scene
      (red-egg 6))
    (red-snapper 60)))

(define biohazard-pict
  (text "!!!" '() 40))

(define (pathway-pict a b path)
  (hc-append 5 a path b))

(define (fishtank-pathway p)
  (pathway-pict fishtank-pict biohazard-pict p))

(define fishtank/biohazard
  (fishtank-pathway (blank 10 2)))

(define fishtank/biohazard/natural
  (fishtank-pathway (file-icon 40 50 "bisque")))

(define fishtank/biohazard/erasure
  (fishtank-pathway (filled-rectangle 10 10 #:color "green" #:border-color "green")))

(define fishtank/biohazard/locally-defensive
  (fishtank-pathway (rectangle 10 10 #:border-color "OrangeRed")))

;; =============================================================================

(module+ test
  (require rackunit)

  (test-case "tag/type data matches"
    (check-equal? NUM-TAG NUM-TR))

  (test-case "render-max-overhead"
    (check-equal?
      (render-max-overhead 'typed 'fsm)
      "1280x")
    (check-equal?
      (render-max-overhead 'tagged 'fsm)
      "2x"))

  ;; TODO get and check NUM-ITERS
)
