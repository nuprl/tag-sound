#lang racket/base

;; Defines datasets,
;;  exports functions for building plots.

;; Most of the actual plotting is done in the `gtp-plot` library,
;;  this is just a front-end that sets the right parameters for this paper.

(provide
  BM-NAME*
  TR-DATA*
  TAG-DATA*
  RKT-VERSION
  RKT-RELEASE-MONTH
  tag-color-text
  tr-color-text
  tag-color-sample
  tr-color-sample
  NUM-TR
  NUM-ITERS
  X-MAX

  OVERHEADS-HEIGHT
  OVERHEADS-WIDTH
  FONT-SIZE

  *bar-chart-max*
  *bar-chart-height*

  overhead-plot*
  exact-plot*

  models-roadmap

  render-max-overhead
  make-ratios-table
  make-max-table
  make-typed-table
  render-ratios-table
  render-max-table
  ratios-table->typed
  max-table->typed
  render-speedup-barchart

  db-app-pict
  reynolds-pict)

(require
  "lined-codeblock.rkt"
  file/glob
  (only-in gtp-plot/configuration-info
    configuration-info->id
    configuration-info->runtime*)
  gtp-plot/plot
  gtp-plot/typed-racket-info
  (only-in gtp-plot/performance-info
    typed/baseline-ratio
    in-configurations
    performance-info->typed-runtime
    performance-info->untyped-runtime
    max-overhead)
  gtp-util
  (only-in gtp-util/system
    md5sum)
  with-cache
  racket/runtime-path
  (only-in racket/format ~r)
  pict
  (only-in scribble/manual
    centered
    tabular
    bold
    tt
    hspace)
  (only-in racket/string
    string-prefix?)
  racket/draw
  (only-in racket/class new send)
  (only-in plot/no-gui
    hrule
    plot-pict
    error-bars
    discrete-histogram)
  plot/utils
  (only-in racket/path
    file-name-from-path)
  (only-in racket/file
    file->value)
  (only-in racket/port
    with-input-from-string)
  (only-in math/statistics
    mean)
  (only-in racket/math
    exact-round
    exact-ceiling
    exact-floor))

(module+ test
  (require rackunit))

;; =============================================================================

(define-runtime-path CWD ".")

(define RKT-VERSION "6.10.1")
(define RKT-RELEASE-MONTH "September 2017")
(define NUM-SAMPLES 200)
(define TAG-VERSION "v0.15")
(define OVERHEADS-HEIGHT (make-parameter 640))
(define OVERHEADS-HSPACE 50)
(define OVERHEADS-VSPACE 6)
(define OVERHEADS-WIDTH (make-parameter 450))
(define NUM-COLUMNS 2)
(define X-MAX 10)
(define CACHE-DIR "cache")
(define FONT-SIZE (make-parameter 8))
(define TR-BRUSH-STYLE 'solid)
(define LD-BRUSH-STYLE 'fdiagonal-hatch)
(define TR-POINT-SYMBOL 'fullcircle)
(define LD-POINT-SYMBOL 'circle)

(define START-COLOR 3)
(define TICK-FREQ 1)

(define *bar-chart-height* (make-parameter 84))
(define *bar-chart-log-scale* (make-parameter #false))
(define *bar-chart-min* (make-parameter #false))
(define *bar-chart-max* (make-parameter #false))
(define neutral-color 0)

(define ((my-color-converter kind) i)
  (case kind
   [(brush)
    (->brush-color (if (= i START-COLOR) "CornflowerBlue" "darkorange"))]
   [(pen)
    (->pen-color i)]
   [else
    (raise-argument-error 'my-color-converter "unknown kind" 0 kind i)]))

(define BM-NAME* '(
  fsm jpeg kcfa morsecode sieve snake suffixtree synth tetris zombie))

(define (->brush-style i)
  (if (= i START-COLOR)
    TR-BRUSH-STYLE
    LD-BRUSH-STYLE))

(define (draw-shape/border w h draw-fun
                           color [border-color #f] [border-width #f]
                           [brush-style 'solid])
  (dc (λ (dc dx dy)
        (define old-brush (send dc get-brush))
        (define old-pen   (send dc get-pen))
        (send dc set-brush
              (send the-brush-list find-or-create-brush
                    (cond
                          [color        color]
                          [else         (send old-pen get-color)])
                    brush-style))
            (when (or border-color border-width)
              ;; otherwise, leave pen as is
              (send dc set-pen (send the-pen-list
                                     find-or-create-pen
                                     (or border-color
                                         (send old-pen get-color))
                                     (or border-width
                                         (send old-pen get-width))
                                     (send old-pen get-style))))
        (draw-fun dc dx dy)
        (send dc set-brush old-brush)
        (send dc set-pen   old-pen))
      w h))

(define (filled-rounded-rectangle w h [corner-radius -0.25]
                                  #:brush-style [bs 'solid]
                                  #:color        [color #f]
                                  #:border-color [border-color #f]
                                  #:border-width [border-width #f])
  (define dc-path (new dc-path%))
  (send dc-path rounded-rectangle 0 0 w h corner-radius)
  (let-values ([(x y w h) (send dc-path get-bounding-box)])
    (draw-shape/border w h
                       (lambda (dc dx dy)
                         (send dc draw-path dc-path (- dx x) (- dy y)))
                       color border-color border-width bs)))

(define color-sample
  (let ([->pen (my-color-converter 'pen)]
        [->brush (my-color-converter 'brush)])
    (lambda (i)
      (define border-color (apply make-color (->pen i)))
      (define fill-color (apply make-color (->brush i)))
      (define fill-style (->brush-style i))
      (filled-rounded-rectangle 8 8
                                #:brush-style fill-style
                                #:color fill-color
                                #:border-color border-color
                                #:border-width 1))))

(define (color-text i)
  (case i
    [(0) "black"]
    [(1) "red"]
    [(2) "green"]
    [(3) "blue"]
    [(4) "orange"]
    [(5) "slate"]
    [else "purple"]))

(define-values [tr-color-sample tr-color-text]
  (let ([tr-color START-COLOR])
    (values (color-sample tr-color) (color-text tr-color))))

(define-values [tag-color-sample tag-color-text]
  (let ([tag-color (+ 1 START-COLOR)])
    (values (color-sample tag-color) (color-text tag-color))))

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
      (for/sum ((ln (in-lines)))
        (if (comment-line? ln) 0 1)))))

(define (comment-line? str)
  (string-prefix? str ";"))

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
  (length TR-DATA*))

(define NUM-ITERS
  ;; TODO
  8)

(define (make-plot* make-f x* [extra-tag #f])
  (define base-cache-keys (list *GRID-X* *GRID-Y* *GRID-NUM-COLUMNS* *OVERHEAD-MAX*))
  (parameterize ([*OVERHEAD-SHOW-RATIO* #f]
                 [*OVERHEAD-SAMPLES* NUM-SAMPLES]
                 [*OVERHEAD-LINE-COLOR* START-COLOR]
                 [*OVERHEAD-MAX* X-MAX]
                 [*GRID-X* (OVERHEADS-WIDTH)]
                 [*GRID-Y* (OVERHEADS-HEIGHT)]
                 [*GRID-X-SKIP* OVERHEADS-HSPACE]
                 [*GRID-Y-SKIP* OVERHEADS-VSPACE]
                 [*GRID-NUM-COLUMNS* NUM-COLUMNS]
                 [*LEGEND?* #false]
                 [*LEGEND-VSPACE* 4]
                 [*FONT-SIZE* (FONT-SIZE)]
                 [*BRUSH-COLOR-CONVERTER* (my-color-converter 'brush)]
                 [*PEN-COLOR-CONVERTER* (my-color-converter 'pen)]
                 [*MULTI-INTERVAL-STYLE* (list TR-BRUSH-STYLE LD-BRUSH-STYLE)]
                 [*MULTI-POINT-SYMBOL* (list TR-POINT-SYMBOL LD-POINT-SYMBOL)]
                 [*with-cache-fasl?* #f]
                 ;[*use-cache?* #false]
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
  (parameterize ([*OVERHEAD-FREEZE-BODY* #false]
                 [*POINT-COLOR* START-COLOR])
    (make-plot* data->exact-plot x* "exact")))

(define (ratios-only data**)
  (for/list ([tr+tag (in-list data**)])
    (map data->ratios tr+tag)))

(define (data->ratios fname)
  (define v (file->value fname))
  (map / (vector-ref v (- (vector-length v) 1))
         (vector-ref v 0)))
  #;(define-values [data-0 data-N]
    (with-input-from-file fname
      (values
        (for/first ((ln (in-lines))
                    #:when (list? (string->list ln)))
          (string->list ln))
        (for/last ((ln (in-lines))
                   #:when (list? (string->list ln)))
          (string->list ln)))))
  #;(map / data-N data-0)

(define (string->list str)
  (with-handlers ((exn:fail:read? (lambda (x) #false)))
    (with-input-from-string str read)))

;(define (ratios-plot tr-data* tag-data*)
;  ;; input (listof (list tr tag))
;  ;; - [ ] plot average
;  ;; - [ ] plot error bars
;  (define tr-ratio** (ratios-only tr-data*))
;  (define tag-ratio** (ratios-only tag-data*))
;  (define name*
;    (for/list ([tr (in-list tr-data*)])
;      (render-table-name (filename->prefix tr))))
;  (define SKIP 2)
;  (define WIDTH OVERHEADS-WIDTH)
;  (parameterize ([plot-font-size 8]
;                 [plot-x-ticks no-ticks])
;    (plot-pict
;      (list
;        ;; TODO error bars
;        (for/list ([x-min (in-naturals START-COLOR)]
;                   [col-title (in-list (list "TR" "LD"))] ;; TODO
;                   [r** (in-list (list tr-ratio** tag-ratio**))])
;          (discrete-histogram
;            #:skip SKIP
;            #:x-min x-min
;            #:label "ugh"
;            #:color x-min
;            (for/list ([r* (in-list r**)]
;                       [name (in-list name*)])
;              (define y (mean r*))
;              (vector name y))))))))

(define (data->filename x)
  (cond
   [(path-string? x)
    (format "tr-~a.rktd" (filename->prefix x))]
   [(pair? x)
    (define tr (path->string (file-name-from-path (car x))))
    (define tag (path->string (file-name-from-path (cadr x))))
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

(define (data->typed/untyped-runtime* x)
  (cond
    [(path-string? x)
     (define pi (make-typed-racket-info x))
     (cons (performance-info->typed-runtime* pi)
           (performance-info->untyped-runtime* pi))]
    [else
     (raise-argument-error 'data->typed/baseline-ratio "unrecognized data format" x)]))

(define (performance-info->runtime* pi good-cfg?)
  (for/or ((cfg (in-configurations pi)))
    (and (good-cfg? cfg)
         (configuration-info->runtime* cfg))))

(define (performance-info->typed-runtime* pi)
  (performance-info->runtime* pi typed-config?))

(define (performance-info->untyped-runtime* pi)
  (performance-info->runtime* pi untyped-config?))

(define (typed-config? cfg)
  (for/and ([c (in-string (configuration-info->id cfg))])
    (eq? c #\1)))

(define (untyped-config? cfg)
  (for/and ([c (in-string (configuration-info->id cfg))])
    (eq? c #\0)))

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

(define (render-max-overhead kind bm-name #:tbl [tbl #f] #:precision [psc #f])
  (unless (valid-embedding? kind)
    (raise-argument-error 'max-overhead "valid-embedding?" 0 kind bm-name))
  (unless (memq bm-name BM-NAME*)
    (raise-argument-error 'max-overhead "benchmark-name?" 1 kind bm-name))
  (define overhead
    (if tbl
      (max-table-lookup tbl kind bm-name)
      (let ([rktd
             (case kind
              [(typed)
               (find-rktd TR-DATA* bm-name)]
              [(tagged)
               (find-rktd TAG-DATA* bm-name)]
              [else
               (error 'impossible)])])
        (max-overhead (make-typed-racket-info rktd)))))
  (define rounded
    (if psc
      (~r overhead #:precision psc)
      (number->string (exact-round overhead))))
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

(define (make-typed-table . data**)
  (make-data-table data->typed/untyped-runtime* data** "typed-runtime"))

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
                 [*current-cache-directory* (build-path CWD CACHE-DIR)]
                 [*current-cache-keys* (list (lambda () md5*))])
    (with-cache (cachefile (string-append key ".rktd"))
      (λ ()
        (define col0 (map filename->prefix (car data**)))
        (define col*
          (for/list ([data* (in-list data**)])
            (for/list ([data (in-list data*)])
              (data->number data))))
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
       (list "" "TR-N" "TR-LD")))

(define (render-numbers-table rt titles)
  (centered
    (tabular
      #:sep (hspace 2)
      #:style 'block
      #:row-properties '(left right)
      #:column-properties '(right)
      (map cons (cons "" titles)
                (cons (map render-table-name (car rt))
                      (for/list ([r (in-list (cdr rt))])
                        (for/list ([x (in-list r)])
                          (string-append (rnd x) "x"))))))))

;; render-speedup-barchart : (-> (list/c (listof symbol?) (listof (listof (cons/c natural? natural?))) (listof (listof (cons/c natural? natural?)))) pict?)
(define (render-speedup-barchart tbl)
  (make-plot-labeled-data discrete-histogram/error-bars tbl #:invert? #true))

(define (make-plot-labeled-data render-labeled-reals tbl #:invert? [invert? #false])
  (define rt
    ;; Immediately normalize the data into a table-like thing ... this function is doing too much
    (cons (car tbl)
          (for/list ([ab* (in-list (cdr tbl))])
            (for/list ([ab (in-list ab*)])
              (if invert?
                (map / (cdr ab) (car ab))
                (map / (car ab) (cdr ab)))))))
  (define y-max (exact-ceiling (max*** (cdr rt))))
  (parameterize ([plot-x-ticks no-ticks]
                 [plot-y-ticks (make-overhead-bars-ticks)]
                 [plot-y-transform (if (*bar-chart-log-scale*) log-transform id-transform)]
                 [error-bar-width 8]
                 [error-bar-alpha 0.8]
                 [error-bar-line-width 1])
    (define (make-tick-hrule y)
      (hrule y #:color neutral-color #:style 'solid #:alpha 0.2))
    (plot-pict
      (append
        (if (*bar-chart-log-scale*)
          (for*/list ((i (in-range 0 (exact-ceiling (log y-max 10))))
                      (j (in-range 2 10 2)))
            (make-tick-hrule (* (expt 10 i) j)))
          (for/list ((i (in-range 0 (* TICK-FREQ (or (*bar-chart-max*) y-max)))))
            (make-tick-hrule (/ i TICK-FREQ))))
        (for/list ([c*r (in-list (list cadr caddr))]
                   [color (in-naturals START-COLOR)]
                   [style (in-list (list TR-BRUSH-STYLE LD-BRUSH-STYLE))]
                   [x-min (in-naturals 0)])
          (render-labeled-reals
            (for/list ([lbl (in-list (car rt))]
                       [r (in-list (c*r rt))])
              (list lbl r))
            #:color color
            #:style style
            #:x-min x-min
            #:skip 3))
        (list (hrule 1 #:color 0 #:style 'solid #:alpha 1)))
      #:title #f
      #:x-min 0
      ;#:x-max #f
      #:y-min (*bar-chart-min*)
      #:y-max (or (*bar-chart-max*) (round-ymax y-max))
      #:x-label #false
      #:y-label #false
      #:width (OVERHEADS-WIDTH)
      #:height (*bar-chart-height*))))

(define (rnd+ n)
  (if (exact-integer? n)
    (number->string n)
    (~r n #:precision '(= 1))))

(define (make-overhead-bars-ticks)
  (if (*bar-chart-log-scale*)
    (ticks (λ (ax-min ax-max)
             (define major-ticks
               (for/list ((i (in-range 0 (log ax-max 10))))
                 (pre-tick (expt 10 i) #true)))
             (define minor-ticks
               (for*/list ((i (in-range 0 (exact-ceiling (log ax-max 10))))
                           (j (in-range 2 10 2)))
                   (pre-tick (* (expt 10 i) j) #false)))
             (append minor-ticks major-ticks))
           (lambda (ax-min ax-max pre-ticks)
             (for/list ([pt (in-list pre-ticks)])
               (format "10~a" (integer->superscript (exact-floor (log (pre-tick-value pt) 10)))))))
    (ticks (lambda (ax-min ax-max)
             (define major-ticks
               (for/list ((i (in-list (linear-seq ax-min ax-max 3 #:start? #true #:end? #true))))
                 (pre-tick (exact-floor i) #true)))
             (define minor-ticks
               (for/list ((i (in-range (* ax-min TICK-FREQ) (* ax-max TICK-FREQ))))
                 (pre-tick (/ i TICK-FREQ) #false)))
             (define candidate-ticks
               (append major-ticks minor-ticks))
             (cond
               [(for/or ([tick (in-list candidate-ticks)])
                  (= (pre-tick-value tick) 1))
                candidate-ticks]
               [else
                (cons (pre-tick 1 #t) candidate-ticks)]))
           (lambda (ax-min ax-max pre-ticks)
             (for/list ((pt (in-list pre-ticks)))
               (define str (rnd+ (pre-tick-value pt)))
               (if (= (pre-tick-value pt) ax-max)
                 (string-append str "x")
                 str))))))

(define (discrete-histogram/error-bars labeled-r* #:x-min [x-min 0] #:skip [skip 2] #:color [color 0] #:add-ticks? [add-ticks? #true] #:style [style 'solid])
  ;; 2018-05-10 : currently NOT plotting error bars, because `labeled-r*` doesn't have enough data
  (list
    (discrete-histogram
      (for/list ([lbl+r* (in-list labeled-r*)])
        (vector (car lbl+r*) (mean (cadr lbl+r*))))
      #:alpha 0.9 #;(*MULTI-INTERVAL-ALPHA*)
      #:x-min x-min
      #:skip skip
      #:label #f
      #:style style
      #:color ((my-color-converter 'brush) color)
      #:line-color ((my-color-converter 'pen) color)
      #:add-ticks? add-ticks?)
    (if (*bar-chart-log-scale*)
      '()
      (error-bars
        (for/list ([lbl+r* (in-list labeled-r*)]
                   [i (in-naturals)])
          (define x (+ 1/2 (+ x-min (* i skip))))
          (define lo+hi (confidence-interval (cadr lbl+r*) #:cv 1.96))
          (vector x
                  (mean (list (car lo+hi) (cdr lo+hi)))
                  (- (cdr lo+hi) (car lo+hi))))))))

(define render-ratios-table render-numbers-table)
(define render-max-table render-numbers-table)

(define (table-lookup tbl embedding bm-name)
  (or
    (for/or ([name (in-list (cdr (car tbl)))]
             [tr (in-list (cdr (cadr tbl)))]
             [ld (in-list (cdr (caddr tbl)))])
      (and (eq? (string->symbol name) bm-name)
           (if (eq? embedding 'typed) tr ld)))
    (raise-arguments-error 'table-lookup "not found" "key" bm-name "table" tbl "embedding" embedding)))

(define max-table-lookup table-lookup)
(define ratios-table-lookup table-lookup)

(define (table->typed rt)
  (cdr (cadr rt)))

(define ratios-table->typed table->typed)
(define max-table->typed table->typed)

(define (table->locally-defensive rt)
  (cdr (caddr rt)))

(define ratios-table->locally-defensive table->locally-defensive)
(define max-table->locally-defensive table->locally-defensive)

(define (round-ymax y)
  (if (*bar-chart-log-scale*)
    (round-up-to-next-log10-tick y)
    y))

(define (round-up-to-next-log10-tick n)
  (let loop ([i 0])
    (define e (expt 10 i))
    (if (<= e n)
      (loop (+ i 1))
      e)))

(define (max*** x***)
  (for*/fold ((acc #false))
             ((x** (in-list x***))
              (x* (in-list x**))
              (x (in-list x*)))
    (if (or (not acc) (< acc x))
      x
      acc)))

(define reynolds-pict
  (ht-append 60
    (codeblock-pict/numbers #:title "bessel.rkt"
#<<>>
#lang typed/racket

(define-type Bessel
  (List Nonnegative-Real Real))

(: add_B (-> Bessel Bessel Bessel))
(define (add_B b0 b1)
  (map + b0 b1))
>>
)
    (codeblock-pict/numbers #:title "student.rkt"
#<<>>
#lang racket

(require "bessel.rkt")

(define d0 (list 4 0))
(define d1 (list -2 1))

(add_B d0 d1)
>>
)))

(define db-app-pict
  (ht-append 20
    (codeblock-pict/numbers #:title "database.rkt"
#<<>>
#lang racket

(define (create db name)
  (exec_query ...))

;; ...
>>
)
    (codeblock-pict/numbers #:title "typed_db.rkt"
#<<>>
#lang typed/racket

(require/typed/provide
  "database.rkt"
  [#:opaque DB
   sql_connection?]
  [create
   (-> DB Username
       Boolean)])

(define-type Username
  Symbol)
>>
)
    (codeblock-pict/numbers #:title "app.rkt"
#<<>>
#lang racket

(require
  "typed_db.rkt")

(define (serve r)
  (if (new_user? r)
    (create ...)
    ...))

;; ...
>>
)))

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
