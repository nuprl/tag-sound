#lang racket/base

(require
  gf-icfp-2018/talk/src/constant
  gf-icfp-2018/plot
  gtp-plot/plot
  pict
  plot/utils
  (only-in scribble-abbrevs/pict add-border)
  (only-in gtp-util save-pict)
  racket/runtime-path)

(define-runtime-path cache-scatterplots.png "cache-scatterplots.png")

;; -----------------------------------------------------------------------------

(define data* (map list TR-DATA* TAG-DATA*))

(define (nat->color n)
  (case n
    ((0) GREEN) ;; E
    ((1) LIGHT-RED) ;; H
    ((2) BLUE) ;; 1
    (else (raise-argument-error 'nat->color "small number" n))))

(define (data->framed-plot x)
  (add-border (data->exact-plot x)))

(define (make-scatterplots)
  (add-margin 4
    (parameterize ([OVERHEADS-WIDTH 650]
                   [OVERHEADS-HEIGHT 700]
                   [plot-decorations? #false]
                   [*POINT-ALPHA* 0.4]
                   [*AUTO-POINT-ALPHA?* #false]
                   [*OVERHEAD-LABEL?* #true]
                   [*OVERHEAD-FREEZE-BODY* #true]
                   [*EXACT-RUNTIME-BASELINE?* #true]
                   [*OVERHEAD-SHOW-RATIO* #false]
                   [*POINT-COLOR* 1]
                   [*LEGEND?* #false]
                   [*BRUSH-COLOR-CONVERTER* nat->color]
                   [*FONT-SIZE* 12]
                   [*GRID-NUM-COLUMNS* 3])
       (grid-plot data->framed-plot (cdr data*)))))

(define (add-margin m p)
  (define h (pict-height p))
  (define w (pict-width p))
  (cc-superimpose (blank (+ w m) (+ h m)) p))

(define (save-scatterplots filename)
  (save-pict filename (make-scatterplots)))

(module+ main
  (save-scatterplots cache-scatterplots.png))
