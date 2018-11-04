#lang racket/base

(require racket/contract)
(provide
  (contract-out
    [speech-bubble
      (->* [pict?] [#:direction (or/c 'left 'right)
                    #:radius (or/c #f real?)] pict?)]))

(require
  pict
  racket/class
  racket/draw
  "two-tone.rkt")

;; =============================================================================

(define (speech-bubble #:direction [direction 'left]
                       #:radius [pre-radius #f]
                       str-pict)
  (define corner-radius (or pre-radius -0.25))
  (define str-w (pict-width str-pict))
  (define str-h (pict-height str-pict))
  (define balloon-w (+ str-w 70))
  (define balloon-h (+ str-h 40))
  (define balloon-body-color "white")
  (define balloon-line-color "black")
  (define balloon-line-width 8)
  (define balloon-tail-param 8)
  (define balloon-pict
    (cc-superimpose
      (rounded-rectangle/2t balloon-w balloon-h
                            #:radius corner-radius
                            #:color-1 "whitesmoke"
                            #:color-2 balloon-body-color
                            #:border-color balloon-line-color #:border-width balloon-line-width)
      str-pict))
  (define triangle-pict
    (let* ([triangle-width 30]
           [triangle-height 50]
           [draw-fun (lambda (dc dx dy)
                       (define old-brush (send dc get-brush))
                       (define old-pen (send dc get-pen))
                       (send dc set-brush (new brush% [style 'solid] [color balloon-body-color]))
                       (let ((path (new dc-path%)))
                         (send dc set-pen (new pen% [width balloon-line-width] [color balloon-body-color]))
                         (send path move-to 0 0)
                         (send path line-to triangle-width 0)
                         (send dc draw-path path dx dy))
                       (let ((path (new dc-path%)))
                         (send dc set-pen (new pen% [width balloon-line-width] [color balloon-line-color]))
                         (send path move-to 0 0)
                         (send path line-to (/ triangle-width 2) triangle-height)
                         (send path line-to triangle-width 0)
                         (send dc draw-path path dx dy))
                       (send dc set-brush old-brush)
                       (send dc set-pen old-pen))])
    (dc draw-fun triangle-width triangle-height)))
  (define tag-v (- 1))
  (define tag-h (/ balloon-w 10))
  (case direction
    ((left)
     (vl-append tag-v balloon-pict (hc-append tag-h (blank) triangle-pict)))
    ((right)
     (vr-append tag-v balloon-pict (hc-append tag-h triangle-pict (blank))))
    (else
      (raise-argument-error 'speech-bubble "direction?" 1 str-pict direction))))
