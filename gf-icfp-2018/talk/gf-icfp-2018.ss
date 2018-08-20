#lang at-exp slideshow

;; Slides for ICFP 2018

(require
  pict
  pict/convert
  ppict
  slideshow/code
  racket/draw racket/runtime-path
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style)

;; =============================================================================
;; --- constants

(define PAGENUM #true)
(define TITLESTR "A Spectrum of Type Soundness and Performance")

(define VALUE-HEIGHT 40)
(define VALUE-MATERIAL plastic-icon-material)
(define SCANNER-HEIGHT 160)
(define BELT-RATIO 1/4)
(define ARROW-RATIO 1/2)
(define FF-RATIO 7/8)
(define RAY-RATIO 1/5)

(define (string->color str)
  (or (send the-color-database find-color str)
      (raise-argument-error 'string->color "color-name?" str)))

(define BROWN (string->color "chocolate"))
(define GREEN (string->color "mediumseagreen"))
(define BLUE (string->color "cornflowerblue"))
(define DARK-BLUE syntax-icon-color)
(define RED (string->color "firebrick"))
(define RAY-COLOR RED)
(define BOX-COLOR (string->color "bisque"))
(define FF-COLOR DARK-BLUE)
(define BLACK (string->color "black"))
(define GREY (string->color "gray"))
(define DARK-GREY (string->color "DarkSlateGray"))

(define material* (list plastic-icon-material rubber-icon-material glass-icon-material metal-icon-material))

;; -----------------------------------------------------------------------------
;; --- outline

(define (do-show)
  (set-page-numbers-visible! PAGENUM)
  (parameterize ([current-main-font "Avenir"]
                 [current-font-size 32]
                 #;[current-titlet string->title]
                 #;[*current-tech* #true]
                )
    (sec:title)
    (sec:shape-preview)
    (sec:extra)
    (void)))

;; -----------------------------------------------------------------------------
;; --- helper functions

;; TODO try images/compile-time to embed

(define (make-bomb #:height [h VALUE-HEIGHT])
  (bitmap (bomb-icon #:height h #:material plastic-icon-material)))

(define (make-triangle #:height [h VALUE-HEIGHT] #:color [c GREEN] #:material [m VALUE-MATERIAL])
  (bitmap (regular-polygon-icon 3 #:color c #:height h #:material m)))

(define (make-dyn #:height [h VALUE-HEIGHT] #:color [c BROWN])
  (define q-mark (bitmap (text-icon "?" #:height (- h 2) #:color BLACK)))
  q-mark
  #;(cc-superimpose
    (bitmap (make-circle #:height h #:color c))
    q-mark))

(define (make-stuck #:height [h VALUE-HEIGHT])
  (bitmap (stop-sign-icon #:height h #:material VALUE-MATERIAL)))

(define (make-circle #:height [h VALUE-HEIGHT] #:color [c RED] #:material [m VALUE-MATERIAL])
  (bitmap (record-icon #:color c #:height h #:material m)))

(define (make-arrow #:left? [left? #false] #:height [h VALUE-HEIGHT] #:color [c syntax-icon-color])
  (bitmap ((if left? left-arrow-icon right-arrow-icon) #:color c #:height h)))

(define (make-ff #:height [h VALUE-HEIGHT] #:color [c FF-COLOR] #:left? [left? #false])
  (bitmap ((if left? rewind-icon fast-forward-icon) #:color c #:height h)))

(define (make-belt #:height h #:width w #:left? [left? #false] #:radius [r 0] #:angle [a 0])
  (define inner-color GREY)
  (define belt-color DARK-GREY)
  (define belt-width (/ w 50))
  (define ff-height (* FF-RATIO h))
  (define ff (make-ff #:left? left? #:height ff-height))
  (define bar (filled-rounded-rectangle w h #:color inner-color #:border-color belt-color #:border-width belt-width))
  (define end (disk h #:draw-border? #true #:color inner-color #:border-color belt-color #:border-width belt-width))
  ;; TODO use end
  (rc-superimpose (lc-superimpose bar ff) ff))

(define (make-box #:height h #:width w #:color [c BOX-COLOR])
  (define bw (/ h 20))
  (filled-rectangle w h #:color c #:draw-border? #true #:border-color BLACK #:border-width bw))

(define (make-function dom-pict cod-pict #:left? [left? #false] #:height [pre-h #false])
  (define total-height
    (or pre-h
        (let ([dom-h (pict-height dom-pict)]
              [cod-h (pict-height cod-pict)])
          (* 2 (max dom-h cod-h)))))
  (define belt-height (* total-height BELT-RATIO))
  (define box-height (* total-height (- 1 BELT-RATIO)))
  (define arrow-pict (make-arrow #:left? left? #:height (* ARROW-RATIO box-height)))
  (define box-width
    (let ([dom-w (pict-width dom-pict)]
          [cod-w (pict-width cod-pict)]
          [arr-w (pict-width arrow-pict)])
      (* 1.5 (+ dom-w cod-w arr-w))))
  (define belt-width
    (* 1.8 box-width))
  (define belt-pict (make-belt #:left? left? #:height belt-height #:width belt-width))
  (define box-pict (make-box #:height box-height #:width box-width))
  (vc-append
    (cc-superimpose
      box-pict
      (let ([box-sep (/ box-width 20)])
        (if left?
          (hc-append box-sep cod-pict arrow-pict dom-pict)
          (hc-append box-sep dom-pict arrow-pict cod-pict))))
    belt-pict))

(define (make-scanner lbl-pict #:height [h SCANNER-HEIGHT] #:alarm? [alarm? #false])
  (define head-h
    (* 1.1 (pict-height lbl-pict)))
  (define head-pict
    (cc-superimpose (make-scanner-head #:height head-h)
                    (vc-append (blank 0 4) lbl-pict)))
  (define ray-pict
    (make-scanner-ray #:height (max 10 (- h head-h))))
  (define s-pict
    (vc-append head-pict ray-pict))
  (if alarm?
    (vc-append 4 (make-scanner-alarm #:height VALUE-HEIGHT) s-pict)
    s-pict))

(define (make-scanner-alarm #:height h)
  #;(text "!" '(bold) 20)
  (bitmap (text-icon "!" #:height h #:color BLACK)))

(define (make-scanner-head #:height h)
  (define bw (/ h 40))
  (filled-rounded-rectangle h h #:color GREY #:draw-border? #true #:border-color BLACK #:border-width bw))

(define (make-scanner-ray #:height h)
  (define w (* RAY-RATIO VALUE-HEIGHT))
  (define seg-length (* w 2))
  (vline* w h seg-length #:color RAY-COLOR)
  #;(let ([w h])
    (dc ray-dc-proc w h)))

(define (vline* w total-h h #:color [c BLACK])
  (define h-sep (* h 1/5))
  (define (make-segment w h)
    (filled-rectangle w h #:color c #:draw-border? #false))
  (define (make-space h)
    (blank 0 h))
  (let loop ([acc (make-space 0)]
             [rem-h total-h])
    (cond
      [(<= rem-h 0)
       acc]
      [(<= rem-h h)
       (vc-append acc (make-segment w rem-h))]
      [(<= rem-h (+ h h-sep))
       (vc-append acc (make-segment w h) (make-space (- rem-h h-sep)))]
      [else
        (loop (vc-append acc (make-segment w h) (make-space h-sep)) (- rem-h h h-sep))])))

(define (ray-dc-proc dc dx dy)
  (define old-brush (send dc get-brush))
  (define old-pen (send dc get-pen))
  (send dc set-brush
    (new brush% [style 'fdiagonal-hatch]
                [color RAY-COLOR]))
  (send dc set-pen
    (new pen% [width 3] [color RAY-COLOR]))
  (define path (new dc-path%))
  (send path move-to 20 0)
  (send path line-to 40 0)
  (send path line-to 45 50)
  (send path line-to 15 50)
  (send path close)
  (send dc draw-path path dx dy)
  (send dc set-brush old-brush)
  (send dc set-pen old-pen))

;; -----------------------------------------------------------------------------
;; --- slide functions

(define (sec:title)
  (slide
    ;; TODO racket-logo title slide
    @text[TITLESTR (current-main-font) (+ (current-font-size) 20)]
    @t{Ben Greenman & Matthias Felleisen}
    @t{PLT @"@" Northeastern University}
    @comment{
      yolo
    })
  (void))

(define (sec:shape-preview)
  (slide
    (hc-append
      20
      (make-function (make-stuck) (make-dyn) #:left? #true)
      (make-function (make-triangle) (make-dyn) #:left? #true)
      (make-function (make-bomb) (make-circle)))
    ;; TODO small function
    ;; TODO add scanner to function
    ;; TODO add stuck to function
    (make-scanner (make-triangle) #:alarm? #true)
    (make-scanner (make-triangle))
    )
  (void))

(define (sec:extra)
  (void))


;; =============================================================================

(module+ main
  (do-show))
