#lang at-exp slideshow

;; Slides for GRACE 2018
;;
;; Date: 2018-11-04 (sunday)
;; Time: 14:00 -- 14:20
;; Topic: ICFP + DLS talks ... mostly ICFP, switch to DLS
;; Abstract:
;;   The literature on gradual typing is filled with unscientific claims about
;;   different systems; in particular, about the guarantees of their types, their
;;   relative performance, and the degree to which they accommodate the needs of
;;   developers. This work attempts a scientific comparison on all three counts:
;;   soundness, performance, and developers’ preference.
;;
;;   The soundness and performance comparison is joint work with Matthias Felleisen.
;;   The preference comparison is joint work with Preston Tunnell Wilson, Justin
;;   Pombrio, and Shriram Krishnamurthi.
;;
;; Outline ... mostly performance? Boundaries, then performance. Maybe fish?

(require
  gf-icfp-2018/talk/src/gt-system
  gf-icfp-2018/talk/src/grace-util
  pict pict/convert pict/balloon pict/shadow
  pict-abbrevs
  ppict/2
  scribble-abbrevs/pict
  plot/no-gui
  racket/draw
  racket/list
  (only-in racket/string string-split)
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style)

(module+ test (require rackunit))

;; -----------------------------------------------------------------------------

(define ((add-bg-assembler default-assembler #:color color) s v-sep c)
  (define fg (default-assembler s v-sep c))
  (define bg
    (inset (filled-rectangle
             (+ (* 2 margin) client-w)
             (+ (* 2 margin) client-h)
             #:color color
             #:draw-border? #false) (- margin)))
  (cc-superimpose bg fg))

(module+ main
  (set-page-numbers-visible! #true)
  (set-spotlight-style! #:size 40 #:color (color%-update-alpha HIGHLIGHT-COLOR 0.6))
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size NORMAL-FONT-SIZE]
                 [current-slide-assembler (add-bg-assembler (current-slide-assembler)
                                                            #:color (color%-update-alpha (string->color% "Moccasin") 0.4))]
                 [current-titlet string->title])
    (void)
;    (sec:title)
    (sec:background)
;    (sec:gt-cost)
;    ;(sec:anecdotes)
;    (pslide (make-section-break "The Method"))
;    (sec:lattice)
;    (sec:exhaustive-method)
;    (pslide (make-section-break "A Method for Presenting the Data"))
;    (sec:dead-plot)
;    (pslide (make-section-break "Scaling the Method"))
;    (sec:scale)
;    (pslide (make-section-break "More in Paper"))
;    (sec:conclusion)
;    (sec:thanks)
;    (sec:title #:star? #true)
    (void)))

;; -----------------------------------------------------------------------------

(define (sec:title)
  (pslide
    #:go (coord SLIDE-LEFT 35/100 'lt)
    (parameterize ((current-main-font (list* 'bold 'italic TITLE-FONT))
                   (current-font-size TITLE-FONT-SIZE))
      @t{Three Approaches to Gradual Typing})
    #:go (coord SLIDE-RIGHT SLIDE-BOTTOM 'rb)
    (parameterize ((current-main-font ALL-CAPS-FONT)
                   (current-font-size SMALL-FONT-SIZE))
      @para{@bt{Ben Greenman},
            Justin Pombrio,
            Matthias Felleisen,
            Preston Tunnell Wilson,
            Shriram Krishnamurthi, and many others})
    #;#;#:go (coord 1/2 SLIDE-BOTTOM 'cc)
    #;(apply hb-append 40 all-logo*)
    )
  (void))

(define (sec:background)
  (parameterize ((current-para-width (w%->pixels 55/100)))
    (let ((dyn-desc
            (lines-append
              @subsubtitle-text{Dynamic Typing}
              @para{@bt{value}-level abstractions, enforced at run-time}))
          (sta-desc
            (lines-append
              @subsubtitle-text{Static Typing}
              @para{@bt{type}-level abstractions, checked before run-time}))
          (mixed-desc
            (lines-append
              @subsubtitle-text{Gradual Typing}
              @para{mix of static & dynamic typing ... somehow}))
          (h-width 4)
          (h-color HIGHLIGHT-COLOR))
    (pslide
     #:go CENTER-COORD
         (make-2table
         (list
           (list dyn-desc
                 (make-program-pict/dyn))
           (list sta-desc
                 (make-program-pict/sta))
           (list mixed-desc
                 (make-program-pict/mixed #:show-boundary? #true))))
     #:next
     #:alt [
     #:go (at-leftline dyn-desc)
     (make-leftline dyn-desc h-width #:color h-color) ]
     #:alt [
     #:go (at-leftline sta-desc)
     (make-leftline sta-desc h-width #:color h-color) ]
     #:go (at-leftline mixed-desc)
     (make-leftline mixed-desc h-width #:color h-color))))
  (pslide
    #:go HEADING-COORD
    (subsubtitle-text "Gradual Typing is growing ...")
    #:go (coord 1/10 20/100 'lt)
    (vl-append (h%->pixels 1/15)
               @para{Over 80 publications}
               @para{Over 20 implementations})
    #:next
    #:go (coord 1/2 1/2 'ct)
    (parameterize ((current-para-width (w%->pixels 60/100)))
      (alert-frame @para[#:align 'center]{But NO common definition of gradual typing --- due to@bt{different} goals and priorities}))
    #:next
    #:go (coord 1/2 SLIDE-BOTTOM 'cc)
    @para[#:align 'center]{Little acknowledgment (or analysis!) of the differences}
    )
  (void))

;; -----------------------------------------------------------------------------

(module+ raco-pict
  (provide raco-pict)
  (define p
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size NORMAL-FONT-SIZE])
    (let ((bb (blank client-w client-h)))
      (blank)


  )))
  (define (add-bg p)
    (cc-superimpose (blank (+ 100 (pict-width p)) (+ 100 (pict-height p))) (frame p)))
  (define raco-pict (add-bg p))
  (void))
