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
;    (sec:background)
    (sec:three)

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
    @para[#:align 'center]{Little acknowledgment (or analysis!) of the differences})
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "One kind of gradual typing:")
   #:go (coord 1/10 SLIDE-TOP 'lt)
   (hc-append (subtitle-text "Migratory Typing") @t{ (SNAPL'17)})
   #:go (coord 1/4 25/100 'lt)
   (parameterize ((current-para-width (w%->pixels 55/100)))
     (make-2table
       #:row-sep (h%->pixels 1/15)
       #:col-sep 10
       #:row-align lt-superimpose
       (list
         (list @t{1.} @para{Begin with an existing, dynamically-typed language})
         (list @t{2.} @para{Design an idiomatic type system})
         (list @t{3.} @para{Allow interaction between the two languages})))))
  (void))

(define (sec:three)
  (define-values [deep-system-pict shallow-system-pict erasure-system-pict] (make-DSE-system-pict*))
  (define-values [d-pict s-pict e-pict] (apply values (make-DSE-halo-pict*)))
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "a few Migratory Typing systems")
   #:go (coord SLIDE-LEFT 1/5 'lt)
   #:alt [(make-2table
     #:row-align lt-superimpose
            (list
              (list (pict->blank d-pict) deep-system-pict)
              (list (pict->blank s-pict) shallow-system-pict)
              (list (pict->blank e-pict) erasure-system-pict)))]
   (make-2table
     #:row-align lt-superimpose
     (list
       (list d-pict deep-system-pict)
       (list s-pict shallow-system-pict)
       (list e-pict erasure-system-pict))))
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "three approaches to Migratory Typing")
   #:go (coord SLIDE-LEFT 1/5 'lt)
   #:alt [(make-2table
     #:row-align lt-superimpose
            (list
              (list d-pict (pict->blank deep-system-pict))
              (list s-pict (pict->blank shallow-system-pict))
              (list e-pict (pict->blank erasure-system-pict))))]
   (make-2table
     #:col-sep 20
     #:row-align lt-superimpose
     (list
       (list d-pict (cl-superimpose (blank (pict-height d-pict) 0) (t (gt-strategy->kafka DEEP-TAG))))
       (list s-pict (cl-superimpose (blank (pict-height s-pict) 0) (t (gt-strategy->kafka SHALLOW-TAG))))
       (list e-pict (cl-superimpose (blank (pict-height e-pict) 0) (t (gt-strategy->kafka ERASURE-TAG))))))
   #:next
   #:go (coord 50/100 20/100 'lt)
   (parameterize ((current-para-width (w%->pixels 1/2))
                  (current-main-font SS-FONT))
     (vl-append 20
       (let-values (((a b c) (make-boundary-pict*)))
                   (scale a 0.8))
       @para{Three strategies for enforcing types at a boundary})))
  (void))

(define (sec:boundary)
  (define-values [sd sta-pict dyn-pict] (make-boundary-pict*))
  (let* ((validate-coord (coord 1/2 1/3 'cc))
         (sd/int (add-thought/sta sd sta-pict (need-txt "Integer"))) 
         (sd/int-0 (add-thought/dyn sd/int dyn-pict @t{42}))
         (sd/int-1 (add-thought/dyn sd/int dyn-pict @t{'NaN}))
         (sd/los (add-thought/sta sd sta-pict (need-txt "Listof(Symbol)")))
         (sd/los-0 (add-thought/dyn sd/los dyn-pict @t{'(A B 3 D)}))
         (sd/ii (add-thought/sta sd sta-pict (need-txt "Bool->Bool")))
         (sd/ii-0 (add-thought/dyn sd/ii dyn-pict @t{#<procedure>})))
    (pslide
      #:go HEADING-COORD
      (subtitle-text "Typed-Untyped Interaction")
      #:go (coord 1/2 1/2 'cb)
      #:alt [sd]
      #:alt [sd/int]
      #:alt [sd/int-0 #:next #:go validate-coord (large-check-icon)]
      #:alt [sd]
      #:alt [sd/int]
      #:alt [sd/int-1 #:next #:go validate-coord (large-x-icon)]
      #:alt [sd]
      #:alt [sd/los]
      #:alt [sd/los-0 #:next #:go validate-coord (large-x-icon)]
      #:alt [sd]
      #:alt [sd/ii]
      #:alt [sd/ii-0 #:next #:go validate-coord (make-monitor-icon "Bool?")]
      sd
      #:go (coord 1/2 3/5 'ct)
      @t{Type boundaries impose a run-time cost!}
      #:go (coord 1/2 SLIDE-BOTTOM 'ct)
      (vl-append 4
        @smallt{(Some mixed-typed languages do not enforce}
        @smallt{ types. For these languages, the performance}
        @smallt{ of type boundaries is not an issue.)})))
  (void))

;; -----------------------------------------------------------------------------

(define (make-DSE-system-pict*)
  (parameterize ((current-para-width (w%->pixels 65/100))
                 #;(current-line-sep 8))
    (values
      (gt*->pict #:direction 'H (filter/embedding 'H MT-system*))
      (gt*->pict #:direction 'H (filter/embedding '1 MT-system*))
      (gt*->pict #:direction 'H (filter/embedding 'E MT-system*)))))

;; -----------------------------------------------------------------------------

(module+ raco-pict
  (provide raco-pict)
  (define p
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size NORMAL-FONT-SIZE])
    (let ((bb (blank client-w client-h)))
      (blank)

   (;pslide
    ppict-do bb
    #:go (coord SLIDE-LEFT 1/5 'lt)
    (make-DSE-halo-pict)
    ;#:next
)

  )))
  (define (add-bg p)
    (cc-superimpose (blank (+ 100 (pict-width p)) (+ 100 (pict-height p))) (frame p)))
  (define raco-pict (add-bg p))
  (void))
