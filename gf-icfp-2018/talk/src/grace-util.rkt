#lang racket/base

(provide (all-defined-out))

(require
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  racket/format
  (only-in scribble-abbrevs add-commas)
  racket/math
  (only-in gtp-util natural->bitstring)
  racket/class
  racket/draw
  racket/match
  racket/list
  racket/runtime-path
  gf-icfp-2018/talk/src/two-tone
  gf-icfp-2018/talk/src/gt-system
  gf-icfp-2018/talk/src/speech-bubble
  pict
  pict/balloon pict/shadow
  (only-in pict-abbrevs string->color% color%-update-alpha revolution rule pict-bbox-sup pict-bbox-sup*)
  ppict/2
  (except-in plot/utils min* max*)
  plot/no-gui
  (only-in racket/string string-replace)
  (only-in plot/utils ->pen-color)
  (only-in slideshow bt current-font-size current-main-font margin client-w client-h t para))

(module+ test (require rackunit))

;; make-X-component
;; make-X-program
;; make-comment-bubble
;; title-font
;; desc-font
;; comment-font
;; add-halo

;;   behavioral transient optional

;; -----------------------------------------------------------------------------

;; TODO tweak colors

(define QUESTION-COLOR (string->color% "CadetBlue"))
(define ANSWER-COLOR (string->color% "LemonChiffon" #;"Khaki"))
(define HIGHLIGHT-COLOR (string->color% "RoyalBlue"))
(define HIGHLIGHT-BRUSH-COLOR (color%-update-alpha HIGHLIGHT-COLOR 0.3))
(define WHITE (string->color% "white"))
(define BLACK (string->color% "black"))
(define GREY (string->color% "gray"))
(define GRAY GREY)
(define DYN-COLOR (string->color% "Firebrick"))
(define DYN-TEXT-COLOR (string->color% light-metal-icon-color))
(define STAT-COLOR (string->color% "PaleTurquoise"))
(define TAU-COLOR "DarkGoldenrod")
;(define DEEP-COLOR (string->color% "DarkMagenta"))
;(define SHALLOW-COLOR (string->color% "MediumSeaGreen"))
;(define ERASURE-COLOR (string->color% "DarkOrange"))
(define DEEP-COLOR (string->color% "Tomato"))
(define SHALLOW-COLOR (string->color% "cornflowerblue"))
(define ERASURE-COLOR (string->color% "mediumseagreen"))

(define TYPE-BOUNDARY-COLOR (string->color% "Fuchsia"))
(define LABEL-COLOR (string->color% "Plum"))
(define SURVEY-COLOR (string->color% "Gainsboro"))
(define BLANK-COLOR (string->color% "LightGoldenrodYellow"))
(define LIGHT-RED (string->color% "Tomato"))
(define GREEN (string->color% "mediumseagreen"))
(define BLUE (string->color% "cornflowerblue"))

(define DEEP-TAG 'deep)
(define SHALLOW-TAG 'shallow)
(define ERASURE-TAG 'erasure)

(define PLOT-FN-ALPHA 0.6)
(define PLOT-RATIO 3/4) ;; TODO nonsense

(define GT-TAG* (list DEEP-TAG SHALLOW-TAG ERASURE-TAG))

(define DEEP-STR "Deep")
(define SHALLOW-STR "Shallow")
(define ERASURE-STR "Erasure")

(define (gt-strategy-text str color tag [size SUBSUBTITLE-FONT-SIZE])
  (define txt
    (parameterize ((current-main-font MONO-FONT)
                   (current-font-size size))
      (text/bgcolor str color)))
  (tag-pict txt tag))

(define (string->title str #:size [size TITLE-FONT-SIZE] #:color [color BLACK])
  (colorize (text str TITLE-FONT size) color))

(define ALL-CAPS-FONT "Triplicate C3" #;"Bebas Neue")
(define MONO-FONT "Triplicate T4")
(define TITLE-FONT "Triplicate C4")
(define SS-FONT "Fira Sans")

(define NORMAL-FONT-SIZE 32)
(define SMALL-FONT-SIZE 28)
(define FOOTNOTE-FONT-SIZE 22)
(define TITLE-FONT-SIZE 44)
(define SUBTITLE-FONT-SIZE 40)
(define SUBSUBTITLE-FONT-SIZE 34)

(define SLIDE-TOP 1/10)
(define SLIDE-LEFT 1/50)
(define SLIDE-BOTTOM 4/5)
(define SLIDE-RIGHT (- 1 SLIDE-LEFT))
(define BODY-TOP 15/100)

(define HEADING-COORD (coord SLIDE-LEFT SLIDE-TOP 'lb))
(define -HEADING-COORD (coord SLIDE-RIGHT SLIDE-TOP 'rb))
(define CENTER-COORD (coord 1/2 1/2 'cc))
(define QUESTION-COORD (coord 98/100 1/2 'rc)) 
(define NOTATION-COORD (coord 1/2 1/4 'ct))
(define MT-SYSTEM-COORD (coord 1/5 1/5 'lt))
(define MAIN-CONTRIB-COORD (coord 1/5 1/5 'lt))
(define -MAIN-CONTRIB-COORD (coord 4/5 4/5 'rt))

(define SMALL-ROUND -0.08)
(define SUBTITLE-MARGIN 20)
(define SUBSUBTITLE-MARGIN 10)
(define COMPONENT-MARGIN 40)
(define COMPONENT-LATTICE-MARGIN 6)
(define LINE-MARGIN 4)
(define INDENT-MARGIN 30)
(define COLUMN-MARGIN 70)
(define LATTICE-NODE-X-MARGIN 20)
(define LATTICE-NODE-Y-MARGIN 40)

(define BALLOON-RADIUS 10)

(define COMPONENT-ARROW-SIZE 11)
(define COMPONENT-ARROW-WIDTH 3)
(define TYPE-BOUNDARY-ARROW-SIZE 13)
(define TYPE-BOUNDARY-ARROW-WIDTH 4)
(define TYPE-BOUNDARY-TAG 'the-type-boundary)
(define MIGRATION-ARROW-SIZE 25)
(define MIGRATION-ARROW-WIDTH 8)

(define-runtime-path racket-logo.png "racket-logo.png")
(define-runtime-path cache-scatterplots.png "cache-scatterplots.png")

(define STA-TAG 'sta-component)
(define DYN-TAG 'dyn-component)

(define (right-arrow [size 30] #:color [c #f])
  (my-arrow size 0 c))

(define (up-arrow [size 30] #:color [c #f])
  (my-arrow size (* 1/4 revolution) c))

(define (left-arrow [size 30] #:color [c #f])
  (my-arrow size (* 1/2 revolution) c))

(define (down-arrow [size 30] #:color [c #f])
  (my-arrow size (* 3/4 revolution) c))

(define (my-arrow size angle color)
  (maybe-colorize (arrow size angle) color))

(define (maybe-colorize p c)
  (if c (colorize p c) p))

(define (-pct num-yes num-no)
  (round (* 100 (/ num-yes (+ num-yes num-no)))))

(define (pixels->w% x)
  (/ x (+ (* 2 margin) client-w)))

(define (pixels->h% x)
  (/ x (+ (* 2 margin) client-h)))

(define (w%->pixels pct)
  (* pct client-w))

(define (h%->pixels pct)
  (* pct client-h))

(define (erase-pict p [alpha 0.2])
  (cellophane p alpha))

(define (snoc x* x)
  (let loop ((x* x*))
    (if (null? x*) (list x) (cons (car x*) (loop (cdr x*))))))

(module+ test
  (test-case "snoc"
    (check-equal? (snoc '() 'x) '(x))
    (check-equal? (snoc '(A B) 'C) '(A B C))))

(define (string->tag str)
  (string->symbol (string-downcase (string-replace str " " "-"))))

(module+ test
  (test-case "string->tag"
    (check-equal? (string->tag "hello") 'hello)
    (check-equal? (string->tag "hello world") 'hello-world)
    (check-equal? (string->tag "What hits?") 'what-hits?)))

(define (lines-append . arg*)
  (lines-append* arg*))

(define (lines-append* arg*)
  (apply vl-append (* 1/2 (current-font-size)) arg*))

(define (columns-append . arg*)
  (columns-append* arg*))

(define (columns-append* arg*)
  (apply ht-append (* 11/6 (current-font-size)) arg*))

(define (text/color str c)
  (text str (cons c (current-main-font)) (current-font-size)))

(define (dynt str)
  (text/color str DYN-TEXT-COLOR))

(define BG-ALPHA 0.6)

(define (text/bgcolor str c)
  (define the-margin 4)
  (define the-radius 15)
  (define tt (text str (current-main-font) (current-font-size)))
  (define bg (filled-rounded-rectangle (+ (* 2 the-margin) (pict-width tt))
                                       (+ the-margin (pict-height tt))
                                       the-radius
                                       #:color (color%-update-alpha c BG-ALPHA)
                                       #:draw-border? #false))
  (cc-superimpose bg tt))

(define (deept str)
  (text/bgcolor str DEEP-COLOR))

(define (shallowt str)
  (text/bgcolor str SHALLOW-COLOR))

(define (erasuret str)
  (text/bgcolor str ERASURE-COLOR))

(define (ss-text str)
  (text str SS-FONT (current-font-size)))

(define (large-check-icon)
  (make-icon check-icon #:height 80))

(define (small-check-icon)
  (make-icon check-icon #:height 30))

(define (make-monitor-icon str)
  (define the-color "DarkOrange")
  (define h 50)
  (hc-append -2
    (large-text-icon "(" #:color the-color #:height h)
    (bt str)
    (cc-superimpose
      (blank 28 0)
      (large-text-icon "∘" #:color the-color #:height 22))
    (rule 40 5 #:color BLACK)
    (large-text-icon ")" #:color the-color #:height h)))

(define (large-text-icon str #:color c #:height h)
  (make-icon (my-text-icon str #:color c) #:height h))

(define (large-?-icon)
  (large-text-icon "?"))

(define (large-~-icon)
  (make-icon (my-text-icon "~" #:color "dimgray") #:height 20))

(define ((my-text-icon str #:color c) #:material m #:height h)
  (text-icon str #:color c #:height h #:material m))

(define (large-x-icon)
  (make-icon x-icon #:height 80))

(define (small-x-icon)
  (make-icon x-icon #:height 30))

(define (small-tau-icon)
  (make-icon tau-icon #:height 40))

(define (large-tau-icon)
  (make-icon tau-icon #:height 90))

(define tau-font
  (make-font #:smoothing 'unsmoothed #:family 'roman #:weight 'semibold))

(define (tau-icon #:color [c TAU-COLOR] #:height [h (default-icon-height)] #:material [m (default-icon-material)])
  (text-icon "τ" tau-font #:color c #:height h #:material m))

(define (small-lambda-icon)
  (make-icon lambda-icon #:height 40))

(define (large-lambda-icon)
  (make-icon lambda-icon #:height 90))

(define (make-large-focus-icon)
  (make-icon magnifying-glass-icon #:height 90))

(define (make-small-focus-icon)
  (make-icon magnifying-glass-icon #:height 50))

(define (make-icon i #:height h)
  (bitmap (i #:material plastic-icon-material #:height h)))

(define (title-text str [pre-size #f])
  (define size (or pre-size TITLE-FONT-SIZE))
  (text str TITLE-FONT size))

(define (subtitle-text str)
  (title-text str SUBTITLE-FONT-SIZE))

(define (subsubtitle-text str)
  (title-text str SUBSUBTITLE-FONT-SIZE))

(define (caps-text str)
  (text str ALL-CAPS-FONT (+ 2 (current-font-size))))

(define (scale-q p)
  (scale-to-fit p (* 4/5 client-w) (* 4/5 client-h)))

(define (bigger-program p)
  (scale p 3/2))

(define (scale-logo p)
  (scale-to-fit p 180 80))

(define (add-tax v pct)
  (+ v (* v pct)))

(define (add-rectangle-background p
                                  #:radius [the-radius 10]
                                  #:color [color WHITE]
                                  #:draw-border? [draw-border? #false]
                                  #:x-margin [x-margin 0]
                                  #:y-margin [y-margin 0])
  (define-values [w h] (values (pict-width p) (pict-height p)))
  (define bg
    (filled-rounded-rectangle (add-tax w x-margin) (add-tax h y-margin) the-radius
                              #:color color
                              #:draw-border? draw-border?))
  (cc-superimpose bg p))

(define (add-rounded-border pp)
  (define-values [w h] (values (pict-width pp) (pict-height pp)))
  (define the-radius 10)
  (define frame
    (rounded-rectangle w h the-radius #:border-width 1 #:border-color BLACK))
  (define pp/bg
    (add-rectangle-background pp
                              #:color WHITE
                              #:draw-border? #false
                              #:radius the-radius))
  (cc-superimpose pp/bg frame))

(define neu-logo (bitmap "src/neu-seal.png"))
(define nwu-logo (bitmap "src/nwu-logo.png"))
(define ctu-logo (bitmap "src/ctu-logo.png"))
(define igalia-logo (add-rectangle-background (bitmap "src/igalia-logo.png") #:x-margin 1/10 #:y-margin 1/10))

(define all-logo* (pict-bbox-sup* (map scale-logo (list neu-logo))))
; igalia-logo nwu-logo ctu-logo

(define (round-frame fg #:title [title #false] #:align [align 'left])
  (add-rounded-frame fg
                     #:title title
                     #:align align
                     #:page-margin 30
                     #:fg-color WHITE
                     #:bg-color "plum"))

(define (add-rounded-frame fg
                           #:title [title #false]
                           #:align [align 'left]
                           #:fg-color [fg-color WHITE]
                           #:bg-color [bg-color BLACK]
                           #:radius [the-radius 8]
                           #:border-margin [pre-border-margin #f]
                           #:page-margin [pre-page-margin #f])
  (define the-border-margin (or pre-border-margin 20))
  (define the-page-margin (or pre-page-margin (* 2 the-border-margin)))
  (define mg
    (filled-rounded-rectangle (+ the-page-margin (pict-width fg))
                              (+ the-page-margin (pict-height fg))
                              the-radius
                              #:color fg-color
                              #:draw-border? #true
                              #:border-width 1
                              #:border-color BLACK))
  (define bg
    (filled-rounded-rectangle (+ the-border-margin (pict-width mg))
                              (+ the-border-margin (pict-height mg))
                              the-radius
                              #:color bg-color
                              #:draw-border? #true
                              #:border-width 1
                              #:border-color BLACK))
  (define main-pict (cc-superimpose bg mg fg))
  (if title
    ((y-align->combiner align) SUBSUBTITLE-MARGIN title main-pict)
    main-pict))

(define (y-align->combiner k)
  (case k
    ((left) vl-append)
    ((center) vc-append)
    ((right) vr-append)
    (else (raise-argument-error 'y-align->combiner "(or/c 'left 'center 'right)" k))))

(define deep-pict
  (gt-strategy-text DEEP-STR DEEP-COLOR DEEP-TAG))

(define shallow-pict
  (gt-strategy-text SHALLOW-STR SHALLOW-COLOR SHALLOW-TAG))

(define erasure-pict
  (gt-strategy-text ERASURE-STR ERASURE-COLOR ERASURE-TAG))

(define (gt-strategy-tag? x)
  (and (symbol? x) (memq x (list DEEP-TAG SHALLOW-TAG ERASURE-TAG))))

(define (gt-strategy->kafka-text x)
  (define kt (gt-strategy->kafka x))
  (t (string-append "(" kt ")")))

(define (gt-strategy->kafka x)
  (cond
    [(eq? x DEEP-TAG)    "behavioral"]
    [(eq? x SHALLOW-TAG) "transient"]
    [(eq? x ERASURE-TAG) "optional"]
    [else (raise-argument-error 'gt-strategy->kafka "gt-strategy-tag?" x)]))

(define (gt-strategy->t x)
  (cond
    [(eq? x DEEP-TAG)    deept]
    [(eq? x SHALLOW-TAG) shallowt]
    [(eq? x ERASURE-TAG) erasuret]
    [else (raise-argument-error 'gt-strategy->t "gt-strategy-tag?" x)]))

(define (gt-strategy->letter x)
  (cond
    [(eq? x DEEP-TAG)    "D"]
    [(eq? x SHALLOW-TAG) "S"]
    [(eq? x ERASURE-TAG) "E"]
    [else (raise-argument-error 'gt-strategy->letter "gt-strategy-tag?" x)]))

(define (gt-strategy->pict x)
  (cond
    [(eq? x DEEP-TAG) deep-pict]
    [(eq? x SHALLOW-TAG) shallow-pict]
    [(eq? x ERASURE-TAG) erasure-pict]
    [else (raise-argument-error 'gt-strategy->pict "gt-strategy-tag?" x)]))

(define (gt-strategy->color x)
  (cond
    [(eq? x DEEP-TAG) DEEP-COLOR]
    [(eq? x SHALLOW-TAG) SHALLOW-COLOR]
    [(eq? x ERASURE-TAG) ERASURE-COLOR]
    [else (raise-argument-error 'gt-strategy->color "gt-strategy-tag?" x)]))

(define (gt-strategy->str x)
  (cond
    [(eq? x DEEP-TAG) DEEP-STR]
    [(eq? x SHALLOW-TAG) SHALLOW-STR]
    [(eq? x ERASURE-TAG) ERASURE-STR]
    [else (raise-argument-error 'gt-strategy->str "gt-strategy-tag?" x)]))

(define (make-2table kv**
                     #:col-sep [pre-col-sep #f]
                     #:row-sep [pre-row-sep #f]
                     #:col-align [col-align lc-superimpose]
                     #:row-align [row-align cc-superimpose])
  (define col-sep (or pre-col-sep (w%->pixels 1/15)))
  (define row-sep (or pre-row-sep (h%->pixels 1/10)))
  (table 2 (flatten kv**) col-align row-align col-sep row-sep))

(define (make-program-pict/sta)
  (add-program-edges (list->component* '(#t #t #t))))

(define (make-program-pict/dyn)
  (add-program-edges (list->component* '(#f #f #f))))

(define (make-program-pict/mixed #:show-boundary? [show-boundary? #false])
  (add-program-edges (list->component* '(#t #f #f))
                     #:show-boundary? show-boundary?))

(define (list->component* bool*)
  (define-values [sta-body-pict dyn-body-pict]
    (apply values (pict-bbox-sup (small-tau-icon) (small-lambda-icon))))
  (for/list ((b (in-list bool*)))
    (if b
      (tag-pict (make-component-pict/sta #:body sta-body-pict) STA-TAG)
      (tag-pict (make-component-pict/dyn #:body dyn-body-pict) DYN-TAG))))

(define (add-program-edges c* #:show-boundary? [show-boundary? #false])
  (match c*
    [(list c0 c1 c2)
     (define the-pict (apply hb-append COMPONENT-MARGIN c*))
     (for/fold ((acc the-pict))
               ((edge-spec (in-list `(((,c0 ,rt-find) (,c2 ,lt-find)  50)
                                      ((,c1 ,rc-find) (,c2 ,lc-find)   0)))))
       (define dom-spec (car edge-spec))
       (define cod-spec (second edge-spec))
       (define dom-pict (car dom-spec))
       (define cod-pict (car cod-spec))
       (define boundary-color
         (if (and show-boundary? (not (eq? (pict-tag dom-pict) (pict-tag cod-pict))))
           TYPE-BOUNDARY-COLOR
           BLACK))
       (pin-arrows-line COMPONENT-ARROW-SIZE
                        acc
                        dom-pict (second dom-spec)
                        cod-pict (second cod-spec)
                        #:start-angle (- (caddr edge-spec))
                        #:end-angle (caddr edge-spec)
                        #:line-width COMPONENT-ARROW-WIDTH
                        #:color boundary-color))]
    [_
      (raise-argument-error 'add-program-edges "(list pict? pict? pict?)" c*)]))

(define (make-boundary-pict #:l [pre-l-body-pict #f]
                            #:c [pre-c-body-pict #f]
                            #:r [pre-r-body-pict #f])
  (define-values [l-body-pict r-body-pict _spacer]
    (apply values (pict-bbox-sup (or pre-l-body-pict (blank))
                                 (or pre-r-body-pict (blank))
                                 (blank 90 90))))
  (define c-body-pict (or pre-c-body-pict (blank)))
  (define l-pict (make-component-pict/dyn #:body l-body-pict))
  (define r-pict (make-component-pict/sta #:body r-body-pict))
  (define arrow-margin 2)
  (add-labeled-arrow #:direction 'right
                     #:label (vc-append arrow-margin c-body-pict (blank))
                     #:x-sep (/ client-w 4)
                     (hb-append arrow-margin l-pict (blank))
                     (hb-append arrow-margin (blank) r-pict)))

(define (add-labeled-arrow l-pict
                           r-pict
                           #:x-sep [pre-x-sep #f]
                           #:direction [dir 'right]
                           #:label [pre-lbl #f])
  (define x-sep (or pre-x-sep (/ client-w 4)))
  (define bg (hc-append x-sep l-pict r-pict))
  (define lbl-pict (or pre-lbl (blank)))
  (define-values [dom-pict dom-find cod-pict cod-find]
    (case dir
      ((left)
       (values r-pict lc-find l-pict rc-find))
      ((right)
       (values l-pict rc-find r-pict lc-find))
      (else
        (raise-argument-error 'add-labeled-arrow "direction?" dir))))
  (pin-arrow-line TYPE-BOUNDARY-ARROW-SIZE
                  bg
                  dom-pict dom-find
                  cod-pict cod-find
                  #:label lbl-pict
                  #:color TYPE-BOUNDARY-COLOR
                  #:line-width TYPE-BOUNDARY-ARROW-WIDTH))

(define (make-DSE-halo-pict)
  (apply vc-append 90 (make-DSE-halo-pict*)))

(define (make-DSE-halo-pict*)
  (let* ((p* (pict-bbox-sup deep-pict shallow-pict erasure-pict)))
    (map gt-strategy->halo p* GT-TAG*)))

(define (gt-strategy->halo p p-tag)
  (define c (gt-strategy->color p-tag))
  (tag-pict (add-halo p c) p-tag))

(define (add-halo p c)
  (define blur-val 15)
  (define e-margin 40)
  (define laddye
      (filled-ellipse (+ e-margin (pict-width p))
                   (+ e-margin (pict-height p))
                   #:color c
                   #:draw-border? #false))
  (define ladye
      (ellipse (+ e-margin (pict-width p))
                   (+ e-margin (pict-height p))
                   #:border-color c
                   #:border-width 10))
  (define halo
    (blur ladye blur-val blur-val))
  (cc-superimpose halo laddye p))

(define (wide-rectangle height
                        #:border-width [border-width 1]
                        #:border-color [border-color BLACK]
                        #:color-1 [color-1 WHITE]
                        #:color-2 [color-2 WHITE])
  (inset
    (rectangle/2t (+ (* margin 2) client-w) height
                  #:border-width border-width
                  #:border-color border-color
                  #:color-1 color-1
                  #:color-2 color-2)
    (- margin)))

(define (comment-frame pp)
  (add-rounded-frame pp
                     #:title #false
                     #:align 'left
                     #:fg-color "Azure"
                     #:bg-color BLACK
                     #:radius 14
                     #:border-margin 1
                     #:page-margin 28))

(define (alert-frame pp)
  (add-rounded-frame pp
                     #:title #false
                     #:align 'center
                     #:fg-color WHITE
                     #:bg-color "Crimson"
                     #:radius 14
                     #:border-margin 12
                     #:page-margin 28))

(define (make-component-pict/sta #:body [body (blank)]
                                 #:width [pre-width #f]
                                 #:height [pre-height #f])
  (make-component-pict/tu #:body body
                          #:width pre-width
                          #:height pre-height
                          #:color STAT-COLOR))

(define (make-component-pict/dyn #:body [body (blank)]
                                 #:width [pre-width #f]
                                 #:height [pre-height #f])
  (make-component-pict/tu #:body body
                          #:width pre-width
                          #:height pre-height
                          #:color DYN-COLOR))

(define (make-component-pict/blank #:body [body-blank #f]
                                   #:width [pre-width #f]
                                   #:height [pre-height #f])
  (make-component-pict/tu #:body (or body-blank (blank))
                          #:width pre-width
                          #:height pre-height
                          #:color BLANK-COLOR))

(define (make-component-pict/tu #:body body 
                                #:width w
                                #:height h
                                #:color c)
  (make-component-pict #:body body
                       #:width w
                       #:height h
                       #:color c
                       #:border-width 2
                       #:border-color "black"))

(define (make-component-pict #:body [body (blank)]
                             #:width [pre-width #f]
                             #:height [pre-height #f]
                             #:color [color WHITE]
                             #:border-width [border-width 4]
                             #:border-color [border-color "black"])
  (define m/2 (/ margin 2))
  (define w (or pre-width (+ m/2 (pict-width body))))
  (define h (or pre-height (+ m/2 (pict-height body))))
  (define bg
    (if border-width
      (filled-rounded-rectangle
        w h SMALL-ROUND
        #:draw-border? #true
        #:color color
        #:border-color border-color
        #:border-width border-width)
      (filled-rounded-rectangle w h SMALL-ROUND #:color color #:draw-border? #false)))
  (cc-superimpose bg body))

(define (at-underline pp #:abs-y [abs-y LINE-MARGIN])
  (at-find-pict pp lb-find 'lt #:abs-y abs-y))

(define (make-underline pp [height LINE-MARGIN] #:color [color HIGHLIGHT-COLOR] #:width [width #f])
  (rule (or width (pict-width pp)) height #:color color))

(define (at-leftline pp #:abs-y [abs-y 0] #:abs-x [abs-x -10])
  (at-find-pict pp lt-find 'lt #:abs-y abs-y #:abs-x abs-x))

(define (make-leftline pp [width LINE-MARGIN] #:color [color HIGHLIGHT-COLOR])
  (rule width (pict-height pp) #:color color))

(define (at-highlight pp #:abs-x [abs-x 0] #:abs-y [abs-y -2])
  (at-find-pict pp lt-find 'lt #:abs-x abs-x #:abs-y abs-y))

(define (make-highlight pp #:color [color HIGHLIGHT-BRUSH-COLOR])
  (define-values [w h]
    (if (pict? pp)
      (values (pict-width pp) (pict-height pp))
      (values (car pp) (cdr pp))))
  (rule w h #:color color))

(define (make-highlight* pp tag)
  (for/fold ((acc pp))
            ((tgt (in-list (find-tag* pp tag))))
    (ppict-do acc #:go (at-highlight tgt) (make-highlight (pict-path->wh pp tgt)))))

(define (pict-path->wh pp tgt)
  (define-values [x-lo y-lo] (lt-find pp tgt))
  (define-values [x-hi y-hi] (rb-find pp tgt))
  (cons (- x-hi x-lo) (- y-hi y-lo)))

(define (make-boundary-pict*)
  (let* ((sd* (list->component* '(#true #false)))
         (sta-pict (car sd*))
         (dyn-pict (cadr sd*))
         (acc (apply hb-append (* 2 COLUMN-MARGIN) sd*))
         (edge-spec `((,sta-pict ,rc-find) (,dyn-pict ,lc-find) 0))
         (sd (scale (add-boundary-arrows acc edge-spec #:color TYPE-BOUNDARY-COLOR) 2))
         (sd (vc-append (blank (pict-width sd) (pict-height sd)) sd)))
    (values sd sta-pict dyn-pict)))

(define (add-boundary-arrows acc edge-spec #:color [boundary-color BLACK])
  (add-boundary-X pin-arrows-line acc edge-spec #:color boundary-color))

(define (add-boundary-arrow acc edge-spec #:color [boundary-color BLACK])
  (add-boundary-X pin-arrow-line acc edge-spec #:color boundary-color))

(define (add-boundary-X arrow-fn acc edge-spec #:color [boundary-color BLACK])
  (define dom-spec (car edge-spec))
  (define cod-spec (second edge-spec))
  (define dom-pict (car dom-spec))
  (define cod-pict (car cod-spec))
  (define the-angle (caddr edge-spec))
  (arrow-fn
    COMPONENT-ARROW-SIZE
    acc
    dom-pict (second dom-spec)
    cod-pict (second cod-spec)
    #:start-angle (- the-angle)
    #:end-angle the-angle
    #:line-width COMPONENT-ARROW-WIDTH
    #:color boundary-color))

(define (add-thought/sta base tgt txt
                         #:adjust-x [adjust-x values]
                         #:adjust-y [adjust-y #f])
  (add-thought base tgt txt WHITE #:adjust-x adjust-x #:adjust-y (or adjust-y (lambda (n) (* 2 n)))))

(define (add-thought/dyn base tgt txt
                         #:adjust-x [adjust-x #f]
                         #:adjust-y [adjust-y values])
  (add-thought base tgt txt WHITE #:adjust-x (or adjust-x -) #:adjust-y adjust-y))

(define (add-thought base tgt txt color
                     #:adjust-x [adjust-x values]
                     #:adjust-y [adjust-y values])
  (define b-x (adjust-x (* 1/10 (pict-width txt))))
  (define b-y (adjust-y (pict-height txt)))
  (define b-pict (wrap-balloon txt 's b-x b-y color BALLOON-RADIUS))
  (pin-balloon b-pict base tgt ct-find))

(define (need-txt str)
  (hb-append (t "need ") (bt str)))

(define (smallt str)
  (parameterize ((current-font-size SMALL-FONT-SIZE)) (t str)))

(define (gt->pict gt)
  (define mt? (gt-system-mt? gt))
  (define str
    (gt-system-name gt))
  (define-values [fg-color bg-color]
    (if mt?
      (values "black" "Gainsboro")
      (values "white" "Dim Gray")))
  (define txt-p
    (colorize (text str (current-main-font) 22) fg-color))
  (define w (+ 10 (pict-width txt-p)))
  (define h (+ 10 (pict-height txt-p)))
  (define bg-radius 6)
  (tag-pict
    (cc-superimpose
      (filled-rounded-rectangle w h bg-radius #:color bg-color)
      txt-p)
    (string->symbol str)))

(define (gt*->pict gt* #:direction [dir 'H])
  (case dir
    ((H)
     (apply para (map gt->pict gt*)))
    (else
      (raise-argument-error 'gt*->pict "undefined for #:direction" dir))))

(define (pict->blank pp)
  (blank (pict-width pp) (pict-height pp)))

(define (scale-soundness p)
  (scale p 0.74))

(define (scale-for-theorem p)
  (define h (current-font-size))
  (scale-to-fit p h h))

(define make-folklore-slide
  (let ([q1 "Is type soundness all-or-nothing?"]
        [q1-h 2/10]
        [a1 "No! (in a mixed-typed language)"]
        [q2 "How does type soundness affect performance?"]
        [q2-h 5/10]
        [a2 "See graphs"])
    (lambda (#:q1? [q1? #true] #:q2? [q2? #true] #:answers? [answers? #false] #:extra [extra #f])
      (pslide
        #:go (coord SLIDE-LEFT q1-h 'lt)
        (if q1? (speech-bubble #:direction 'left (ss-text q1)) (blank))
        #:go (coord SLIDE-RIGHT 31/100 'rt)
        (if (and q1? answers?) (speech-bubble #:direction 'right (ss-text a1)) (blank))
        #:go (coord SLIDE-LEFT q2-h 'lt)
        (if q2? (speech-bubble #:direction 'left (ss-text q2)) (blank))
        #:go (coord SLIDE-RIGHT 61/100 'rt)
        (if (and q2? answers?) (speech-bubble #:direction 'right (ss-text a2)) (blank))
        #:go (if extra (car extra) (coord 0 0))
        (if extra (cdr extra) (blank))))))

(define (well-t str0 str1)
  (define p*
    (if str1 (list (t ":") (string-pict->text str1)) '()))
  (apply hb-append 2 (t "⊢") (string-pict->text str0) p*))

(define (string-pict->text str)
  (if (pict? str)
    str
    (t str)))

(define (list->program bool* #:margin [margin COMPONENT-MARGIN])
  (define c* (list->component* bool*))
  (apply hb-append margin c*))

(define (make-small-node x)
  (scale (make-node x) 1/10))

(define (bool*->tag b*)
  (bitstring->tag (bool*->bitstring b*)))

(define (bool*->bitstring b*)
  (list->string
    (for/list ((b (in-list b*)))
      (if b #\1 #\0))))

(define (bitstring->tag str)
  (string->symbol (string-append "cfg-" str)))

(define (make-node b*)
  (define pp (list->program b* #:margin COMPONENT-LATTICE-MARGIN))
  (define pp/bg
    (add-rectangle-background pp
                              #:radius 4
                              #:color SURVEY-COLOR
                              #:draw-border? #true
                              #:x-margin 1/16
                              #:y-margin 1/7))
  (tag-pict pp/bg (bool*->tag b*)))

(define (make-lattice total-bits make-node
                      #:x-margin [x-margin LATTICE-NODE-X-MARGIN]
                      #:y-margin [y-margin LATTICE-NODE-Y-MARGIN])
  (define posn* (build-list total-bits values))
  (define level-picts
    (for/list ([on-bits (in-range total-bits -1 -1)])
      (apply hc-append x-margin
       (for/list ([combo (in-combinations posn* on-bits)])
         (define bv (for/list ((b (in-list posn*))) (and (member b combo) #true)))
         (make-node bv)))))
  (apply vc-append y-margin level-picts))

(define (runtime->pict n)
  (t (string-append (add-commas (exact-floor n)) " ms")))

(define (overhead->pict n)
  (define n-str
    (if (< n 1)
      (~r n #:precision '(= 2))
      (add-commas (exact-floor n))))
  (bt (string-append n-str "x")))

(define (make-lattice-icon)
  (define y-max (h%->pixels 1/6))
  (define x-max (* 3 y-max))
  (scale-to-fit (make-lattice 4 make-node #:x-margin 4 #:y-margin 2) x-max y-max))

(define (make-fraction t-pict b-pict)
  (vc-append t-pict (rule (pict-width t-pict) 8) b-pict))

(define (make-check-x-fraction)
  (apply make-fraction
         (pict-bbox-sup (small-check-icon)
                        (hc-append 6 (small-check-icon) (subtitle-text "+") (small-x-icon)))))

(define (make-url str)
  (hyperlinkize (text str MONO-FONT (current-font-size))))

(define (make-overhead-plot e* #:legend? [legend? #true])
  (define w 500)
  (define x-min 0)
  (define x-max (+ (/ pi 10) pi))
  (define pp
    (parameterize ((plot-x-ticks no-ticks)
                   (plot-y-ticks no-ticks)
                   (plot-font-size (current-font-size)))
      (plot-pict
        (for/list ((e (in-list e*)))
          (define c (symbol->color e))
          (function (make-embedding-function e x-min x-max)
                    #:width (* 15 (line-width))
                    #:alpha PLOT-FN-ALPHA
                    #:color c))
        #:y-label #f ;;"Overhead vs. Untyped"
        #:x-label #f ;;"Num. Type Ann."
        #:width 700
        #:height (* PLOT-RATIO w)
        #:x-min x-min
        #:x-max x-max
        #:y-min 0
        #:y-max (* 10 (+ 1 (order-of-magnitude x-max))))))
  (define pp+axis (add-overhead-axis-labels (tag-pict pp 'the-plot) legend?))
  (if legend?
    (ppict-do
      (hc-append 30 (blank) pp+axis)
      #:go (at-find-pict 'the-plot lb-find 'rb #:abs-x -10)
      (make-overhead-legend '(H 1 E)))
    pp+axis))

(define (symbol->color e)
  (case e
    ((H)
     LIGHT-RED)
    ((E)
     GREEN)
    ((1)
     BLUE)
    (else
      (raise-argument-error 'symbol->color "(or/c 'H 'E '1)" e))))

(define (make-overhead-legend e*)
  (define w (* 22/100 client-w))
  (for/fold ([acc (blank w 50)])
            ([e (in-list e*)])
    (vl-append 20 acc (make-embedding-legend e))))

(define (add-overhead-axis-labels pp [legend? #t])
  (define margin 20)
  (define y-label
    (vr-append (t "Overhead vs.")
               (t "Untyped")))
  (define x-label (t "Num. Type Annotations"))
  (define fp (frame-plot pp))
  (if legend?
    (ht-append margin y-label (vr-append margin fp x-label))
    fp))

(define (frame-plot p)
  (add-axis-arrow (add-axis-arrow p 'x) 'y))

(define (add-axis-arrow p xy)
  (define find-dest
    (case xy
      ((x)
       rb-find)
      ((y)
       lt-find)
      (else (raise-argument-error 'add-axis-arrow "(or/c 'x 'y)" 1 p xy))))
  (pin-arrow-line 20 p p lb-find p find-dest #:line-width 6))

(define (make-embedding-function e x-min x-max)
  (define pi/4 (/ 3.14 4))
  (define 3pi/4 (* 3.5 pi/4))
  (case e
    ((H)
     (lambda (n)
       (cond
         [(< n pi/4)
          (max 1 (+ 0.9 (sin n)))]
         [(< n 3pi/4)
          10]
         [else
          0.4])))
    ((E)
     (lambda (n) 1))
    ((1)
     (lambda (n)
       (cond
         [(< n 3pi/4)
          (add1 n)]
         [else
           (- (+ 1 3pi/4) (* 2/10 (- n 3pi/4)))
          ]))
     #;(lambda (n) (add1 n)))
    (else
      (raise-argument-error 'make-embedding-line "embedding?" e))))

(define (make-embedding-legend e)
  (define-values [txt _descr bx] (symbol->name+box e))
  (define txt-pict (t txt))
  (hc-append 10 bx txt-pict))

(define (scale-for-legend p)
  (define h 20)
  (scale-to-fit (cellophane p PLOT-FN-ALPHA) h h))

(define (make-DSE-rule c)
  (rule 40 20 #:color c))

(define (symbol->name+box sym)
  (define dse* (map make-DSE-rule (list DEEP-COLOR SHALLOW-COLOR ERASURE-COLOR)))
  (case sym
    ((H)
     (values "deep" "enforce full types" (car dse*)))
    ((1)
     (values "shallow" "enforce type constructors" (cadr dse*)))
    ((E)
     (values "erasure" "ignore types" (caddr dse*)))
    (else
      (raise-argument-error 'symbol->name+box "(or/c 'H '1 'E)" sym))))

(define (small-overhead-plot)
  (let ((w (* 40/100 client-w)))
    (scale-to-fit (make-overhead-plot '(H 1 E) #:legend? #false) w w)))

(define (make-png-path str)
  (format "src/~a.png" str))

(define (question-frame fg #:title [title #false] #:border-margin [bm #f] #:page-margin [pm #false])
  (add-rounded-frame fg #:title title #:fg-color WHITE #:bg-color QUESTION-COLOR #:border-margin bm #:page-margin pm))

(define (answer-frame fg #:title [title #false] #:fg-color [fg-color WHITE] #:border-margin [bm #f] #:page-margin [pm #false])
  (add-rounded-frame fg #:title title #:fg-color fg-color #:bg-color ANSWER-COLOR #:border-margin bm #:page-margin pm))

(define data-slide-q-x 2/100)
(define -data-slide-q-x (- 1 data-slide-q-x))
(define data-slide-q-coord (coord data-slide-q-x data-slide-q-x 'lt))
(define -data-slide-q-coord (coord -data-slide-q-x (- 1 (* 4 data-slide-q-x)) 'rb))

(define (make-data-slide q-pict r-pict)
  (pslide
    #:go data-slide-q-coord
    q-pict
    #:next
    #:go -data-slide-q-coord
    r-pict))

