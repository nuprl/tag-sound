#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - slide background
;; - fancy title slide
;; - 

(require
  pict
  pict/convert
  ppict
  slideshow/code
  racket/draw racket/runtime-path
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in racket/list make-list))

;; =============================================================================
;; --- constants

(define PAGENUM #true)
(define TITLESTR "A Spectrum of Type Soundness and Performance")

(define VALUE-HEIGHT 40)
(define VALUE-MATERIAL plastic-icon-material)
(define SCANNER-HEIGHT 160)
(define BELT-HEIGHT-RATIO 1/4)
(define BELT-WIDTH-RATIO 2)
(define SCANNER-RATIO 1/30)
(define STUCK-OFFSET-RATIO 1/10)
(define STUCK-HEIGHT-RATIO 2)
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
(define WHITE (string->color "Snow"))
(define RAY-COLOR RED)
(define BOX-COLOR (string->color "bisque"))
(define FF-COLOR (string->color "forestgreen"))
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
    ;(sec:title)
    ;(sec:folklore-I)
    (sec:notation)
    ;
    (sec:graph)
    (sec:folklore-II)
    ;
    ;(sec:shape-preview)
    ;(sec:extra)
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

(define (make-square #:height [h VALUE-HEIGHT] #:color [c DARK-BLUE] #:material [m VALUE-MATERIAL])
  (bitmap (stop-icon #:color c #:height h #:material m)))

(define (make-arrow #:left? [left? #false] #:height [h VALUE-HEIGHT] #:color [c syntax-icon-color])
  (bitmap ((if left? left-arrow-icon right-arrow-icon) #:color c #:height h)))

(define (make-container elem-pict*)
  ;; < elem-pict* ... >
  (t "make-container not implemented"))

(define (make-ff #:height [h VALUE-HEIGHT] #:color [c FF-COLOR] #:left? [left? #false])
  (bitmap ((if left? rewind-icon fast-forward-icon) #:color c #:height h)))

(define (make-belt #:height h #:width w #:left? [left? #false] #:radius [r 0] #:angle [a 0])
  (define inner-color GREY)
  (define belt-color DARK-GREY)
  (define belt-width (/ w 40))
  (define ff-height (* FF-RATIO h))
  (define ff (make-ff #:left? left? #:height ff-height))
  (define bar (filled-rounded-rectangle w h #:color inner-color #:border-color belt-color #:border-width belt-width))
  ;; (define end (disk h #:draw-border? #true #:color inner-color #:border-color belt-color #:border-width belt-width))
  ;; TODO use ends
  (rc-superimpose (lc-superimpose bar ff) ff))

(define (make-box #:height h #:width w #:color [c BOX-COLOR])
  (define bw (/ h 20))
  (filled-rectangle w h #:color c #:draw-border? #true #:border-color BLACK #:border-width bw))

(define (make-function dom-pict cod-pict #:left? [left? #false])
  (define box-height
    (let ([dom-h (pict-height dom-pict)]
          [cod-h (pict-height cod-pict)])
      (* 1.6 (max dom-h cod-h))))
  (define arrow-pict (make-arrow #:left? left? #:height (* ARROW-RATIO box-height)))
  (define box-width
    (let ([dom-w (pict-width dom-pict)]
          [cod-w (pict-width cod-pict)]
          [arr-w (pict-width arrow-pict)])
      (+ 30 (+ dom-w cod-w arr-w))))
  (define box-pict (make-box #:height box-height #:width box-width))
  (cc-superimpose
    box-pict
    (let ([box-sep (/ box-width 25)])
      (if left?
        (hc-append box-sep cod-pict arrow-pict dom-pict)
        (hc-append box-sep dom-pict arrow-pict cod-pict)))))

(define (make-function/belt dom-pict cod-pict #:left? [left? #false])
  (define f-pict (make-function dom-pict cod-pict #:left? left?))
  (define b-pict
    (let ([f-w (pict-width f-pict)]
          [f-h (pict-height f-pict)])
      (define h (* BELT-HEIGHT-RATIO f-h))
      (define w (* BELT-WIDTH-RATIO f-w))
      (make-belt #:height h #:width w #:left? left?)))
  (vc-append -4 f-pict b-pict))

(define (make-function-label dom-pict cod-pict)
  (define f-pict (make-function dom-pict cod-pict))
  (define scale-factor 3/4)
  (scale f-pict scale-factor))

(define (add-scanner/dom f-pict lbl-pict #:alarm? [alarm? #false])
  (add-scanner f-pict lbl-pict 'dom #:alarm? alarm?))

(define (add-scanner/cod f-pict lbl-pict #:alarm? [alarm? #false])
  (add-scanner f-pict lbl-pict 'cod #:alarm? alarm?))

(define (add-scanner f-pict lbl-pict where #:alarm? [alarm? #false])
  (define f-h (pict-height f-pict))
  (define f-w (pict-width f-pict))
  (define s-pict
    (make-scanner lbl-pict #:height (+ f-h (* 1/3 f-h)) #:alarm? alarm?))
  (add-thing f-pict s-pict where))

(define (add-stuck f-pict)
  (define w (pict-width f-pict))
  (define s-pict (make-stuck #:height (* STUCK-HEIGHT-RATIO VALUE-HEIGHT)))
  #;(define offset (* STUCK-OFFSET-RATIO w))
  #;(define s+
    (hc-append (blank offset 0) s-pict))
  (cc-superimpose f-pict s-pict))

(define (add-input f-pict val-pict)
  (define v+ (raise-above-belt val-pict (pict-height f-pict)))
  (add-thing f-pict v+ 'dom))

(define (add-output f-pict val-pict)
  (define v+ (raise-above-belt val-pict (pict-height f-pict)))
  (add-thing f-pict v+ 'cod))

(define (raise-above-belt p total-height)
  (define belt-height
    ;; depends on how total-height was computed, in make-function/belt
    (/ (* total-height BELT-HEIGHT-RATIO)
       (+ 1 BELT-HEIGHT-RATIO)))
  (vl-append p (blank 0 belt-height)))

(define (add-thing f-pict s-pict where)
  (define f-w (pict-width f-pict))
  (define offset-pict
    (blank (* SCANNER-RATIO f-w) 0))
  (define-values [f s+]
    (case where
      ((dom)
       (values lb-superimpose (hc-append offset-pict s-pict)))
      ((cod)
       (values rb-superimpose (hc-append s-pict offset-pict)))))
  (f s+ f-pict))

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

(define (itemrm n . str*)
  (define r-str (string-append (integer->roman n) ". "))
  (define r-pict (t r-str))
  (item #:bullet r-pict str*))

(define (itemrmX n . str*)
  (define r-str (integer->roman n))
  (define rX-pict
    (let* ([h (pict-width (t "."))]
           [w (- (pict-height (t r-str)) (* 2 h))]
           [rect (filled-rectangle w h #:draw-border? #false #:color RED)]
           [x-pict rect #;(rotate rect (/ pi 3))])
      (lc-superimpose (t (string-append r-str ". ")) x-pict)))
  (item #:bullet rX-pict str*))

(define (integer->roman n)
  (define r (natural->roman (abs n)))
  (if (< n 0)
    (string-append "-" r)
    r))

(define natural->roman
  (let ([ROMAN '#("" "I" "II" "III" "IV" "V" "VI" "VII" "VIII" "IX" "X")])
    (lambda (n)
      (vector-ref ROMAN n))))

;; -----------------------------------------------------------------------------
;; --- slide functions

(define (sec:shape-preview)
  (slide
    (hc-append
      20
      (make-function/belt (make-stuck) (make-dyn) #:left? #true)
      (make-function/belt (make-triangle) (make-dyn) #:left? #true)
      (make-function/belt (make-bomb) (make-circle)))
    (make-function/belt (make-function-label (make-triangle) (make-triangle))
                        (make-function-label (make-circle) (make-dyn)))
    (add-scanner/dom (make-function/belt (make-stuck) (make-dyn))
                     (make-circle))
    (add-scanner/cod (make-function/belt (make-stuck) (make-dyn))
                     (make-dyn))
    (add-stuck (make-function/belt (make-dyn) (make-circle)))
    )
  (void))

(define (sec:title)
  (slide
    ;; TODO racket-logo title slide ... make package for that
    @text[TITLESTR (current-main-font) (+ (current-font-size) 10)]
    @t{Ben Greenman & Matthias Felleisen}
    @t{PLT @"@" Northeastern University}
    @comment{
hello this paper is about gradual typing but this talk is really about two
pieces of folklore ....
    })
  (void))

(define (sec:folklore-I)
  ;; original folklore
  (slide
    #:title "Folklore"
    @itemrm[1]{Type soundness is all-or-nothing}
    @itemrm[2]{Adding type information can only improve performance (Perf ∝ #τ)}
    @comment{
folklore I is the belief that type soundness is a yes-or-no proposition namely
a langauge is either type-sound, unsound, or has a bug --- the space in between
is useless folklore II is the belief that adding type information to a program
can only improve performance in that it gives a compiler more information about
invariants and nothing else as you know the thing about folklore is it can be
true and useful or false and misleading the goal of this talk is to show that
neither claim is very true (or useful) for a language that allows types and
utnyped code to interact and that said to substitute an accurate picture based
on the content of our paper
    })
  (void))

(define (sec:notation)
  (define the-function (make-function/belt (make-triangle #:color WHITE) (make-triangle #:color WHITE)))
  (slide
    the-function
    @comment{
(lets get started) this is a function the label on the left says that this
function expects triangles as input and the label on the right says it produces
triangles as output
    })
  (slide
    ;; TODO make smooth animation
    'alts
    `((,(add-input the-function (make-triangle #:color GREEN)))
      (,the-function)
      (,(add-output the-function (make-triangle #:color RED))))
    @comment{
and yes if we run it on a triangle we get back a new
triangle (tri -> green tri)
    })
  (slide
    'alts
    `((,(add-input the-function (make-circle #:color DARK-BLUE)))
      (,(add-stuck the-function))
      (,(add-input the-function (make-container (make-list 2 (make-triangle #:color GREEN)))))
      (,(add-stuck the-function))
      (,(add-input the-function (make-function (make-triangle #:color WHITE) (make-triangle #:color WHITE))))
      (,(add-output the-function (make-bomb))))
    @comment{
if we run it on something that is not a triangle,
say a square or a list of triangles or --- since this is a higher-order
language --- another function, then the result is undefined it might crash our
function and it might compute a nonsense output so theres a danger of crashes
and silent failures
    })

  (void))

(define (sec:graph)
  ;; perf vs types graph
  (void))

(define (sec:folklore-II)
  (slide
    ;; TODO why are itemrmX not aligned???
    #:title "Folklore"
    @itemrmX[1]{Type soundness is all-or-nothing}
    @itemrmX[2]{Adding type information can only improve performance (Perf ∝ #τ)}
    @comment{
???
    })
  (void))

(define (sec:extra)
  (void))


;; =============================================================================

(module+ main
  (do-show))
