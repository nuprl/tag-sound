#lang slideshow

;; Slides for ICFP 2018

(require
  pict
  pict/convert
  ppict
  slideshow/code
  racket/draw racket/runtime-path
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in racket/list make-list))

;; =============================================================================

(define (do-show)
  (set-page-numbers-visible! PAGENUM)
  (parameterize ([current-main-font "Avenir"]
                 [current-font-size 32]
                 #;[current-titlet string->title]
                 #;[*current-tech* #true]
                )
    (sec:title)
    ;(sec:folklore-I)
    ;(sec:notation)
    ;
    ;(sec:graph)
    ;(sec:folklore-II)
    ;
    ;(sec:shape-preview)
    ;(sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

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


(define (sec:conclusion)
  (slide
    #:title "Scientific Foundation for Typed/Untyped Interaction"
    @item{1 language, static + dynamic typing}
    @item{3 formal semantics}
    @item{3 @b{pairs} of type soundness theorems}
    @item{3 models, 3 implementations}
    @comment{
the end thank you
    })
  (void))


;; =============================================================================

(module+ main
  (do-show))
