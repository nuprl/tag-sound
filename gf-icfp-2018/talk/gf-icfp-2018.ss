#lang at-exp slideshow

;; Slides for ICFP 2018

(require
  pict
  ppict
  slideshow/code
  racket/runtime-path)

;; =============================================================================
;; --- constants

(define PAGENUM #true)
(define TITLESTR "A Spectrum of Type Soundness and Performance")

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
    (sec:extra)
    (void)))

;; -----------------------------------------------------------------------------
;; --- helper functions

;; -----------------------------------------------------------------------------
;; --- slide functions

(define (sec:title)
  (slide
    @text[TITLESTR (current-main-font) (+ (current-font-size) 20)]
    @t{Ben Greenman & Matthias Felleisen}
    @comment{
      yolo
    })
  (void))

(define (sec:extra)
  (void))


;; =============================================================================

(module+ main
  (do-show))
