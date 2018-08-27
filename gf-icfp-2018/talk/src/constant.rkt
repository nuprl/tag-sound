#lang racket/base

(provide (all-defined-out))

(require
  images/icons/style images/logos
  pict
  ppict/tag
  racket/class
  racket/draw
  racket/runtime-path)

;; -----------------------------------------------------------------------------

(define (string->color str)
  (or (send the-color-database find-color str)
      (raise-argument-error 'string->color "color-name?" str)))

(define (triplet->color rgb)
  (make-object color% (car rgb) (cadr rgb) (caddr rgb)))

(define TITLESTR "A Spectrum of Type Soundness and Performance")

(define SLIDE-TOP 1/10)
(define SLIDE-LEFT 1/20)
(define SLIDE-BOTTOM 4/5)
(define SLIDE-RIGHT (- 1 SLIDE-LEFT))

(define BROWN (string->color "chocolate"))
(define RED (string->color "firebrick"))
(define LIGHT-RED (string->color "Tomato"))
(define GREEN (string->color "mediumseagreen"))
(define BLUE (string->color "cornflowerblue"))
(define LIGHT-BLUE (string->color "Lavender"))
(define DARK-BLUE syntax-icon-color)
(define WHITE (string->color "Snow"))
(define RAY-COLOR RED)
(define BOX-COLOR (string->color "bisque"))
(define FF-COLOR (string->color "forestgreen"))
(define BLACK (string->color "black"))
(define GREY (string->color "gray"))
(define DARK-GREY (string->color "DarkSlateGray"))
(define DYN-COLOR DARK-GREY)
(define DYN-TEXT-COLOR (string->color light-metal-icon-color))
(define STAT-COLOR (string->color "Pink"))
(define HIGHLIGHT-COLOR (string->color "DarkViolet"))

(define TAU-COLOR "DarkGoldenrod")

(define FILE-RATIO 5/6) ;; TODO nonsense
(define PLOT-RATIO 3/4) ;; TODO nonsense

(define-runtime-path racket-logo.png "racket-logo.png")
(define-runtime-path neu-logo.png "neu-seal.png")

(define racket-logo (scale-to-fit (bitmap racket-logo.png) 80 80))
(define neu-logo (scale-to-fit (bitmap neu-logo.png) 80 80))

(define (arrow-text str)
  (text str '() 20))

(define (make-> str)
  (define tag (string->symbol (format "->~a" str)))
  (tag-pict (arrow-text (format "→~a" str)) tag))

(define (make-⊢ str)
  (ht-append -6
             (arrow-text "⊢")
             (vl-append (blank 0 16)
                        (arrow-text str))))

(define make-TR->
  (let ([tiny (bitmap (plt-logo #:height 20))])
    (lambda (str)
      (hc-append tiny (arrow-text str)))))

(define ->racket (make-> "racket"))
(define ->H (make-> "H"))
(define ->E (make-> "E"))
(define ->1 (make-> "1"))
(define ->TR-H (make-TR-> "H"))
(define ->TR-E (make-TR-> "E"))
(define ->TR-1 (make-TR-> "1"))
(define ⊢H (make-⊢ "H"))
(define ⊢E (make-⊢ "E"))
(define ⊢1 (make-⊢ "1"))

(define ALL-CAPS-FONT "Bebas Neue")
(define MONO-FONT "Triplicate T4s")

(define WATERMARK-ALPHA 1/5)

(define (set-alpha c a)
  (make-object color% (send c red) (send c green) (send c blue) a))

(define q-color
  (set-alpha (string->color "LemonChiffon") WATERMARK-ALPHA))

(define a-color
  (string->color "AliceBlue"))

(define TITLE-FONT "Fira Sans, Heavy")

(define POOL-TAG 'pool)
(define STAT-TAG 'stat-file)
(define DYN-TAG 'dyn-file)
(define POOL-X-BASE 30)
(define POOL-Y-BASE 60)

(define MAIN-CONTRIB-X (- SLIDE-LEFT 2/100))
(define MAIN-CONTRIB-Y 15/100)

(define PLOT-FN-ALPHA 0.6)

(define-runtime-path cache-scatterplots.png "cache-scatterplots.png")
(define-runtime-path kafka.png "kafka.png")
