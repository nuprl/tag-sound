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
(define BOX-COLOR (string->color "SeaShell" #;"AntiqueWhite" #;"LightGoldenrodYellow" #;"Beige" #;"bisque"))
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
(define COL-RATIO 85/100)

(define (scale-for-column p)
  (scale p COL-RATIO))

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
(define-runtime-path ben-chung.png "ben-chung.png")
(define-runtime-path paley-li.png "paley-li.png")
(define-runtime-path francesco-zappa-nardelli.png "francesco-zappa-nardelli.png")
(define-runtime-path jan-vitek.png "jan-vitek.png")

(define ARROW-LINE-WIDTH 8)
(define ARROW-HEAD-SIZE 28)
(define EVAL-ARROW-SIZE 24)

(define (hex-triplet->color% x)
  (define-values [r g b]
    (values (arithmetic-shift x -16)
            (bitwise-and #x0000ff (arithmetic-shift x -8))
            (bitwise-and #x0000ff x)))
  (make-color r g b))

(define TRAFFIC-YELLOW (hex-triplet->color% #xFF7221 #;#xffff00 #;#xfad201))

(define ECOOP-RED (hex-triplet->color% #x7b0d0f))

(define kafka-author*
  (list
    (cons "Benjamin Chung" ben-chung.png)
    (cons "Paley Li" paley-li.png)
    (cons "Francesco Zappa Nardelli" francesco-zappa-nardelli.png)
    (cons "Jan Vitek" jan-vitek.png)))

(define-runtime-path erik-ernst.png "erik-ernst.png")
(define-runtime-path ron-garcia.png "ron-garcia.png")
(define-runtime-path ben-lerner.png "ben-lerner.png")
(define-runtime-path fabian-m.png "fabian-m.png")
(define-runtime-path max-new.png "max-new.png")
(define-runtime-path eric-tanter.png "eric-tanter.png")
(define-runtime-path ross-tate.png "ross-tate.png")
(define-runtime-path artem-p.png "artem-p.png")
; We thank Erik Ernst, Ron Garcia, Benjamin S. Lerner, Fabian Muehlboeck,
; Max S. New, Eric Tanter, and Ross Tate for insightful conversations, and
; thank Artem Pelenitsyn, Jan Vitek, and the anonymous ICFP reviewers for
; feedback on early drafts.

(define ack*
  (list
    erik-ernst.png
    ron-garcia.png
    ben-lerner.png
    fabian-m.png
    max-new.png
    eric-tanter.png
    ross-tate.png
    artem-p.png
    #;jan-vitek.png))

(define-runtime-path garden-center.png "garden-center.png")

(define pi 3.14)
(define DOWN-ARROW (arrow EVAL-ARROW-SIZE (* 3/2 pi)))

  (define (generic-arrow stem? solid? size angle pen-thickness brush-style)
    (values
     (dc
      (lambda (dc x y)
	(define (pt->xform-obj p)
	  (let* ([x (car p)]
		 [y (cadr p)]
		 [d (sqrt (+ (* x x) (* y y)))]
		 [a (atan y x)])
	    (make-object point% 
              (* d size 1/2 (cos (+ a angle)))
              (* d size 1/2 (- (sin (+ a angle)))))))
	(let ([b (send dc get-brush)]
	      [p (send dc get-pen)])
	  (send dc set-pen (send the-pen-list
				 find-or-create-pen
				 (send p get-color)
				 (if solid? 0 (send p get-width))
				 'solid))
	  (send dc set-brush (send the-brush-list
				   find-or-create-brush
				   (if solid? (send p get-color) "white")
				   brush-style))
	  (send dc draw-polygon 
		(map pt->xform-obj
		     (if stem?
			 `((1 0)
			   (0 -1)
			   (0 -1/2)
			   (-1 -1/2)
			   (-1 1/2)
			   (0 1/2)
			   (0 1))
			 `((1 0)
			   (-1 -1)
			   (-1/2 0)
			   (-1 1))))
		(+ x (/ size 2)) (+ y (/ size 2)))
	  (send dc set-brush b)
	  (send dc set-pen p)))
      size size)
     (- (- 0 (* 1/2 size (cos angle))) (/ size 2))
     (- (+ (* 1/2 size) (- (* 1/2 size (sin angle)))) size)))

  (define (stripe-arrow/delta size angle)
    (generic-arrow #t #t size angle 0 'crossdiag-hatch #;bdiagonal-hatch))
  (define (stripe-arrow size angle)
    (let-values ([(p dx dy) (stripe-arrow/delta size angle)])
      p))
(define STRIPE-DOWN-ARROW (stripe-arrow EVAL-ARROW-SIZE (* 3/2 pi)))

