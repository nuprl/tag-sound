#lang typed/racket

(require "data.rkt")

(define-type (NEListof A) (Pairof A (Listof A)))
(define-type Dir (U "up" "down" "left" "right"))
(define-type Snake snake)
(define-type World world)
(define-type Posn  posn)

(provide
 (struct-out posn)
 (struct-out snake)
 (struct-out world)
 Dir
 Snake
 World
 Posn
 NEListof)
