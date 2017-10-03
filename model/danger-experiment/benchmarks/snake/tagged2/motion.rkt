#lang typed/racket

(require
  "data-adaptor.rkt"
  "const.rkt"
  "data.rkt"
  "motion-help.rkt")

(provide reset!)
(define r (make-pseudo-random-generator)) 
(define (reset!)
  (parameterize ((current-pseudo-random-generator r))
    (random-seed 1324)))

(: world->world : ((Option World) . -> . World))
(define (world->world w)
  (assert w world?)
  (cond [(eating? w) (snake-eat w)]
        [else
         (world (snake-slither (world-snake w))
                (world-food w))]))

;; Is the snake eating the food in the world.
(: eating? : (World . -> . Boolean))
(define (eating? w)
  (posn=? (assert (world-food w) posn?)
          (car (assert (snake-segs (assert (world-snake w) snake?)) list?))))

;; Change the direction of the snake.
(: snake-change-direction : (Snake Dir . -> . Snake))
(define (snake-change-direction snk dir)
  (snake dir
         (snake-segs snk)))

;; Change direction of the world.
(: world-change-dir : ((Option World) (Option Dir) . -> . World))
(define (world-change-dir w dir)
  (assert w world?)
  (world (snake-change-direction (assert (world-snake w) snake?) (assert dir string?))
         (assert (world-food w) posn?)))

;; Eat the food and generate a new one.
(: snake-eat : (World . -> . World))
(define (snake-eat w)
  (define i (add1 (random (sub1 BOARD-WIDTH) r)))
  (define j (add1 (random (sub1 BOARD-HEIGHT) r)))
  (world (snake-grow (world-snake w))
         (posn i j)))
(provide
 world-change-dir
 world->world)
