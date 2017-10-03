#lang typed/racket
;; Movie handlers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(require
  "data-adaptor.rkt"
  "collide.rkt"
  "motion.rkt")

(: handle-key : ((Option World) (Option String) . -> . World) )
(define (handle-key w ke)
  (assert w world?)
  (assert ke string?)
  (cond [(equal? ke "w") (world-change-dir w "up")]
        [(equal? ke "s") (world-change-dir w "down")]
        [(equal? ke "a") (world-change-dir w "left")]
        [(equal? ke "d") (world-change-dir w "right")]
        [else w]))

(: game-over? : ((Option World) . -> . Boolean))
(define (game-over? w)
  (assert w world?)
  (or (snake-wall-collide? (world-snake w))
      (snake-self-collide? (world-snake w))))

(provide
 handle-key 
 game-over?)
