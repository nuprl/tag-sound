#lang typed/racket

(require
  "base-types.rkt"
  "block.rkt"
  "consts.rkt")

;; Determine if the block is in the set of blocks.
(: blocks-contains? (-> (Option DangerBSet) (Option Block) Boolean))
(define (blocks-contains? bs b)
  (ormap (λ: ([c : (Option Block)]) (block=? b c)) (assert bs list?)))

;; is every element in bs1 also in bs2?
(: blocks-subset? (-> (Option DangerBSet) (Option DangerBSet) Boolean))
(define (blocks-subset? bs1 bs2)
  (andmap (λ: ([b : (Option Block)]) (blocks-contains? bs2 b)) (assert bs1 list?)))

;; Determine if given sets of blocks are equal.
(: blocks=? (-> (Option DangerBSet) (Option DangerBSet) Boolean))
(define (blocks=? bs1 bs2)
  (and (blocks-subset? bs1 bs2)
       (blocks-subset? bs2 bs1)))

;; Return the set of blocks that appear in both sets.
(: blocks-intersect (-> (Option DangerBSet) (Option DangerBSet) DangerBSet))
(define (blocks-intersect bs1 bs2)
  (filter (λ: ([b : (Option Block)]) (blocks-contains? bs2 b)) (assert bs1 list?)))

;; Return the number of blocks in the set.
(: blocks-count (-> (Option DangerBSet) Natural))
(define (blocks-count bs)
  (length (assert bs list?)))  ;; No duplicates, cardinality = length.

;; Move each block by the given X & Y displacement.
(: blocks-move (-> (Option Real) (Option Real) (Option DangerBSet) BSet))
(define (blocks-move dx dy bs)
  (map (λ: ([b : (Option Block)]) (block-move dx dy b)) (assert bs list?)))

;; Rotate the blocks 90 counterclockwise around the posn.
(: blocks-rotate-ccw (-> (Option Posn) (Option DangerBSet) BSet))
(define (blocks-rotate-ccw c bs)
  (map (λ: ([b : (Option Block)]) (block-rotate-ccw c b)) (assert bs list?)))

;; Rotate the blocks 90 clockwise around the posn.
(: blocks-rotate-cw (-> (Option Posn) (Option DangerBSet) BSet))
(define (blocks-rotate-cw c bs)
  (map (λ: ([b : (Option Block)]) (block-rotate-cw c b)) (assert bs list?)))

(: blocks-change-color (-> (Option DangerBSet) (Option Color) BSet))
(define (blocks-change-color bs c)
  (assert c symbol?)
  (map (λ: ([b : (Option Block)]) (assert b block?) (block (block-x b) (block-y b) c))
       (assert bs list?)))

;; Return the set of blocks in the given row.
(: blocks-row (-> (Option DangerBSet) (Option Real) DangerBSet))
(define (blocks-row bs i)
  (assert i real?)
  (filter (λ: ([b : (Option Block)]) (= i (block-y (assert b block?)))) (assert bs list?)))

;; Are there a full row of blocks at the given row in the set.
(: full-row? (-> (Option DangerBSet) (Option Natural) Boolean))
(define (full-row? bs i)
  (= board-width (blocks-count (blocks-row bs i))))

;; Have any of the blocks reach over the top of the board?
(: blocks-overflow? (-> (Option BSet) Boolean))
(define (blocks-overflow? bs)
  (ormap (λ: ([b : (Option Block)]) (<= (block-y (assert b block?)) 0)) (assert bs list?)))

;; Union the two sets of blocks.
(: blocks-union (-> (Option DangerBSet) (Option DangerBSet) DangerBSet))
(define (blocks-union bs1 bs2)
  (foldr (λ: ([b  : (Option Block)]
              [bs : DangerBSet])
           (cond [(blocks-contains? bs b) bs]
                 [else (cons b bs)]))
         (assert bs2 list?)
         (assert bs1 list?)))

;; Compute the maximum y coordinate;
;; if set is empty, return 0, the coord of the board's top edge.
(: blocks-max-y (-> (Option DangerBSet) Real))
(define (blocks-max-y bs)
  (foldr (λ: ([b : (Option Block)]
              [n : Real])
           (max (block-y (assert b block?)) n)) 0 (assert bs list?)))

;; Compute the minimum x coordinate;
;; if set is empty, return the coord of the board's right edge.
(: blocks-min-x (-> (Option DangerBSet) Real))
(define (blocks-min-x bs)
  (foldr (λ: ([b : (Option Block)]
              [n : Real])
           (min (block-x (assert b block?)) n)) board-width (assert bs list?)))

;; Compute the maximum x coordinate;
;; if set is empty, return 0, the coord of the board's left edge.
(: blocks-max-x (-> (Option DangerBSet) Real))
(define (blocks-max-x bs)
  (foldr (λ: ([b : (Option Block)] 
              [n : Real])
           (max (block-x (assert b block?)) n)) 0 (assert bs list?)))

(provide
 blocks-contains?
 blocks=?
 blocks-subset?
 blocks-intersect
 blocks-count
 blocks-overflow?
 blocks-move
 blocks-rotate-cw
 blocks-rotate-ccw
 blocks-change-color
 blocks-row
 full-row?
 blocks-union
 blocks-max-x
 blocks-min-x
 blocks-max-y)
