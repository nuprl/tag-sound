#lang typed/racket

(define-type Color Symbol)
(require "data.rkt")

(define-type Posn posn)
(define-type Block block)
(define-type Tetra tetra)
(define-type World world)
(define-type BSet  (Listof Block))
(define-type DangerBSet  (Listof (Option Block)))

(provide
 (struct-out posn)
 (struct-out block)
 (struct-out tetra)
 (struct-out world)
 Posn
 Block
 Tetra
 World
 Color
 BSet
 Color
 BSet
 DangerBSet)
