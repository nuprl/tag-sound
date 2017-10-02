#lang typed/racket/base

(provide
  (struct-out label)
  (struct-out suffix-tree)
  (struct-out node))


(define-struct label ([datum : (Option (Vectorof (Option (U Char Symbol))))] [i : (Option Natural)] [j : (Option Natural)]) #:mutable)

;; A suffix tree consists of a root node.
(define-struct suffix-tree ([root : (Option node)]))

;; up-label: label
;; parent: (union #f node)
;; children: (listof node)
;; suffix-link: (union #f node)
(define-struct node ([up-label : (Option label)] [parent : (Option (U #f node))] [children : (Option (Listof (Option node)))] [suffix-link : (Option (U #f node))]) #:mutable)
