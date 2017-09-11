#lang mf-apply racket/base

;; Tagged Racket v2
;;  more types

;; TODO
;; - type-check polymorphic function application (or, do polymorphism in general)
;; - blame for dynamic checks
;; - remove unnecessary checks
;; - optimize

;; -----------------------------------------------------------------------------

(require
  redex/reduction-semantics)

;; =============================================================================

(define-language TAG
  (τ ::= Int Pos Neg Zero
         (Box τ) (Pair τ τ) (→ τ τ)
         (∀ (α) τ) (μ (α) τ)
         (∪ τ τ τ ...) (∩ τ τ τ ...))
  (Γ ::= ((x τ) ...))

  (t ::= (:: integer τ)
         (:: (box t) τ)
         (:: (cons t t) τ)
         (:: (t t) τ)
         (:: (fun x (x) t) τ)
         (:: (let (x t) t) τ)
         (:: (require (x τ e) t) τ)
         ;; ... MORE
         )
  (e ::= integer
         (box e)
         (cons e e)
         ;; ... MORE
         )
  (c ::= integer
         (box c)
         (cons c c)
         (fun x (x) c)
         (let (x c) c)
         (c c)
         ;; ... MORE
         )

  (x α ::= variable-not-otherwise-mentioned)
#:binding-forms
  (fun x_f (x) t #:refers-to (shadow x_f x))
  (fun x_f (x) c #:refers-to (shadow x_f x))
)
