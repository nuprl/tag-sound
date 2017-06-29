#lang mf-apply racket/base

;; Workspace for a type sound RST, based on simply-typed λ calculus

;; TODO
;; - substitution lemma (anything hard here?)
;; - mon, need to remember more things????
;; - mon, why/how not nested???
;; - lemma `∀L . ⊢L mon(t,e,L+) : t`

;; =============================================================================

(require
  racket/set
  redex/reduction-semantics)

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse))
)

;; =============================================================================


;; -----------------------------------------------------------------------------
;; --- evalution

;; simple rule for application
;; - if e0 not value then step
;; - if e1 not value then step
;; - if L_ctx = R and v0 not λ then die
;; - if L_ctx finer-than L_λ then mon(t_cod (e[x ↦ mon(t_dom v1 L_ctx)]) L_λ)
;; - if L_ctx coarser-than L_λ then e[x ↦ mon(t_dom v1 L_ctx)]
;; - else e[x ↦ v1]

;; lang(mon _ _ L) = L
;; lang(_) = L_ctx

;; typeof(mon τ _ _) = τ
;; typeof(_) = τ0 or (TST → TST)

;; -----------------------------------------------------------------------------
;; --- examples

;; Assume type-checked,
;; ((λR f . f) (λS x . (+ x 1))) :: String->String
;; --> (mon [String->String] R ((λ f . f) (mon [Int->Int] (λS x . (+ x 1)))))
;; --> (mon [String->String] R (mon [Int->Int] (λS x . (+ x 1))))
;; --> (mon [String->String] R (λS x . (+ x 1)))
;; ??? why does/should this work ??!
