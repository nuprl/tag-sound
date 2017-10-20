#lang mf-apply racket/base

;; Soundness for Typed Racket semantics
;; i.e. theorems connecting the typechecker to the reduction semantics

;; Theorems:
;; - program soundness
;;   * if PROGRAM well-typed at TYPE-ENV
;;   * then reduces to a VAL-ENV
;;   * and VAL-ENV models TYPE-ENV
;;   * (ignore the σ)
;; - module-soundness
;;   * if Γ ⊢ MODULE well-typed at Γ+
;;   * then for any ρ that models Γ
;;   * module reduces to a ρ+
;;   * and ρ+ models Γ+
;;   * (ignore the σ ... sort of)
;; - require soundness
;;   * if Γ ⊢ require at Γ+
;;   * then for any ρ that models Γ
;;   * requires reduce to ρ
;;   * and ρ+ models Γ+
;; - define soudness
;;   * if Γ ⊢ define at Γ+
;;   * then for any ρ that models Γ
;;   * defines reduce to ρ+
;;   * and ρ+ models Γ+
;; - provide soundness
;;   * if Γ ⊢ provide at Γ+
;;   * then for any ρ that models Γ
;;   * provides reduce to ρ+
;;   * and ρ+ models Γ+
;; - expression soundness
;;   * if Γ ⊢ e : τ
;;   * then forall ρ models Γ
;;   * ⊢ ρ(e) : τ
;;   * either:
;;     + reduces to value, ⊢ v : τ
;;     + diverges, raises value error
;;     + raises type error in untyped code
;;     + raises boundary error
;;   * via progress and preservation

;; Just do expressions for now, everything else should follow.

;; -----------------------------------------------------------------------------

(require
  "eval-common.rkt"
  "eval-typed.rkt"
  "lang.rkt"
  "grammar.rkt"
  "metafunctions.rkt"
  "typecheck.rkt"
  racket/set
  redex/reduction-semantics
  redex-abbrevs)

;; =============================================================================

