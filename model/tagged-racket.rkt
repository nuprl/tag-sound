#lang mf-apply racket/base

;; Tagged Racket

;; TODO general principles

;; -----------------------------------------------------------------------------

(require
  racket/set
  redex/reduction-semantics
  redex-abbrevs
  redex-abbrevs/unstable
  (only-in racket/string string-split))

(define *debug* (make-parameter #f))

(define (debug msg . arg*)
  (when (*debug*)
    (apply printf msg arg*)))

(module+ test
  (require rackunit-abbrevs rackunit syntax/macro-testing
           (for-syntax racket/base racket/syntax syntax/parse)))

;; -----------------------------------------------------------------------------

(define-language++ TAG #:alpha-equivalent? α=?
  (e ::= v x (e e) (if e e e) (and e e)
         (let (x τ P) e) (let (x e) e)
         (letrec (x τ P) e) (letrec (x τ e) e) (letrec (x e) e) (REC x)
         (cons e e) (car e) (cdr e)
         (binop e e) (= e e)
         (box e) (make-box e) (unbox e) (set-box! e e)
         (dyn-check tag e srcloc))
  (v ::= (box x) integer boolean Λ (cons v v))
  (Λ ::= (λ (x) e) (λ (x τ) e))
  (P ::= (L e))
  (τ ::= (U τk ...) τk TST)
  (τk ::= Int Bool (Pair τ τ) (→ τ τ) (Box τ))
  (τ/γ ::= (Int srcloc) (Bool srcloc) (TST srcloc)
           ((U τ/γ ...) srcloc)
           ((Pair τ/γ τ/γ) srcloc) ((→ τ/γ τ/γ) srcloc) ((Box τ/γ) srcloc))
  (Γ/γ ::= ((x τ/γ) ...))
  (L ::= R S)
  (Γ ::= ((x τ) ...))
  (ρ ::= (RB ...))
  (RB ::= (x (BOX v)) (x UNDEF) (x (LETREC v)))
  (primop ::= car cdr binop =)
  (binop ::= + * -)
  (tag ::= tagk (U tagk ...))
  (tagk ::= Int Bool Pair → Box)
  (E ::= hole
         (E e) (v E) (if E e e) (and E e) (let (x E) e) (letrec (x E) e)
         (cons E e) (cons v E)
         (car E) (cdr E)
         (binop E e) (binop v E)
         (= E e) (= v E)
         (make-box E) (set-box! E e) (set-box! v E) (unbox E)
         (dyn-check tag E srcloc))
  (RuntimeError ::= (DynError tag v srcloc) (UndefError x))
  (srcloc ::= (path-elem srcloc) (unbox τ) (set-box! τ) (primop τ) (x τ) •)
  (path-elem ::= dom cod car cdr unbox set-box! (proj natural))
  (A ::= [ρ e] RuntimeError)
  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (let (x τ P) e #:refers-to x)
  (letrec (x τ e_L #:refers-to x) e #:refers-to x)
  (letrec (x τ (L e_L #:refers-to x)) e #:refers-to x)
  ;; the 3rd letrec is NOT a binding form, needs to cooperate with enclosing environment
  (λ (x) e #:refers-to x)
  (λ (x τ) e #:refers-to x))

;; -----------------------------------------------------------------------------
