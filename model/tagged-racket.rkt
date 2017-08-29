#lang mf-apply racket/base

;; Tagged Racket
;; "you can trust the tags"
;;
;; Check any value that enters typed code from "untyped" code
;; - check imports from untyped code
;; - check input to typed functions
;; - check reads from untyped data (calling untyped function, read from box/list)
;; For now, be conservative. Anything might be untyped.
;;
;; This is dynamic typing, where every type annotation represents a boundary.

;; Soundness = tag soundness

;; TODO
;; - blame for dynamic checks
;; - remove unnecessary checks
;; - optimize

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

;; =============================================================================

(define-language++ TAG #:alpha-equivalent? α=?
;; τ = specification language
  (?τ ::= τ Dyn)
  (τ ::= k (k τ ...))
  (k ::= Nat Int Bool Pair → Box)
  (K ::= k) ;; types we can check at runtime, O(1)
  (Γ ::= ((x ?τ) ...))

;; v = values
  (v ::= (box x) integer boolean Λ (cons v v))
  (Λ ::= (fun x (x) e))

;; e = implicitly typed source language, allows untyped terms
;;     needs explicit types for functions
;;      and embedded untyped terms
  (e ::= v x (e e) (if e e e)
         (let (x e) e)
         (:: Λ τ) (let (x (:: e τ)) e)
         (unop e) (binop e e))
  (primop ::= unop binop)
  (binop ::= + * - =)
  (unop ::= car cdr)

;; t = explicitly typed intermediate language, still allows untyped (source) terms
  (t ::= (:: v τ) (:: x τ) (:: (t t) τ) (:: (if t t t) τ)
         (:: (let (x t) t) τ)
         (:: (let (x e) t) τ)
         (:: (unop t) τ)
         (:: (binop t t) τ))

;; c = type-erased, explicitly checked core language
  (c ::= v x (c c) (if c c c) (let (x c) c) (unop c) (binop c c) (check K c))
  (σ ::= ((x v) ...))
  (E ::= hole (E c) (v E) (if E c c) (let (x E) c) (unop E) (binop E c) (binop v E))
  (RuntimeError ::= (CheckError K v))
  (A ::= [ρ e] RuntimeError)

  (x ::= variable-not-otherwise-mentioned)
#:binding-forms
  (let (x e) e_1 #:refers-to x)
  (let (x (:: e τ)) e_1 #:refers-to x)
  (fun x_f (x) e #:refers-to (shadow x_f x))
  (:: (let (x t) t_1 #:refers-to x) τ)
  (:: (let (x e) t_1 #:refers-to x) τ)
  (let (x c) c_1 #:refers-to x))

;; =============================================================================

(define-metafunction TAG
  theorem:type-soundness : e -> boolean
  [(theorem:type-soundness e)
   boolean_sound
   (where (:: t τ) #{type-check# e})
   (where c #{completion# t})
   (where A #{eval# c})
   (where K #{tag# τ})
   (where boolean_ok #{value-check# A K})])

(module+ test
  (test-case "type-soundness:basic"
    (check-true (term (theorem:type-soundness
      (+ 2 2))))
    (check-true (term (theorem:type-soundness
      ((:: (fun factorial (n)
             (if (= n 1) 1 (* n (factorial (- n 1))))) (→ Int Int))
       5))))
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  type-check# : e -> (:: t τ)
  [(type-check# e)
   (:: t τ)
   (judgment-holds (type-check e (:: t τ)))
   (side-condition (term #{sound-elaboration# e (:: t τ)}))]
  [(type-check# e)
   ,(raise-argument-error 'type-check# "well-typed expression" (term e))])

(module+ test
  (test-case "type-check:basic"
    (check-mf-apply*
     [(type-check# (+ 2 2))
      (:: (+ (:: 2 Int) (:: 2 Int)) Int)]
     [(type-check# (:: (fun f (x) #true) (→ Int Bool)))
      (:: (fun f (x) (:: #false Bool)) (→ Int Bool))])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  completion# : t -> c
  [(completion# t)
   c
   (judgment-holds (completion t c))
   (side-condition (term #{sound-completion# t c}))]
  [(completion# t)
   ,(raise-argument-error 'completion# "(completable) type-annotated term" (term t))])

(module+ test
  (test-case "completion:basic"
    (check-mf-apply*
     [(completion# (:: (+ (:: 2 Int) (:: 2 Int)) Int))
      (+ 2 2)]
     [(completion# (:: (let (x (:: 2 Int)) (:: (+ (:: x Int) (:: 2 Int)) Int)) Int))
      (let (x 2) (+ x 2))]
     [(completion# (:: (let (f (:: (fun f (x) x) (→ Int Int))) (:: ((:: f (→ Int Int)) (:: 2 Int)) Int)) Int))
      (let (f (fun f (x) x)) (check Int (f x)))]
     [(completion# (:: (car (:: (cons 2 2) (Pair Int Int))) Int))
      (check Int (car (cons x 2)))])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  eval# : c -> A
  [(eval# c)
   A_1
   (where A_0 #{load# c})
   (where A_1 ,(apply-reduction-relation* eval* (term c)))]
  [(eval# c)
   ,(raise-argument-error 'eval# "core term" (term c))])

(define-metafunction TAG
  load# : c -> A
  [(load# c)
   [() c]])

(module+ test
  (test-case "eval:basic"
    (check-mf-apply*
     [(eval# (+ 2 2))
      4]
     [(eval# ((fun fact (n) (if (= n 1) 1 (* n (fact (- n 1))))) 5))
      120])
    (void)))

;; -----------------------------------------------------------------------------

(define-metafunction TAG
  value-check# : A K -> boolean
  [(value-check# A K)
   #true
   (judgment-holds (value-check A K))]
  [(value-check# A K)
   #false])

(module+ test
  (test-case "value-check:basic"
    (check-mf-apply*
     [(value-check# [() 4] Int)
      #true]
     [(value-check# [() 4] Bool)
      #false]
     [(value-check# [() (fun f (x) #false)] →)
      #true])
    (void)))

;; =============================================================================
;; === type check

(define-judgment-form TAG
  #:mode (type-check I O)
  #:contract (type-check e t)
  [
   ---
   (type-check e (:: 0 Int))])

(define-metafunction TAG
  sound-elaboration# : e t -> boolean
  [(sound-elaboration# e t)
   ,(raise-user-error 'sound-elaboration# "undefined")])

;; =============================================================================
;; === completion

(define-judgment-form TAG
  #:mode (completion I O)
  #:contract (completion t c)
  [
   ---
   (completion t 0)])

(define-metafunction TAG
  sound-completion# : t c -> boolean
  [(sound-completion# t c)
   ,(raise-user-error 'sound-completion# "not implemented")])

;; =============================================================================
;; === eval

(define -->TAG
  (reduction-relation TAG
   #:domain A
   [-->
    [σ c]
    (CheckError Int 0)
    (side-condition (raise-user-error '-->TAG "not implemented"))]))

(define eval*
  (make--->* -->TAG))

;; =============================================================================
;; === value-check

(define-judgment-form TAG
  #:mode (value-check I I)
  #:contract (value-check A K)
  [
   ---
   (value-check A K)])

(define-metafunction TAG
  tag# : τ -> K
  [(tag# τ)
   K
   (judgment-holds (tag-of τ K))])

(define-judgment-form TAG
  #:mode (tag-of I O)
  #:contract (tag-of τ K)
  [
   ---
   (tag-of τ Int)])

;; =============================================================================
;; =============================================================================

;; =============================================================================
;; === grammar

;; TODO

;; =============================================================================
;; === misc

;; =============================================================================
;; === test

