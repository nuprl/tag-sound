#lang typed/racket

;; Populations of Automata

(provide
  build-random-population
  population-payoffs
  match-up*
  death-birth
  ;; == 
  Payoff
  Population
)
 (: build-random-population
  ;; (build-population n c) for even n, build a population of size n 
  ;; with c constraint: (even? n)
  (-> (Option Natural) Population))
 (: population-payoffs (-> (Option DangerPopulation) [Listof Payoff]))
 (: match-up*
  ;; (match-ups p r) matches up neighboring pairs of
  ;; automata in population p for r rounds 
  (-> (Option DangerPopulation) (Option Natural) DangerPopulation))
 (: death-birth
  ;; (death-birth p r) replaces r elements of p with r "children" of 
  ;; randomly chosen fittest elements of p, also shuffle 
  ;; constraint (< r (length p))
  (-> (Option DangerPopulation) (Option Natural) [#:random (Option (U False Real))] DangerPopulation))

;; =============================================================================
(require "automata.rkt" "utilities.rkt")

(define-type DangerPopulation (Pairof (Option DangerAutomaton*) (Option DangerAutomaton*)))
(define-type Population (Pairof Automaton* Automaton*))
(define-type Automaton* [Vectorof Automaton])
(define-type DangerAutomaton* [Vectorof (Option Automaton)])

(define DEF-COO 2)

;; -----------------------------------------------------------------------------
(define (build-random-population n)
  (define v (build-vector (assert n exact-nonnegative-integer?) (lambda (_) (make-random-automaton DEF-COO))))
  (cons v v))

;; -----------------------------------------------------------------------------
(define (population-payoffs population0)
  (define population (assert (car (assert population0 pair?)) vector?))
  (for/list ([a population]) (automaton-payoff (assert a automaton?))))

;; -----------------------------------------------------------------------------

(define (match-up* population0 rounds-per-match)
  (define a* (assert (car (assert population0 pair?)) vector?))
  ;; comment out this line if you want cummulative payoff histories:
  ;; see below in birth-death
  (population-reset a*)
  ;; -- IN --
  (for ([i (in-range 0 (- (vector-length a*) 1) 2)])
    (define p1 (vector-ref a* i))
    (define p2 (vector-ref a* (+ i 1)))
    (define-values (a1 a2) (match-pair p1 p2 rounds-per-match))
    (vector-set! a* i a1)
    (vector-set! a* (+ i 1) a2))
  population0)

(: population-reset (-> DangerAutomaton* Void))
;; effec: reset all automata in a*
(define (population-reset a*)
  (for ([x (in-vector a*)] [i (in-naturals)])
    (vector-set! a* i (automaton-reset x))))

;; -----------------------------------------------------------------------------

(define (death-birth population0 rate #:random (q #false))
  (match-define (cons pre-a* pre-b*) (assert population0 pair?))
  (define a* : DangerAutomaton* (assert pre-a* vector?))
  (define b* : DangerAutomaton* (assert pre-b* vector?))
  (define payoffs
    (for/list : [Listof Payoff] ([x : (Option Automaton) (in-vector a*)])
      (automaton-payoff (assert x automaton?))))
  [define substitutes (choose-randomly payoffs rate #:random q)]
  (for ([i (in-range (assert rate exact-nonnegative-integer?))][p (in-list substitutes)])
    (vector-set! a* i (clone (vector-ref b* p))))
  (shuffle-vector a* b*))

(: shuffle-vector
   (All (X) (-> (Vectorof X) (Vectorof X) (cons (Vectorof X) (Vectorof X)))))
;; effect: shuffle vector b into vector a
;; constraint: (= (vector-length a) (vector-length b))
;; Fisher-Yates Shuffle

(define (shuffle-vector b a)
  ;; copy b into a
  (for ([x (in-vector b)][i (in-naturals)])
    (vector-set! a i x))
  ;; now shuffle a 
  (for ([x (in-vector b)] [i (in-naturals)])
    (define j (random (add1 i)))
    (unless (= j i) (vector-set! a i (vector-ref a j)))
    (vector-set! a j x))
  (cons a b))
