#lang mf-apply racket/base

;; Simple model of Transient Racket
;; - typecheck program
;; - use types to insert runtime checks
;;   insert checks at destructors
;; - no monitors

;; Soundness:
;;   If `⊢ e : τ` then `⊢ e : tag(τ)` either
;;   - `e` reduces to `v` and `⊢ v : tag(τ)`
;;   - `e` diverges
;;   - `e` raises a dynamic typing error
;;     DynError tag v srcloc
;;     where not well-tagged v tag
;;     and tag is component of srcloc (TODO)
;;   - `e` raises a transient-typing error
;;     DynError tag v srcloc
;;     where not well-tagged v tag
;;     and srcloc is path to the boundary that inspired the check
;;
;; MT1 is weaker, MT2 is weaker

;; Lemmas
;; - transient-completion : never uses context
;; - "blames last boundary"

;; Questions
;; - how to negative box boundaries?
;;   - for λ, added dynamic check
;;   - can do same thing for box?
;;   - or just forget it, because the box is tag-sound
;; - how to trace back to let-boundaries?

;; Future
;; - remove boundaries when possible
;;   - distinguish "this function was statically checked"
;; - RST interactions
;; - Function annotations are NOT weaker than λ types

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

(define-language++ μSR #:alpha-equivalent? α=?
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

(module+ test
  (*term-equal?* α=?)

  (define R-fib (term
    (R (letrec (fib (→ Int Int)
               (R (λ (n TST)
                    (if (= n 0) 1 (if (= n 1) 1
                      (let (prev2 TST (R (box 1)))
                        (let (prev1 TST (R (box 1)))
                          (letrec (loop TST
                                  (R (λ (n TST)
                                       (let (curr TST (R (+ (unbox prev1) (unbox prev2))))
                                         (if (= n 0)
                                           curr
                                           (let (blah TST (R (set-box! prev2 (unbox prev1))))
                                             (let (bb TST (R (set-box! prev1 curr)))
                                               (loop (- n 1)))))))))
                            (loop (- n 2))))))))))
         (fib 5)))))

  (define S-fib (term
    (S (letrec (fib (→ Int Int)
               (S (λ (n Int)
                    (if (= n 0) 1 (if (= n 1) 1
                      (let (prev2 (Box Int) (S (box 1)))
                        (let (prev1 (Box Int) (S (box 1)))
                          (letrec (loop (→ Int Int)
                                  (S (λ (n Int)
                                       (let (curr Int (S (+ (unbox prev1) (unbox prev2))))
                                         (if (= n 0)
                                           curr
                                           (let (blah Int (S (set-box! prev2 (unbox prev1))))
                                             (let (bb Int (S (set-box! prev1 curr)))
                                               (loop (- n 1)))))))))
                            (loop n)))))))))
         (fib 5)))))

  ;; TODO gradually typed fib

  (test-case "define-language"
    (check-pred e? (term 2))
    (check-pred e? (term (+ 1 1)))
    (check-pred e? (term (= x 1)))
    (check-pred e? (term (if (= x 1) 1 #false)))
    (check-pred e? (term (if #true 2 3)))
    (check-pred τ? (term (→ Int Int)))
    (check-pred τ? (term TST))
    (check-pred P? (term (R (if (= x 1) 1 #false))))
    (check-pred P? (term (R (λ (x TST) (if (= x 1) 1 #false)))))
    (check-pred P? (term (R (if 1 2 3))))
    (check-pred P? (term (R (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1)))))
    (check-pred e? (term (if 1 2 3)))
    (check-pred e? (term (box 4)))
    (check-pred e? (term (unbox x)))
    (check-pred e? (term (set-box! x 3)))
    (check-pred P? (term (S (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #f))) ((car ff) 4)))))
    (check-pred P? R-fib)
    (check-false (v? (term (box 3))))
    (check-pred P? (term (S (λ (x (Pair Int Int))
                              ((λ (x TST) x)
                               (dyn-check Pair x (x (Pair Int Int))))))))
    (check-pred τ/γ? (term (Int (car (x«107» (Pair Int Int))))))
    (check-pred τ/γ? (term (Int (cdr (x«107» (Pair Int Int))))))
    (check-pred τ/γ? (term ((Pair (Int (car (x«107» (Pair Int Int))))
                                  (Int (cdr (x«107» (Pair Int Int)))))
                            (x«107» (Pair Int Int)))))
    (check-false (τ/γ? (term ((Pair Int Int) •))))
    (check-pred τ/γ? (term ((→ ((Pair (Int •) (Int •)) •)
                               ((Pair (Int (car (x«107» (Pair Int Int))))
                                      (Int (cdr (x«107» (Pair Int Int)))))
                                (x«107» (Pair Int Int))))
                            •)))
    (check-pred srcloc? (term ((proj 0) (x (U Bool Int)))))
    (check-pred τ/γ? (term (Bool ((proj 0) (x (U Bool Int))))))
    (check-pred τ/γ? (term (Int ((proj 1) (x (U Bool Int))))))
    (check-pred τ/γ? (term ((U (Bool ((proj 0) (x (U Bool Int))))
                              (Int ((proj 1) (x (U Bool Int))))) •)))
    (check-pred τ/γ? (term (TST •)))
    (check-pred τ/γ? (term (TST (x TST))))
    (check-pred Γ/γ? (term ((x (TST (x TST))))))
    (check-pred P? (term (R x)))
    (check-pred e? (term (dyn-check Int 1 (x Int))))
    (check-pred e? (term ((λ (x) x) (dyn-check Int 1 (x Int)))))
  )
)

;; -----------------------------------------------------------------------------

(define-judgment-form μSR
  #:mode (well-typed I)
  #:contract (well-typed P)
  [
   (infer-type () P τ)
   ---
   (well-typed P)])

(define-judgment-form μSR
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) τ_actual)
   (type= TST τ_actual)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (S e) τ_actual)
   (subtype τ_actual τ)
   ---
   (check-type Γ (S e) τ)])

(define-judgment-form μSR
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P τ)
  [
   --- R-I-Int
   (infer-type Γ (R integer) TST)]
  [
   --- S-I-Int
   (infer-type Γ (S integer) Int)]
  [
   --- R-I-Bool
   (infer-type Γ (R boolean) TST)]
  [
   --- S-I-Bool
   (infer-type Γ (S boolean) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (cons e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   ---
   (infer-type Γ (S (cons e_0 e_1)) (Pair τ_0 τ_1))]
  [
   (infer-type Γ (R e) τ_e)
   ---
   (infer-type Γ (R (car e)) TST)]
  [
   (infer-type Γ (S e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (S (car e)) τ_0)]
  [
   (infer-type Γ (R e) τ)
   ---
   (infer-type Γ (R (cdr e)) TST)]
  [
   (infer-type Γ (S e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (S (cdr e)) τ_1)]
  [
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e) τ_cod)
   --- R-I-λ
   (infer-type Γ (R (λ (x TST) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (S e) τ_cod)
   --- S-I-λ
   (infer-type Γ (S (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   --- R-I-App
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   --- S-I-App
   (infer-type Γ (S (e_0 e_1)) τ_cod)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (R x) TST)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (S x) τ)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e_body) τ_body)
   --- R-I-Let
   (infer-type Γ (R (let (x τ P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (S e_body) τ_body)
   --- S-I-Let
   (infer-type Γ (S (let (x τ P) e_body)) τ_body)]
  [
   (where Γ_x #{type-env-set Γ (x τ)})
   (check-type Γ_x P τ)
   (infer-type Γ_x (R e_body) τ_body)
   --- R-I-LetRec
   (infer-type Γ (R (letrec (x τ P) e_body)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ)})
   (check-type Γ_x P τ)
   (infer-type Γ_x (S e_body) τ_body)
   --- S-I-LetRec
   (infer-type Γ (S (letrec (x τ P) e_body)) τ_body)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (binop e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (S (binop e_0 e_1)) Int)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (= e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (S (= e_0 e_1)) Bool)]
  [
   (infer-type Γ (R e) τ)
   --- R-I-Box
   (infer-type Γ (R (box e)) TST)]
  [
   (infer-type Γ (S e) τ) ;; no need to generalize
   --- S-I-Box
   (infer-type Γ (S (box e)) (Box τ))]
  [
   (infer-type Γ (R e) τ)
   --- R-I-MakeBox
   (infer-type Γ (R (make-box e)) TST)]
  [
   (infer-type Γ (S e) τ)
   --- S-I-MakeBox
   (infer-type Γ (S (make-box e)) (Box τ))]
  [
   (infer-type Γ (R e) τ)
   --- R-I-Unbox
   (infer-type Γ (R (unbox e)) TST)]
  [
   (infer-type Γ (S e) (Box τ))
   --- S-I-Unbox
   (infer-type Γ (S (unbox e)) τ)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   --- R-I-SetBox
   (infer-type Γ (R (set-box! e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (where (Box τ) τ_0)
   (type= τ τ_1)
   --- S-I-SetBox
   (infer-type Γ (S (set-box! e_0 e_1)) τ_1)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   (infer-type Γ (R e_2) τ_2)
   ---
   (infer-type Γ (R (if e_0 e_1 e_2)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (infer-type Γ (S e_2) τ_2)
   (where τ_3 #{make-union τ_1 τ_2})
   ---
   (infer-type Γ (S (if e_0 e_1 e_2)) τ_3)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (and e_0 e_1)) TST)]
  [
   (infer-type Γ (S e_0) τ_0)
   (infer-type Γ (S e_1) τ_1)
   (where τ_2 #{make-union τ_0 τ_1})
   ---
   (infer-type Γ (S (and e_0 e_1)) τ_2)]
  [
   (side-condition ,(raise-user-error 'infer-type "dyn-check not allowed in source terms ~a" (term (L (dyn-check tag e srcloc)))))
   ---
   (infer-type Γ (L (dyn-check tag e srcloc)) TST)]
)

(define-metafunction μSR
  check-type# : P τ -> boolean
  [(check-type# P τ)
   #true
   (judgment-holds (check-type () P τ))]
  [(check-type# P τ)
   #false])

(define-metafunction μSR
  infer-type# : P -> τ
  [(infer-type# P)
   τ
   (judgment-holds (infer-type () P τ))]
  [(infer-type# P)
   ,(raise-user-error 'infer-type# "failed to infer type for term ~a" (term P))])

(module+ test

  (test-case "check-type#"
    (check-true (term #{check-type# (R (if 1 2 3)) TST})))

  (test-case "infer-type#"
    (check-mf-apply*
     ((infer-type# (S (if (and #true #true) (+ 1 1) (+ 2 2))))
      Int)
     ((infer-type# (R (let (f TST (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (S (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)
     ((infer-type# (S (if 1 2 #false)))
      (U Bool Int))
    )
  )

  (test-case "well-typed"
    (check-judgment-holds*
     (well-typed (S (λ (x Int) 2)))
     (infer-type () (S (λ (x Int) 3)) (→ Int Int))
     (check-type () (S (λ (x Int) 3)) (→ Int Int))
     (well-typed (S (let (x Int (S 1)) (let (y Int (S 2)) (+ x y)))))
     (check-type () (S 1) Int)
     (check-type () (S 1) (U Int (Pair Int Int)))
     (well-typed (S (if 1 2 (cons 2 3))))
     (check-type () (S (and 1 #true)) (U Bool Int))
     (well-typed (S (if (λ (x Int) x) 1 0)))
     (well-typed (S (let (x Int (S 1)) (let (y Int (S 2)) (+ x y)))))
     (well-typed (S (let (h (→ Bool Bool)
                         (R (let (g (→ Int Int)
                                    (S (let (f (→ Int Int)
                                               (R (λ (x TST) x)))
                                         f)))
                              g)))
                   (h #true))))
     (well-typed (R (car (λ (x TST) x))))
     (well-typed (R (car 3)))
     (well-typed (R (car (cons 1 2))))
     (well-typed (S (car (cons 1 2))))
     (well-typed (S (λ (x Int) (+ x 1))))
     (well-typed (R (let (f (→ Int Int) (S (λ (x Int) (+ x 1)))) (f 3))))
     (well-typed (R (unbox 3)))
     (well-typed (R (+ 1 (make-box 3))))
     (well-typed (R (make-box (λ (x TST) (+ 2 2)))))
     (well-typed (S (make-box (λ (x Bool) (+ 2 2)))))
     (well-typed (S (+ 1 (unbox (box 4)))))
     (well-typed (S (+ 1 (unbox (make-box 4)))))
     (well-typed (S (let (x (Box Int) (R (box #true))) (+ 1 (unbox x)))))
     (well-typed (R (letrec (fact (→ Int Int) (R (λ (n TST) (if (= n 0) n (* n (fact (- n 1))))))) (fact 6))))
     (well-typed (S (letrec (fact (→ Int Int) (S (λ (n Int) (if (= n 0) n (* n (fact (- n 1))))))) (fact 6))))
     (well-typed (S (letrec (x (Box Int) (R (box 3))) x)))
     (well-typed (S (letrec (x (Box Int) (R (box 3)))
                      (let (y Int (S (set-box! x 4)))
                        y))))
     (well-typed (S (letrec (x (Box Int) (R (make-box 3)))
                      (let (y Int (S (set-box! x 4)))
                        y))))
     (well-typed (S (letrec (x (Box Int) (R (box 3)))
                      (let (y Int (S (set-box! x 4)))
                        (+ y (unbox x))))))
     (well-typed ,R-fib)
     (well-typed ,S-fib)
    )

    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (R (dyn-check Int 3 (x Int)))))))
    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (S (dyn-check → (λ (x Int) 3) (f Int)))))))

  )

  (test-case "not-well-typed"
    (check-not-judgment-holds*
     (well-typed (S (car 1)))
     (well-typed (S (set-box! 1 1)))
     (well-typed (S (unbox (λ (x Int) x))))
     (well-typed (S (unbox 1)))
     (well-typed (S (set-box! (box 0) (box 4))))
     (well-typed (S (let (b (Box Int) (R (box 1))) (set-box! b #false))))
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- evalution

(define -->μSR
  (reduction-relation μSR
    #:domain A
;; -- APP
    [-->
     [ρ (in-hole E ((λ (x) e) v_1))]
     [ρ (in-hole E (substitute e x v_1))]
     App-Beta]
;; -- BOX
    [-->
     [ρ (in-hole E (make-box v))]
     [ρ_x (in-hole E (box x_loc))]
     Make-Box
     (fresh x_loc)
     (where ρ_x #{runtime-env-set ρ x_loc (BOX v)})]
    [-->
     [ρ (in-hole E (unbox (box x)))]
     [ρ (in-hole E v)]
     Unbox
     (where (BOX v) #{runtime-env-ref-box ρ x})]
    [-->
     [ρ (in-hole E (set-box! (box x) v))]
     [ρ_v (in-hole E v)]
     SetBox
     (where ρ_v #{runtime-env-update-box ρ x v})]
;; -- LET/REC
    [-->
     [ρ (in-hole E (let (x v) e))]
     [ρ (in-hole E (substitute e x v))]
     Let]
    [-->
     [ρ (in-hole E (letrec (x τ e_x) e))] ;; TODO the τ doesn't matter, it's just a "start" marker
     [ρ_x (in-hole E (letrec (x_self (substitute e_x x (REC x_self)))
                       (substitute e x (REC x_self))))]
     LetRec-Init
     (fresh x_self)
     (where ρ_x #{runtime-env-set ρ x_self UNDEF})]
    [-->
     [ρ (in-hole E (letrec (x v) e))]
     [ρ_x (in-hole E e)]
     LetRec-End
     (where ρ_x #{runtime-env-update-rec ρ x v})]
    [-->
     [ρ (in-hole E (REC x))]
     [ρ (in-hole E v)]
     LetRec-Var
     (where v #{runtime-env-ref-rec ρ x})]
    [-->
     [ρ (in-hole E (REC x))]
     (UndefError x)
     LetRec-Error
     (where UNDEF #{runtime-env-ref-rec ρ x})]
;; -- AND / IF
    [-->
     [ρ (in-hole E (and v_0 e_1))]
     [ρ (in-hole E e_1)]
     And-True
     (judgment-holds (truthy v_0))]
    [-->
     [ρ (in-hole E (and #false e_1))]
     [ρ (in-hole E #false)]
     And-False]
    [-->
     [ρ (in-hole E (if v e_1 e_2))]
     [ρ (in-hole E e_1)]
     If-True
     (judgment-holds (truthy v))]
    [-->
     [ρ (in-hole E (if #false e_1 e_2))]
     [ρ (in-hole E e_2)]
     If-False]
;; -- primop
    [-->
     [ρ (in-hole E (primop v ...))]
     [ρ (in-hole E #{apply-op primop v ...})]
     Primop] ;; no need to check because well-typed or dyn-check'd
;; -- dyn-check
    [-->
     [ρ (in-hole E (dyn-check tag v srcloc))]
     [ρ (in-hole E v)]
     DynCheck-Ok
     (judgment-holds (well-tagged v tag))]
    [-->
     [ρ (in-hole E (dyn-check tag v srcloc))]
     (DynError tag v srcloc)
     DynCheck-Error
     (side-condition (not (judgment-holds (well-tagged v tag))))]))

(define -->μSR*
  (make--->* -->μSR))

(define-metafunction μSR
  eval : P  -> any
  [(eval P)
   #{eval* P #false}])

(define-metafunction μSR
  eval* : P boolean -> any
  [(eval* P boolean_keeptrace)
   any
   (judgment-holds (well-typed P))
   (where P_c #{completion# P})
   (where e_c #{erasure# P_c})
   (where any_init #{load e_c})
   (where any ,(if (term boolean_keeptrace)
                 (apply-reduction-relation* -->μSR (term any_init) #:all? #t)
                 (let ([final (-->μSR* (term any_init))])
                 (when (*debug*) (printf "FINAL STATE ~a~n" final))
                   (term #{unload ,final}))))]
  [(eval* P boolean_keeptrace)
   ,(raise-user-error 'eval "trouble eval'ing ~a" (term e_c))
   (judgment-holds (well-typed P))
   (where P_c #{completion# P})
   (where e_c #{erasure# P_c})]
  [(eval* P boolean_keeptrace)
   ,(raise-user-error 'eval "trouble erasing let from ~a" (term P_c))
   (judgment-holds (well-typed P))
   (where P_c #{completion# P})]
  [(eval* P _)
   ,(raise-user-error 'eval "trouble completing ~a" (term P))
   (judgment-holds (well-typed P))]
  [(eval* P _)
   ,(raise-user-error 'eval "typechecking failed ~a" (term P))])

(define-metafunction μSR
  load : e -> [ρ e]
  [(load e)
   (#{runtime-env-init} e)])

(define-metafunction μSR
  unload : any -> any
  [(unload RuntimeError)
   RuntimeError]
  [(unload [ρ v])
   (runtime-env-unload ρ v)]
  [(unload [ρ e])
   ,(raise-arguments-error 'unload "tried to unload non-value (evaluation got stuck?)"
     "non-value" (term e)
     "env" (term ρ))])

(module+ test
  (test-case "eval:R:I"
    ;; simplest terms, R language
    (check-mf-apply*
     ((eval (R (if 1 2 3)))
      2)
     ((eval (R (if #false 2 3)))
      3)
     ((eval (R (if #true 2 3)))
      2)
     ((eval (R (and 1 2)))
      2)
     ((eval (R (and #true 3)))
      3)
     ((eval (R (and #true #false)))
      #false)
     ((eval (R (and #false #true)))
      #false)
     ((eval (R (and #true #true)))
      #true)
     ((eval (R (= 1 1)))
      #true)
     ((eval (R (= 1 2)))
      #false)
     ((eval (R (= #true 2)))
      (DynError Int #true (dom (= (→ Int (→ Int Bool))))))
     ((eval (R (= 3 (= 1 1))))
      (DynError Int #true (dom (cod (= (→ Int (→ Int Bool)))))))
     ((eval (R (+ 2 2)))
      4)
     ((eval (R (+ #true 2)))
      (DynError Int #true (dom (+ (→ Int (→ Int Int))))))
     ((eval (R (+ 2 #true)))
      (DynError Int #true (dom (cod (+ (→ Int (→ Int Int)))))))
     ((eval (R (cons 1 2)))
      (cons 1 2))
     ((eval (R (+ 1 (car (cons (+ 1 1) (+ 2 2))))))
      3)
     ((eval (R (+ 1 (cdr (cons (+ 1 1) (+ 2 2))))))
      5)
     ((eval (R ((car (cons (λ (x TST) (+ x 1)) 4)) 8)))
      9)
     ((eval (R (unbox (box 3))))
      3)
     ((eval (R (set-box! (box 3) 4)))
      4)
     ((eval (R (box 3)))
      (box 3))
     ((eval (R (set-box! (box 0) (box 4))))
      (box 4))
    )
  )

  (test-case "eval:R:II"
    (check-mf-apply*
      ((eval (R (let (n1 TST (R #false)) n1)))
       #false)
      ((eval (R (let (n1 TST (R (+ 2 2))) (+ n1 n1))))
       8)
      ((eval (R ((λ (x TST) (+ x 1)) 1)))
       2)
      ((eval (R (1 1)))
       (DynError → 1 (#%app (→ TST TST))))
      ((eval (R (let (b TST (R (box 3)))
                  (let (f TST (R (λ (x TST) (unbox b))))
                    (let (dontcare TST (R (set-box! b 4)))
                      (f 1))))))
       4)
    )
  )

  (test-case "eval:simple:S"
    (check-mf-apply*
     [(eval (S 4))
      4]
     ((eval (S (if (and #true (= 4 2)) (+ 1 1) (+ 2 2))))
      4)
     [(eval (S #true))
      #true]
     [(eval (S (+ 2 2)))
      4]
     [(eval (S ((λ (x Int) x) 1)))
      1]
     [(eval (S ((λ (x Int) (+ x 1)) 1)))
      2]
     [(eval (S (if ((λ (x Bool) x) #true) 1 0)))
      1]
     [(eval (S (if #false (+ 6 6) 0)))
      0]
     [(eval (S (let (x Int (S 1))
                 (let (y Int (S 2))
                   (+ x y)))))
      3]
     [(eval (S (let (negate (→ Bool Bool) (S (λ (x Bool) (if x #false #true))))
                 (let (b Bool (S #false))
                   (negate (negate b))))))
      #false]
     [(eval (S (let (x Int (S 4))
                 (let (add-x (→ Int Int) (S (λ (y Int) (+ y x))))
                   (let (x Int (S 5))
                     (add-x x))))))
      9]
     [(eval (S (cons (+ 2 2) (+ 1 1))))
      (cons 4 2)]
     [(eval (S (+ 2 (cdr (cons #false 4)))))
      6]
     [(eval (S (unbox (box 3))))
      3]
     [(eval (S (set-box! (box 3) 4)))
      4]
     [(eval (S (if (λ (x (Box Int)) x) 1 0)))
      1]
    )
  )

  (test-case "eval:simple:S:fail"
    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (S ((λ (x Int) (+ x 1)) #false))})))

    (check-exn #rx"typechecking failed"
      (λ () (term (eval (S (let (x Bool (S (+ 2 5))) x)))))))

  (test-case "apply-R-in-S"
    (check-mf-apply*
     [(eval (S (let (f (→ Int Int) (R (λ (x TST) (+ x 1))))
                 (f 3))))
      4]
     [(eval (S (let (f (→ Int Bool) (R (λ (x TST) (if (= 0 x) #false #true))))
                 (f 3))))
      #true]
     [(eval (S (let (f (→ Int Int) (R (λ (x TST) #false))) (f 1))))
      (DynError Int #false (cod (f (→ Int Int))))]
     [(eval (S (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError Int #f (dom (cod (+ (→ Int (→ Int Int))))))]
     [(eval (S (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError Int #t (dom (+ (→ Int (→ Int Int)))))]
     [(eval (S (let (f (→ Int (Box Int)) (R (λ (x TST) (box x))))
                 (f 3))))
      (box 3)]
     ((eval (S (let (f (→ Int Int) (R (λ (x TST) #false))) (f 3))))
      (DynError Int #false (cod (f (→ Int Int)))))
     ((eval (S (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError Int #false (dom (cod (+ (→ Int (→ Int Int)))))))
     ((eval (S (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError Int #true (dom (+ (→ Int (→ Int Int))))))
    )
  )

  (test-case "apply-S-in-R"
    (check-mf-apply*
     [(eval (R (let (f (→ Int Int) (S (λ (x Int) (+ x 1)))) (f 3))))
      4]
     [(eval (R (let (f (→ Int Bool) (S (λ (x Int) (if (= 0 x) #false #true)))) (f 3))))
      #true]
     [(eval (R (let (f (→ Int Int) (S (λ (x Int) (+ x 4)))) (f #true))))
      (DynError Int #true (x Int))]
    )

    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (R (let (f (→ Int Int) (S (λ (x Int) #false))) (f 1)))})))
  )

  (test-case "eval:box"
    (check-mf-apply*
     ((eval (R (let (x TST (R (box 3))) 0)))
       0)
     ((eval (R (let (x TST (R (box 3))) x)))
      (box 3))
     ((eval (R (letrec (x TST (R (box 3))) x)))
      (box 3))
     ((eval (R (let (x TST (R (box 3))) (unbox x))))
      3)
     ((eval (R (let (x TST (R (box 3))) (+ 1 (unbox x)))))
      4)
     ((eval (R (let (x TST (R (box 3)))
                (let (z TST (R (unbox x)))
                 (let (y TST (R (set-box! x 4)))
                   (+ z (unbox x)))))))
      7)
     ((eval (S (let (x (Box Int) (R (make-box 3)))
                 (let (y Int (S (set-box! x 4)))
                   (+ y (unbox x))))))
      8)
     ((eval (S (letrec (x (Box Int) (R (box 3)))
                 (let (y Int (S (set-box! x 4)))
                   (+ y (unbox x))))))
      8)
    )

  )

  (test-case "eval:R:III"
    (check-mf-apply*
     ((eval (R (letrec (fact TST (R (λ (n TST) (if (= 0 n) 1 (* n (fact (- n 1))))))) (fact 6))))
      720)
     ((eval ,R-fib)
      8)
    )
  )

  (test-case "double-wrap"
    (check-mf-apply*
     ((eval (S (let (h (→ Bool Bool)
                       (R (let (g (→ Int Int)
                                  (S (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h #true))))
      #true) ;; different from T
     ((eval (S (let (h (→ Int Int)
                       (R (let (g (→ Int Int)
                                  (S (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h 5))))
      5)))

  (test-case "more-R-in-S"
    (check-mf-apply*
     ((eval (S (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #false)))
                 ((car ff) 4))))
      8)
     ((eval (S (let (ff (Pair (→ Bool Bool) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      #false)
     ((eval (S (let (ff (Pair (→ Bool Int) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      (DynError Int #false (cod (car (ff (Pair (→ Bool Int) Bool))))))
     ((eval (S (let (ff (→ Int (U Bool Int)) (R (λ (x TST) (if (= x 0) #false x))))
                 (let (gg (→ (U Bool Int) Int) (R (λ (x TST) 900)))
                   (+ (gg (ff 0))
                      (gg (ff 1)))))))
      1800)
    )
  )

  (test-case "boxof-R-in-S"
    (check-mf-apply*
     ((eval (S (let (b (Box Int) (R (box 1)))
                 (let (_dontcare Int (S (set-box! b 2)))
                   (unbox b)))))
      2)
     ((eval (S (let (b (Box Int) (R (box #false)))
                   0)))
      0)
    )
  )

  (test-case "boxof-S-in-R"
    (check-mf-apply*
     [(eval (R (let (b (Box Int) (S (box 1)))
                 (unbox b))))
      1]
     [(eval (R (let (b (Box Int) (S (box 1)))
                 (set-box! b 4))))
      4]
     [(eval (R (let (bb (Box (Box Int)) (S (box (box 1))))
                 (let (_dontcare Int (R (set-box! (unbox bb) 777)))
                   (unbox (unbox bb))))))
      777]
     [(eval (R (let (b (Box Int) (S (box 1)))
                 (set-box! b #f))))
      #f]
     [(eval (R (let (b (Box Int) (S (box 1)))
                 (let (u TST (R (set-box! b #f)))
                   (unbox b)))))
      #f]
     [(eval (R (let (bb (Box (Box Int)) (S (box (box 1))))
                 (let (_dontcare Bool (R (set-box! (unbox bb) #false)))
                   (unbox (unbox bb))))))
      #f]
    )
  )

  (test-case "box:error"
    (check-mf-apply*
     ((eval (S (let (x (Box Int) (R 42)) #false)))
      (DynError Box 42 (x (Box Int))))
     ((eval (S (let (x (Box Int) (R (box #true))) #false)))
      #false)
     ((eval (S (let (x (Box Int) (R (box #true))) (unbox x))))
      (DynError Int #true (unbox (x (Box Int)))))
    )
  )

  (test-case "well-typed-programs-run-faster"
    (define (check-shorter-trace t1 t2)
      (define-values [trace1 trace2]
          (values (term #{eval* ,t1 #true}) (term #{eval* ,t2 #true})))
      (check < (length trace1) (length trace2)))

    (check-shorter-trace (term (S (+ 2 2))) (term (R (+ 2 2))))
  )
)

;; =============================================================================
;; === less interesting from here on
;; =============================================================================

;; -----------------------------------------------------------------------------
;; --- type helpers

(define-judgment-form μSR
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   (side-condition ,(α=? (term #{type-normalize τ_0}) (term #{type-normalize τ_1})))
   --- Refl
   (type= τ_0 τ_1)])

(define-metafunction μSR
  type-normalize : τ -> τ
  [(type-normalize τk)
   τk]
  [(type-normalize TST)
   TST]
  [(type-normalize (U τk ...))
   ,(let ((kk (sort/deduplicate (term (τk ...)) symbol<? #:key simple-type->constructor)))
      (cond
       [(null? kk)
        (term (U))]
       [(null? (cdr kk))
        (car kk)]
       [else
        (cons (term U) kk)]))])

(define (simple-type->constructor t)
  (unless (τk? t)
    (raise-argument-error 'simple-type->constructor "simple type" t))
  (cond
   [(symbol? t)
    t]
   [(pair? t)
    (car t)]
   [else
    (raise-user-error 'simple-type->constructor "undefined for type ~a" t)]))

(define (sort/deduplicate t* <? #:key get-key)
  (let loop ([t* (sort t* <? #:key get-key)])
    (cond
     [(or (null? t*) (null? (cdr t*)))
      t*]
     [(equal? (car t*) (cadr t*)) ;; TODO not great (but also not horrible)
      (loop (cdr t*))]
     [else
      (cons (car t*) (loop (cdr t*)))])))

(define-judgment-form μSR
  #:mode (subtype I I)
  #:contract (subtype τ τ)
  [
   --- Refl
   (subtype τ τ)]
  [
   (subtype τ_dom1 τ_dom0)
   (subtype τ_cod0 τ_cod1)
   --- Arrow
   (subtype (→ τ_dom0 τ_cod0) (→ τ_dom1 τ_cod1))]
  [
   (type= τ_0 τ_1)
   --- Box
   (subtype (Box τ_0) (Box τ_1))]
  [
   (subtype τ_lhs τ_rhs)
   --- U-Member
   (subtype τ_lhs (U τ_0 ... τ_rhs τ_1 ...))]
  [
   --- U-Empty
   (subtype (U) (U τ ...))]
  [
   (subtype τ_lhs τ_rhs)
   (subtype (U τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))
   ---
   (subtype (U τ_lhs τ_0 ...) (U τ_1 ... τ_rhs τ_2 ...))])

(define-metafunction μSR
  make-union : τ τ -> τ
  [(make-union TST τ)
   ,(raise-argument-error 'make-union "cannot make union with TST" 0 (term TST) (term τ))]
  [(make-union τ TST)
   ,(raise-argument-error 'make-union "cannot make union with TST" 1 (term τ) (term TST))]
  [(make-union τk_0 τ)
   (make-union (U τk_0) τ)]
  [(make-union τ τk_1)
   (make-union τ (U τk_1))]
  [(make-union (U τ_0 ...) (U τ_1 ...))
   #{type-normalize (U τ_0 ... τ_1 ...)}])

(define-judgment-form μSR
  #:mode (well-tagged I I)
  #:contract (well-tagged v tag)
  [
   --- Tag-Int
   (well-tagged integer Int)]
  [
   --- Tag-Bool
   (well-tagged boolean Bool)]
  [
   --- Tag-→
   (well-tagged Λ →)]
  [
   --- Tag-Box
   (well-tagged (box _) Box)]
  [
   --- Tag-Pair
   (well-tagged (cons _ _) Pair)]
  [
   (well-tagged v tagk) ;; pick one winner
   --- Tag-U
   (well-tagged v (U tagk_0 ... tagk tagk_1 ...))])

(define-judgment-form μSR
  #:mode (tag= I I)
  #:contract (tag= tag tag)
  [
   ---
   (tag= tag tag)])

(module+ test

  (test-case "simple-type->constructor"
    (check-apply* simple-type->constructor
     ((term Int)
      ==> 'Int)
     ((term Bool)
      ==> 'Bool)
     ((term (Pair Int Int))
      ==> 'Pair)
     ((term (Box Int))
      ==> 'Box)
     ((term (Box (→ Int Int)))
      ==> 'Box)
     ((term (→ Int Int))
      ==> '→)))

  (test-case "type-normalize"
    (check-mf-apply*
     ((type-normalize (U Int Int))
      Int)
     ((type-normalize (U Int Bool))
      (U Bool Int))
     ((type-normalize (U Int Int (Pair Int Int) (Pair Bool Int)))
      (U Int (Pair Int Int) (Pair Bool Int)))
     ((type-normalize (U (Pair Int Int) (Pair Int Int) Int))
      (U Int (Pair Int Int)))))

  (test-case "well-tagged"
    (check-judgment-holds*
     (well-tagged 4 Int)
     (well-tagged #true Bool)
     (well-tagged (λ (x TST) 4) →)
     (well-tagged (cons 1 1) Pair)
     (well-tagged (box x) Box)
     (well-tagged (box y) Box)
     (well-tagged (box z) (U Box Pair))
     (well-tagged 4 (U → Bool Int))
     (well-tagged (cons 1 1) (U Bool Int Pair))
    )
    (check-not-judgment-holds*
     (well-tagged 3 (U Bool Box Pair))
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- environment helpers

(define-metafunction μSR
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction μSR
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

(define-metafunction μSR
  src-env-set : Γ/γ (x τ/γ) -> Γ/γ
  [(src-env-set Γ/γ (x τ/γ))
   ,(cons (term (x τ/γ)) (term Γ/γ))])

(define-metafunction μSR
  src-env-ref : Γ/γ x -> any
  [(src-env-ref Γ/γ x)
   ,(for/first ([xτ (in-list (term Γ/γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

(define-metafunction μSR
  runtime-env-init : -> ρ
  [(runtime-env-init)
   ()])

(define-metafunction μSR
  runtime-env-set : ρ x any -> ρ
  [(runtime-env-set ρ x (BOX v))
   ,(cons (term (x (BOX v))) (term ρ))]
  [(runtime-env-set ρ x UNDEF)
   ,(cons (term (x UNDEF)) (term ρ))])

(define-metafunction μSR
  runtime-env-ref : ρ x -> any
  [(runtime-env-ref () x)
   ,(raise-user-error 'runtime-env-ref "unbound variable ~a" (term x))]
  [(runtime-env-ref ((x (BOX v)) RB ...) x)
   (BOX v)]
  [(runtime-env-ref ((x UNDEF) RB ...) x)
   UNDEF]
  [(runtime-env-ref ((x (LETREC v)) RB ...) x)
   (LETREC v)]
  [(runtime-env-ref (RB_0 RB_1 ...) x)
   (runtime-env-ref (RB_1 ...) x)])

(define-metafunction μSR
  runtime-env-ref-box : ρ x -> (BOX v)
  [(runtime-env-ref-box ρ x)
   (BOX v)
   (where (BOX v) #{runtime-env-ref ρ x})]
  [(runtime-env-ref-box ρ x)
   ,(raise-arguments-error 'runtime-env-ref-box "bad location in box"
      "location" (term x)
      "value" (term #{runtime-env-ref ρ x})
      "env" (term ρ))])

(define-metafunction μSR
  runtime-env-ref-rec : ρ x -> any
  [(runtime-env-ref-rec ρ x)
   v
   (where (LETREC v) #{runtime-env-ref ρ x})]
  [(runtime-env-ref-rec ρ x)
   UNDEF
   (where UNDEF #{runtime-env-ref ρ x})]
  [(runtime-env-ref-rec ρ x)
   ,(raise-arguments-error 'runtime-env-ref-rec "bad recursive binding"
      "var" (term x)
      "value" (term #{runtime-env-ref ρ x})
      "env" (term ρ))])

(define-metafunction μSR
  runtime-env-update : ρ x v -> ρ
  [(runtime-env-update (RB_0 ... (x UNDEF) RB_1 ...) x v)
   (RB_0 ... (x (LETREC v)) RB_1 ...)]
  [(runtime-env-update (RB_0 ... (x (BOX v_x)) RB_1 ...) x v)
   (RB_0 ... (x (BOX v)) RB_1 ...)]
  [(runtime-env-update ρ x v)
   ,(raise-arguments-error 'runtime-env-ref "unbound variable" "var" (term x) "env" (term ρ))])

(define-metafunction μSR
  runtime-env-update-box : ρ x v -> ρ
  [(runtime-env-update-box ρ x v)
   #{runtime-env-update ρ x v}
   (where (BOX v_x) #{runtime-env-ref-box ρ x})]
  [(runtime-env-update-box ρ x v)
   ,(raise-arguments-error 'runtime-env-update "bad location"
     "location" (term x)
     "value" (term #{runtime-env-ref ρ x})
     "env" (term ρ))])

(define-metafunction μSR
  runtime-env-update-rec : ρ x v -> ρ
  [(runtime-env-update-rec ρ x v)
   #{runtime-env-update ρ x v}
   (where UNDEF #{runtime-env-ref-rec ρ x})]
  [(runtime-env-update-rec ρ x v)
   ,(raise-arguments-error 'runtime-env-update "bad rec binding"
     "var" (term x)
     "value" (term #{runtime-env-ref ρ x})
     "env" (term ρ))])

;; Hmm, using `any` because `(box v)` rather than `(box x)`
(define-metafunction μSR
  runtime-env-unload : ρ any -> any
  [(runtime-env-unload () any)
   any]
  [(runtime-env-unload ((x (BOX v_x)) RB ...) any)
   (runtime-env-unload (RB ...) (substitute any x v_x))]
  [(runtime-env-unload ((x (LETREC v_x)) RB ...) any)
   (runtime-env-unload (RB ...) any)])

(module+ test
  (test-case "runtime-env"
    (check-pred ρ? (term #{runtime-env-init}))
  )
)

;; -----------------------------------------------------------------------------
;; --- flat types

;; `(flat L τ)` iff `τ` is strictly positive and `L` fully-checks values with type `τ`
(define-judgment-form μSR
  #:mode (flat I I)
  #:contract (flat L τ)
  [
   ---
   (flat L TST)]
  [
   ---
   (flat S Int)]
  [
   ---
   (flat S Bool)])

(define-judgment-form μSR
  #:mode (non-flat I I)
  #:contract (non-flat L τ)
  [
   (side-condition ,(not (judgment-holds (flat L τ))))
   ---
   (non-flat L τ)])

(module+ test
  (test-case "flat"
    (check-judgment-holds*
     (flat S Int)
     (flat S Bool)

     (non-flat R Int)
     (non-flat S (→ Bool Bool))
     (non-flat S (Pair Int Int))
    )

    (check-not-judgment-holds*
     (flat R Int)
     (flat S (→ Bool Bool))
     (flat S (Pair Int (Pair (→ Int Int) Int)))

     (non-flat S Int)
     (non-flat S Bool)
    )
  )
)

;; -----------------------------------------------------------------------------

(define-judgment-form μSR
  #:mode (proc? I)
  #:contract (proc? v)
  [
   ---
   (proc? (λ (x τ) e))])

(define-judgment-form μSR
  #:mode (cons? I)
  #:contract (cons? v)
  [
   ---
   (cons? (cons e_0 e_1))])

(define-metafunction μSR
  tag-only : τ -> tag
  [(tag-only Int)
   Int]
  [(tag-only Bool)
   Bool]
  [(tag-only (Pair τ_0 τ_1))
   Pair]
  [(tag-only (→ τ_dom τ_cod))
   →]
  [(tag-only (Box τ))
   Box]
  [(tag-only (U τk ...))
   ,(cons (term U) (tagk-sort (term (#{tag-only τk} ...))))]
  [(tag-only TST)
   TST])

(define (tagk-sort tagk*)
  (sort tagk* symbol<?))

;; Add runtime checks to ensure safety
(define-judgment-form μSR
  #:mode (minimal-completion I O)
  #:contract (minimal-completion P P)
  [
   ---
   (minimal-completion (L integer) (L integer))]
  [
   ---
   (minimal-completion (L boolean) (L boolean))]
  [
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (λ (x τ) e)) (L (λ (x τ) e_c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   ---
   (minimal-completion (L (cons e_0 e_1)) (L (cons e_0c e_1c)))]
  [
   ---
   (minimal-completion (L x) (L x))]
  [
   (minimal-completion P P_c)
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (let (x τ P) e)) (L (let (x τ P_c) e_c)))]
  [
   (minimal-completion P P_c)
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (letrec (x τ P) e)) (L (letrec (x τ P_c) e_c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   (minimal-completion (L e_2) (L e_2c))
   ---
   (minimal-completion (L (if e_0 e_1 e_2)) (L (if e_0c e_1c e_2c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   (minimal-completion (L e_1) (L e_1c))
   ---
   (minimal-completion (L (and e_0 e_1)) (L (and e_0c e_1c)))]
  [
   (minimal-completion (L e) (L e_c))
   ---
   (minimal-completion (L (dyn-check tag e srcloc)) (L (dyn-check tag e_c srcloc)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-App
   (minimal-completion (R (e_0 e_1)) (R ((dyn-check → e_0c (#%app (→ TST TST))) e_1c)))]
  [
   (minimal-completion (S e_0) (S e_0c))
   (minimal-completion (S e_1) (S e_1c))
   --- S-App
   (minimal-completion (S (e_0 e_1)) (S (e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Car
   (minimal-completion (R (car e_0)) (R (car (dyn-check Pair e_0c (car (Pair TST TST))))))]
  [
   (minimal-completion (S e_0) (S e_0c))
   --- S-Car
   (minimal-completion (S (car e_0)) (S (car e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Cdr
   (minimal-completion (R (cdr e_0)) (R (cdr (dyn-check Pair e_0c (cdr (Pair TST TST))))))]
  [
   (minimal-completion (S e_0) (S e_0c))
   --- S-Cdr
   (minimal-completion (S (cdr e_0)) (S (cdr e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   (where srcloc (binop (→ Int (→ Int Int))))
   --- R-Binop
   (minimal-completion (R (binop e_0 e_1)) (R (binop (dyn-check Int e_0c (dom srcloc)) (dyn-check Int e_1c (dom (cod srcloc))))))]
  [
   (minimal-completion (S e_0) (S e_0c))
   (minimal-completion (S e_1) (S e_1c))
   --- S-Binop
   (minimal-completion (S (binop e_0 e_1)) (S (binop e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   (where srcloc (= (→ Int (→ Int Bool))))
   --- R-=
   (minimal-completion (R (= e_0 e_1)) (R (= (dyn-check Int e_0c (dom srcloc)) (dyn-check Int e_1c (dom (cod srcloc))))))]
  [
   (minimal-completion (S e_0) (S e_0c))
   (minimal-completion (S e_1) (S e_1c))
   --- S-=
   (minimal-completion (S (= e_0 e_1)) (S (= e_0c e_1c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   --- Box
   (minimal-completion (L (box e_0)) (L (box e_0c)))]
  [
   (minimal-completion (L e_0) (L e_0c))
   --- MakeBox
   (minimal-completion (L (make-box e_0)) (L (make-box e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Unbox
   (minimal-completion (R (unbox e_0)) (R (unbox (dyn-check Box e_0c (unbox (Box TST))))))]
  [
   (minimal-completion (S e_0) (S e_0c))
   --- S-Unbox
   (minimal-completion (S (unbox e_0)) (S (unbox e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-SetBox
   (minimal-completion (R (set-box! e_0 e_1)) (R (set-box! (dyn-check Box e_0c (set-box! (Box TST))) e_1c)))]
  [
   (minimal-completion (S e_0) (S e_0c))
   (minimal-completion (S e_1) (S e_1c))
   --- S-SetBox
   (minimal-completion (S (set-box! e_0 e_1)) (S (set-box! e_0c e_1c)))])

;; Input program is _well-typed_ and _type-annotated_
(define-judgment-form μSR
  #:mode (transient-completion I I O O)
  #:contract (transient-completion Γ/γ P P τ/γ)
  [
   --- TC-Int-R
   (transient-completion Γ/γ (R integer) (R integer) (TST •))]
  [
   --- TC-Int-S
   (transient-completion Γ/γ (S integer) (S integer) (Int •))]
  [
   --- TC-Bool-R
   (transient-completion Γ/γ (R boolean) (R boolean) (TST •))]
  [
   --- TC-Bool-S
   (transient-completion Γ/γ (S boolean) (S boolean) (Bool •))]
  [
   (where τ/γ #{src-env-ref Γ/γ x})
   ;; TODO should be bullet location? I do want to conclude TST
   --- TC-Var-R
   (transient-completion Γ/γ (R x) (R x) (TST •))]
  [
   (where τ/γ #{src-env-ref Γ/γ x})
   --- TC-Var-S
   (transient-completion Γ/γ (S x) (S x) τ/γ)]
  [
   (transient-completion Γ/γ (R e) (R e_c) τ/γ)
   --- TC-Box-R
   (transient-completion Γ/γ (R (box e)) (R (box e_c)) (TST •))]
  [
   (transient-completion Γ/γ (S e) (S e_c) τ/γ)
   --- TC-Box-S
   (transient-completion Γ/γ (S (box e)) (S (box e_c)) ((Box τ/γ) •))]
  [
   (transient-completion Γ/γ (R e_0) (R e_0tc) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1tc) τ/γ_1)
   --- TC-Cons-R
   (transient-completion Γ/γ (R (cons e_0 e_1)) (R (cons e_0tc e_1tc)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0tc) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1tc) τ/γ_1)
   --- TC-Cons-S
   (transient-completion Γ/γ (S (cons e_0 e_1)) (S (cons e_0tc e_1tc)) ((Pair τ/γ_0 τ/γ_1) •))]
  [
   (where Γ/γ_x #{src-env-set Γ/γ (x #{add-srcloc τ_dom (x τ_dom)})})
   (transient-completion Γ/γ_x (R e) (R e_c) τ/γ_cod)
   --- TC-λ-R
   (transient-completion Γ/γ (R (λ (x τ_dom) e)) (R (λ (x τ_dom) e_c)) (TST •))]
  [
   (where srcloc_x (#{xerox x} τ_dom))
   (where τ/γ_dom #{add-srcloc τ_dom srcloc_x})
   (where Γ/γ_x #{src-env-set Γ/γ (x τ/γ_dom)})
   (transient-completion Γ/γ_x (S e) (S e_c) τ/γ_cod)
   (where tag #{tag-only τ_dom})
   (where e_c+ ((λ (x TST) e_c) (dyn-check tag x srcloc_x)))
   --- TC-λ-S
   (transient-completion Γ/γ (S (λ (x τ_dom) e)) (S (λ (x τ_dom) e_c+)) ((→ τ/γ\_dom τ/γ_cod) •))]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   --- TC-App-R
   (transient-completion Γ/γ (R (e_0 e_1)) (R (e_0c e_1c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (where ((→ τ/γ_dom τ/γ_cod) srcloc_0) τ/γ_0)
   (where tag #{tag-only #{remove-srcloc τ/γ_cod}})
   (where e_c (dyn-check tag (e_0c e_1c) (cod srcloc_0)))
   --- TC-App-S
   (transient-completion Γ/γ (S (e_0 e_1)) (S e_c) τ/γ_cod)]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   (transient-completion Γ/γ (R e_2) (R e_2c) τ/γ_2)
   --- TC-If-R
   (transient-completion Γ/γ (R (if e_0 e_1 e_2)) (R (if e_0c e_1c e_2c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (transient-completion Γ/γ (S e_2) (S e_2c) τ/γ_2)
   (where τ/γ_3 ((U τ/γ_1 τ/γ_2) •))
   --- TC-If-S
   (transient-completion Γ/γ (S (if e_0 e_1 e_2)) (S (if e_0c e_1c e_2c)) τ/γ_3)]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   --- TC-And-R
   (transient-completion Γ/γ (R (and e_0 e_1)) (R (and e_0c e_1c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (where τ/γ_2 ((U τ/γ_0 τ/γ_1) •))
   --- TC-And-S
   (transient-completion Γ/γ (S (and e_0 e_1)) (S (and e_0c e_1c)) τ/γ_2)]
  [
   (transient-completion Γ/γ P P_c τ/γ_x)
   (where srcloc_x (#{xerox x} τ))
   (where Γ/γ_x #{src-env-set Γ/γ (x #{add-srcloc τ srcloc_x})}) ;; Use annotation type, not inferred type
   (transient-completion Γ/γ_x (R e) (R e_c) τ/γ_e)
   --- TC-Let-R
   (transient-completion Γ/γ (R (let (x τ P) e)) (R (let (x τ P_c) e_c)) (TST •))]
  [
   (transient-completion Γ/γ P P_c τ/γ_x)
   (where srcloc_x (#{xerox x} τ))
   (where Γ/γ_x #{src-env-set Γ/γ (x #{add-srcloc τ srcloc_x})})
   (transient-completion Γ/γ_x (S e) (S e_c) τ/γ_e)
   (where tag #{tag-only τ})
   (where e_c+ ,(if (equal? 'R (car (term P))) ;; TODO helper function
                  (term ((λ (x TST) e_c) (dyn-check tag x srcloc_x)))
                  (term e_c)))
   --- TC-Let-S
   (transient-completion Γ/γ (S (let (x τ P) e)) (S (let (x τ P_c) e_c+)) τ/γ_e)]
  [
   (where srcloc_x (#{xerox x} τ))
   (where Γ/γ_x #{src-env-set Γ/γ (x #{add-srcloc τ srcloc_x})})
   (transient-completion Γ/γ_x P P_c τ/γ_x)
   (transient-completion Γ/γ_x (R e) (R e_c) τ/γ_e)
   --- TC-LetRec-R
   (transient-completion Γ/γ (R (letrec (x τ P) e)) (R (letrec (x τ P_c) e_c)) (TST •))]
  [
   (where srcloc_x (#{xerox x} τ))
   (where Γ/γ_x #{src-env-set Γ/γ (x #{add-srcloc τ srcloc_x})})
   (transient-completion Γ/γ_x P P_c τ/γ_x)
   (transient-completion Γ/γ_x (S e) (S e_c) τ/γ_e)
   (where tag #{tag-only τ})
   (where e_c+ ,(if (equal? 'R (car (term P)))
                  (term ((λ (x TST) e_c) (dyn-check tag x srcloc_x)))
                  (term e_c)))
   --- TC-LetRec-S
   (transient-completion Γ/γ (S (letrec (x τ P) e)) (S (letrec (x τ P_c) e_c+)) τ/γ_e)]
  [
   (transient-completion Γ/γ (R e) (R e_c) τ/γ)
   --- TC-Car-R
   (transient-completion Γ/γ (R (car e)) (R (car e_c)) (TST •))]
  [
   (transient-completion Γ/γ (S e) (S e_c) τ/γ)
   (where ((Pair τ/γ_car τ/γ_cdr) _) τ/γ)
   (where tag #{tag-only #{remove-srcloc τ/γ_car}})
   (where srcloc #{get-srcloc τ/γ_car})
   --- TC-Car-S
   (transient-completion Γ/γ (S (car e)) (S (dyn-check tag (car e_c) srcloc)) τ/γ_car)]
  [
   (transient-completion Γ/γ (R e) (R e_c) τ/γ)
   --- TC-Cdr-R
   (transient-completion Γ/γ (R (cdr e)) (R (cdr e_c)) (TST •))]
  [
   (transient-completion Γ/γ (S e) (S e_c) τ/γ)
   (where ((Pair τ/γ_car τ/γ_cdr) _) τ/γ)
   (where tag #{tag-only #{remove-srcloc τ/γ_cdr}})
   (where srcloc #{get-srcloc τ/γ_cdr})
   --- TC-Cdr-S
   (transient-completion Γ/γ (S (cdr e)) (S (dyn-check tag (cdr e_c) srcloc)) τ/γ_cdr)]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   --- TC-Binop-R
   (transient-completion Γ/γ (R (binop e_0 e_1)) (R (binop e_0c e_1c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (type= #{remove-srcloc τ/γ_0} Int)
   (type= #{remove-srcloc τ/γ_1} Int)
   --- TC-Binop-S
   (transient-completion Γ/γ (S (binop e_0 e_1)) (S (binop e_0c e_1c)) (Int •))]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   --- TC-=-R
   (transient-completion Γ/γ (R (= e_0 e_1)) (R (= e_0c e_1c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (type= #{remove-srcloc τ/γ_0} Int)
   (type= #{remove-srcloc τ/γ_1} Int)
   --- TC-=-S
   (transient-completion Γ/γ (S (= e_0 e_1)) (S (= e_0c e_1c)) (Bool •))]
  [
   (transient-completion Γ/γ (R e) (R e_c) τ/γ)
   --- TC-Unbox-R
   (transient-completion Γ/γ (R (unbox e)) (R (unbox e_c)) (TST •))]
  [
   (transient-completion Γ/γ (S e) (S e_c) τ/γ_e)
   (where ((Box τ/γ_unbox) _) τ/γ_e)
   (where tag #{tag-only #{remove-srcloc τ/γ_unbox}})
   (where srcloc #{get-srcloc τ/γ_unbox})
   --- TC-Unbox-S
   (transient-completion Γ/γ (S (unbox e)) (S (dyn-check tag (unbox e_c) srcloc)) τ/γ_unbox)]
  [
   (transient-completion Γ/γ (L (box e)) (L (box e_c)) τ/γ)
   --- TC-MakeBox
   (transient-completion Γ/γ (L (make-box e)) (L (make-box e_c)) τ/γ)]
  [
   (transient-completion Γ/γ (R e_0) (R e_0c) τ/γ_0)
   (transient-completion Γ/γ (R e_1) (R e_1c) τ/γ_1)
   --- TC-SetBox-R
   (transient-completion Γ/γ (R (set-box! e_0 e_1)) (R (set-box! e_0c e_1c)) (TST •))]
  [
   (transient-completion Γ/γ (S e_0) (S e_0c) τ/γ_0)
   (transient-completion Γ/γ (S e_1) (S e_1c) τ/γ_1)
   (where ((Box τ/γ) _) τ/γ_0)
   (type= #{remove-srcloc τ/γ} #{remove-srcloc τ/γ_1})
   --- TC-SetBox-S
   (transient-completion Γ/γ (S (set-box! e_0 e_1)) (S (set-box! e_0c e_1c)) τ/γ_1)]
  [
   (side-condition ,(raise-user-error 'infer-type "dyn-check not allowed in source terms ~a" (term (L (dyn-check tag e srcloc)))))
   --- TC-DynCheck-R
   (transient-completion Γ/γ (L (dyn-check tag e srcloc)) (L (dyn-check tag e srcloc)) TST)]
)

(define-metafunction μSR
  transient-completion# : P -> P
  [(transient-completion# P)
   P_t
   (judgment-holds (transient-completion () P P_t _))]
  [(transient-completion# P)
   ,(raise-user-error 'transient-completion "failed to complete ~a" (term P))])

(define-metafunction μSR
  minimal-completion# : P -> P
  [(minimal-completion# P)
   P_+
   (judgment-holds (minimal-completion P P_+))])

(define-metafunction μSR
  completion# : P -> P
  [(completion# P)
   P_+
   (where P_t #{transient-completion# P})
   (where P_+ #{minimal-completion# P_t})])

(define-metafunction μSR
  xerox : any -> any
  [(xerox (any ...))
   (#{xerox any} ...)]
  [(xerox x)
   ,(string->symbol (car (string-split (symbol->string (term x)) "«")))]
  [(xerox any)
   any])

(define (xerox=? t0 t1)
  (define t0+ (term #{xerox ,t0}))
  (define t1+ (term #{xerox ,t1}))
  (debug "xerox=~n    ~a~n    ~a~n" t0+ t1+)
  (equal? t0+ t1+))

(define-metafunction μSR
  apply-op : primop v ... -> v
  [(apply-op car (cons v_0 _))
   v_0]
  [(apply-op cdr (cons _ v_1))
   v_1]
  [(apply-op + v_0 v_1)
   ,(+ (term v_0) (term v_1))]
  [(apply-op * v_0 v_1)
   ,(* (term v_0) (term v_1))]
  [(apply-op - v_0 v_1)
   ,(- (term v_0) (term v_1))]
  [(apply-op = v_0 v_1)
   ,(= (term v_0) (term v_1))])

(define-judgment-form μSR
  #:mode (erasure I O)
  #:contract (erasure P e)
  [
   --- E-Int
   (erasure (L integer) integer)]
  [
   --- E-Bool
   (erasure (L boolean) boolean)]
  [
   (erasure (L e) e_e)
   --- E-λ
   (erasure (L (λ (x τ) e)) (λ (x) e_e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-Pair
   (erasure (L (cons e_0 e_1)) (cons e_0e e_1e))]
  [
   --- E-Var
   (erasure (L x) x)]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-App
   (erasure (L (e_0 e_1)) (e_0e e_1e))]
  [
   (erasure (L_x e_x) e_xc)
   (erasure (L e) e_c)
   --- E-Let
   (erasure (L (let (x τ (L_x e_x)) e))
            (let (x e_xc) e_c))]
  [
   (erasure (L_x e_x) e_xc)
   (erasure (L e) e_c)
   --- E-Letrec
   (erasure (L (letrec (x τ (L_x e_x)) e))
            (letrec (x τ e_xc) e_c))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   (erasure (L e_2) e_2e)
   --- E-If
   (erasure (L (if e_0 e_1 e_2)) (if e_0e e_1e e_2e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-And
   (erasure (L (and e_0 e_1)) (and e_0e e_1e))]
  [
   (erasure (L e) e_e)
   --- E-Car
   (erasure (L (car e)) (car e_e))]
  [
   (erasure (L e) e_e)
   --- E-Cdr
   (erasure (L (cdr e)) (cdr e_e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-Binop
   (erasure (L (binop e_0 e_1)) (binop e_0e e_1e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-=
   (erasure (L (= e_0 e_1)) (= e_0e e_1e))]
  [
   (erasure (L e_0) e_0e)
   --- E-Box
   (erasure (L (box e_0)) (make-box e_0e))]
  [
   (erasure (L e_0) e_0e)
   --- E-MakeBox
   (erasure (L (make-box e_0)) (make-box e_0e))]
  [
   (erasure (L e_0) e_0e)
   --- E-Unbox
   (erasure (L (unbox e_0)) (unbox e_0e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   --- E-SetBox
   (erasure (L (set-box! e_0 e_1)) (set-box! e_0e e_1e))]
  [
   (erasure (L e) e_e)
   --- E-Dyn
   (erasure (L (dyn-check tag e srcloc)) (dyn-check tag e_e srcloc))])

(define-metafunction μSR
  erasure# : P -> e
  [(erasure# P)
   e
   (judgment-holds (erasure P e))])

(define-judgment-form μSR
  #:mode (truthy I)
  #:contract (truthy v)
  [
   (side-condition ,(not (equal? (term v) #false)))
   ---
   (truthy v)])

(define-metafunction μSR
  add-srcloc : τ srcloc -> τ/γ
  [(add-srcloc Int srcloc)
   (Int srcloc)]
  [(add-srcloc Bool srcloc)
   (Bool srcloc)]
  [(add-srcloc TST srcloc)
   (TST srcloc)]
  [(add-srcloc (U τ ...) srcloc)
   ((U τ/γ ...) srcloc)
   (where (τ/γ ...)
         ,(for/list ([t (in-list (term (τ ...)))]
                     [i (in-naturals)])
            (term #{add-srcloc ,t ((proj ,i) srcloc)})))]
  [(add-srcloc (Pair τ_0 τ_1) srcloc)
   ((Pair τ/γ_0 τ/γ_1) srcloc)
   (where τ/γ_0 #{add-srcloc τ_0 (car srcloc)})
   (where τ/γ_1 #{add-srcloc τ_1 (cdr srcloc)})]
  [(add-srcloc (→ τ_0 τ_1) srcloc)
   ((→ τ/γ_0 τ/γ_1) srcloc)
   (where τ/γ_0 #{add-srcloc τ_0 (dom srcloc)})
   (where τ/γ_1 #{add-srcloc τ_1 (cod srcloc)})]
  [(add-srcloc (Box τ) srcloc)
   ((Box τ/γ) srcloc)
   (where τ/γ #{add-srcloc τ (unbox srcloc)})])

(define-metafunction μSR
  get-srcloc : τ/γ -> srcloc
  [(get-srcloc (_ srcloc))
   srcloc])

(define-metafunction μSR
  remove-srcloc : τ/γ -> τ
  [(remove-srcloc (Int _))
   Int]
  [(remove-srcloc (Bool _))
   Bool]
  [(remove-srcloc (TST _))
   TST]
  [(remove-srcloc ((U τ/γ ...) _))
   (U #{remove-srcloc τ/γ} ...)]
  [(remove-srcloc ((Pair τ/γ_0 τ/γ_1) _))
   (Pair #{remove-srcloc τ/γ_0} #{remove-srcloc τ/γ_1})]
  [(remove-srcloc ((→ τ/γ_0 τ/γ_1) _))
   (→ #{remove-srcloc τ/γ_0} #{remove-srcloc τ/γ_1})]
  [(remove-srcloc ((Box τ/γ) _))
   (Box #{remove-srcloc τ/γ})])

(define-metafunction μSR
  make-union/srcloc : τ/γ τ/γ -> τ/γ
  [(make-union/srcloc τ/γ_0 τ/γ_1)
   ((U τ/γ_0 τ/γ_1) •)])

(module+ test

  (test-case "minimal-completion"
    (define d+ (term (dom (+ (→ Int (→ Int Int))))))
    (define dc+ (term (dom (cod (+ (→ Int (→ Int Int)))))))
    (define d* (term (dom (* (→ Int (→ Int Int))))))
    (define dc* (term (dom (cod (* (→ Int (→ Int Int)))))))
    (define d- (term (dom (- (→ Int (→ Int Int))))))
    (define dc- (term (dom (cod (- (→ Int (→ Int Int)))))))
    (define d= (term (dom (= (→ Int (→ Int Bool))))))
    (define dc= (term (dom (cod (= (→ Int (→ Int Bool)))))))

    (check-mf-apply*
     ((minimal-completion# (R 1))
      (R 1))
     ((minimal-completion# (S 1))
      (S 1))
     ((minimal-completion# (R #true))
      (R #true))
     ((minimal-completion# (S #true))
      (S #true))
     ((minimal-completion# (R (λ (x TST) 4)))
      (R (λ (x TST) 4)))
     ((minimal-completion# (S (λ (x Int) 4)))
      (S (λ (x Int) 4)))
     ((minimal-completion# (R (cons 1 1)))
      (R (cons 1 1)))
     ((minimal-completion# (S (cons 1 1)))
      (S (cons 1 1)))
     ((minimal-completion# (R (let (x Int (S (+ 2 2))) (+ x x))))
      (R (let (x Int (S (+ 2 2))) (+ (dyn-check Int x ,d+) (dyn-check Int x ,dc+)))))
     ((minimal-completion# (S (let (x Int (R (+ 2 2))) (+ x x))))
      (S (let (x Int (R (+ (dyn-check Int 2 ,d+) (dyn-check Int 2 ,dc+)))) (+ x x))))
     ((minimal-completion# (R (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (R (if (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)))))
     ((minimal-completion# (S (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (S (if (+ 1 1) (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (and (+ 1 1) (+ 1 1))))
      (R (and (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)))))
     ((minimal-completion# (S (and (+ 1 1) (+ 1 1))))
      (S (and (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (let (n1 TST (R #false)) n1)))
      (R (let (n1 TST (R #false)) n1)))
     ((minimal-completion# (R (= #true 2)))
      (R (= (dyn-check Int #true ,d=) (dyn-check Int 2 ,dc=))))
     ((minimal-completion# (R (f x)))
      (R ((dyn-check → f (#%app (→ TST TST))) x)))
     ((minimal-completion# (S (f x)))
      (S (f x)))
     ((minimal-completion# (R (car 1)))
      (R (car (dyn-check Pair 1 (car (Pair TST TST))))))
     ((minimal-completion# (S (car 1)))
      (S (car 1)))
     ((minimal-completion# (R (cdr 1)))
      (R (cdr (dyn-check Pair 1 (cdr (Pair TST TST))))))
     ((minimal-completion# (S (cdr 1)))
      (S (cdr 1)))
     ((minimal-completion# (R (+ 1 1)))
      (R (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+))))
     ((minimal-completion# (R (* 1 1)))
      (R (* (dyn-check Int 1 ,d*) (dyn-check Int 1 ,dc*))))
     ((minimal-completion# (R (- 1 1)))
      (R (- (dyn-check Int 1 ,d-) (dyn-check Int 1 ,dc-))))
     ((minimal-completion# (S (- 1 1)))
      (S (- 1 1)))
     ((minimal-completion# (S (* 1 1)))
      (S (* 1 1)))
     ((minimal-completion# (S (+ 1 1)))
      (S (+ 1 1)))
     ((minimal-completion# (R (= 1 1)))
      (R (= (dyn-check Int 1 ,d=) (dyn-check Int 1 ,dc=))))
     ((minimal-completion# (S (= 1 1)))
      (S (= 1 1)))
     ((minimal-completion# (R (box (+ 3 3))))
      (R (box (+ (dyn-check Int 3 ,d+) (dyn-check Int 3 ,dc+)))))
     ((minimal-completion# (S (box (+ 3 3))))
      (S (box (+ 3 3))))
     ((minimal-completion# (R (unbox (box 2))))
      (R (unbox (dyn-check Box (box 2) (unbox (Box TST))))))
     ((minimal-completion# (S (unbox (box 2))))
      (S (unbox (box 2))))
     ((minimal-completion# (R (set-box! (box 1) 2)))
      (R (set-box! (dyn-check Box (box 1) (set-box! (Box TST))) 2)))
     ((minimal-completion# (S (set-box! (box 1) 2)))
      (S (set-box! (box 1) 2)))
    )
  )

  (test-case "transient-completion"
    (check-mf-apply*
     ((transient-completion# (S 420))
      (S 420))
     ((transient-completion# (S #true))
      (S #true))
     ((transient-completion# (S (if 1 1 1)))
      (S (if 1 1 1)))
     ((transient-completion# (S (and 1 1)))
      (S (and 1 1)))
     ((transient-completion# (S (cons 1 1)))
      (S (cons 1 1)))
     ((transient-completion# (S (car (cons 1 1))))
      (S (dyn-check Int (car (cons 1 1)) •)))
     ((transient-completion# (S (cdr (cons 1 1))))
      (S (dyn-check Int (cdr (cons 1 1)) •)))
     ((transient-completion# (R (car (cons 1 1))))
      (R (car (cons 1 1))))
     ((transient-completion# (R (cdr 1)))
      (R (cdr 1)))
     ((transient-completion# (S (+ 1 1)))
      (S (+ 1 1)))
     ((transient-completion# (S (- 1 1)))
      (S (- 1 1)))
     ((transient-completion# (S (* 1 1)))
      (S (* 1 1)))
     ((transient-completion# (S (= 1 1)))
      (S (= 1 1)))
     ((transient-completion# (S (box 1)))
      (S (box 1)))
     ((transient-completion# (S (make-box 1)))
      (S (make-box 1)))
     ((transient-completion# (S (unbox (box 1))))
      (S (dyn-check Int (unbox (box 1)) •)))
     ((transient-completion# (S (set-box! (box 1) 2)))
      (S (set-box! (box 1) 2)))
     ((transient-completion# (S (λ (x Int) x)))
      (S (λ (z Int) ((λ (z TST) z) (dyn-check Int z (x Int))))))
     ((transient-completion# (S (λ (x (Pair Int Int)) x)))
      (S (λ (z (Pair Int Int)) ((λ (z TST) z) (dyn-check Pair z (x (Pair Int Int)))))))
     ((transient-completion# (S (let (x Int (R 420)) x)))
      (S (let (z Int (R 420)) ((λ (z TST) z) (dyn-check Int z (x Int))))))
     ((transient-completion# (S (let (x (Box Int) (R (box #true))) x)))
      (S (let (z (Box Int) (R (box #true))) ((λ (z TST) z) (dyn-check Box z (x (Box Int)))))))
     ((transient-completion# (S (let (x Int (S 420)) x)))
      (S (let (x Int (S 420)) x)))
     ((transient-completion# (S (λ (x (U Bool Int)) x)))
      (S (λ (z (U Bool Int)) ((λ (z TST) z) (dyn-check (U Bool Int) z (x (U Bool Int)))))))
     ((transient-completion# (S (λ (x (U (Pair Int Int) (→ Bool Bool))) x)))
      (S (λ (z (U (Pair Int Int) (→ Bool Bool))) ((λ (z TST) z) (dyn-check (U Pair →) z (x (U (Pair Int Int) (→ Bool Bool))))))))
     ((transient-completion# (R (λ (x TST) x)))
      (R (λ (x TST) x)))
     ((transient-completion# (S ((λ (x Int) x) 1)))
      ;; TODO ideally no boundary for this app
      (S (dyn-check Int ((λ (z Int) ((λ (z TST) z) (dyn-check Int z (x Int)))) 1) (cod •))))
     ;; TODO more tests
    )
  )

  (test-case "xerox"
    (check-mf-apply*
     ((xerox x)
      x)
     ((xerox xx«2)
      xx)
     ((xerox some-variable-name)
      some-variable-name)
    )
  )

  (test-case "apply-op"
    (check-mf-apply*
     ((apply-op car (cons 1 2))
      1)
     ((apply-op cdr (cons 1 2))
      2)
     ((apply-op + 1 2)
      3)
     ((apply-op * 3 3)
      9)
     ((apply-op - 1 2)
      -1)
     ((apply-op = 1 2)
      #false)
    )
  )

  (test-case "erasure"
    (check-mf-apply*
     ((erasure# (S 4))
      4)
     ((erasure# (R #true))
      #true)
     ((erasure# (R (cons 1 2)))
      (cons 1 2))
     ((erasure# (S (f x)))
      (f x))
     ((erasure# (R (if 1 2 3)))
      (if 1 2 3))
     ((erasure# (R (and 1 2)))
      (and 1 2))
     ((erasure# (R (car x)))
      (car x))
     ((erasure# (R (cdr x)))
      (cdr x))
     ((erasure# (R (+ 1 2)))
      (+ 1 2))
     ((erasure# (S (= 3 3)))
      (= 3 3))
     ((erasure# (S (box 2)))
      (make-box 2))
     ((erasure# (S (make-box 2)))
      (make-box 2))
     ((erasure# (R (unbox 3)))
      (unbox 3))
     ((erasure# (R (set-box! (box 2) #false)))
      (set-box! (make-box 2) #false))
     ((erasure# (S (dyn-check Int 4 (x Int))))
      (dyn-check Int 4 (x Int)))
    )

    (check-mf-apply* #:is-equal? xerox=?
     ((erasure# (R (let (x (→ Int Int) (S (λ (y Int) (+ y 2)))) (x 3))))
      (let (x (λ (y) (+ y 2))) (x 3)))
     ((erasure# (R (letrec (f (→ Int Int) (S (λ (y Int) (if (= 0 y) 0 (+ 1 (f 0)))))) (f 3))))
      (letrec (f (→ Int Int) (λ (y) (if (= 0 y) 0 (+ 1 (f 0))))) (f 3)))
     ((erasure# (R (λ (x TST) (let (z (→ Int Int) (S (λ (y Int) y))) (z 45)))))
      (λ (x) (let (z (λ (y) y)) (z 45))))
    )
  )

)
