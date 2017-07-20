#lang mf-apply racket/base

;; Simple model of Typed Racket.

;; Soundness (from SNAPL 2017):
;;   If `⊢ e : τ` then either
;;   - `e` reduces to `v` and `⊢ v : τ`
;;   - `e` diverges
;;   - `e` raises a boundary error
;;     BoundaryError L τ P src
;;     where src = (path ... (x τ))
;;     and (let (x τ P') e') subterm of e
;;     and lang(P) = lang(P')
;;     and P not well typed at τ
;;   - `e` raises a dynamic-typing error
;;     DynError tag v srcloc
;;     where not well-tagged v tag
;;     and tag is component of srcloc (TODO)

;; Lemmas
;; - `∀ e . ⊢T e : τ => τ != TST`
;; - `∀ (mon L_ctx τ_ctx (L_v v)) . ⊢L_v v : τ_ctx`
;;   - need stronger statement: `v` well-tagged according to `L_ctx`
;; - completions
;;   - minimal-completion actually minimal (not easy)
;;   - any completion is well-typed (easy)
;; - "blames first boundary" or nothing atall
;; - "boundary error 'more often' than transient"

;; Awkwardnesses
;; - occurrence typing

;; - review once more, writeup on text
;; - start retic model, what are those soundness?!!!

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

(define-language++ μTR #:alpha-equivalent? α=?
  (e ::= v x (e e) (if e e e) (and e e)
         (let (x τ P) e) (let (x e) e)
         (letrec (x τ P) e) (letrec (x τ e) e) (letrec (x e) e) (REC x)
         (cons e e) (car e) (cdr e)
         (binop e e) (= e e)
         (box e) (make-box e) (unbox e) (set-box! e e)
         (dyn-check tag e srcloc)
         (pre-mon L τ P srcloc))
  (v ::= (box x) integer boolean Λ (cons v v) (mon L τ (L v) srcloc))
  (Λ ::= (λ (x) e) (λ (x τ) e))
  (P ::= (L e))
  (τ ::= (U τk ...) τk TST)
  (τk ::= Int Bool (Pair τ τ) (→ τ τ) (Box τ))
  (L ::= R T)
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
         (dyn-check tag E srcloc)
         (pre-mon L τ (L E) srcloc))
  (RuntimeError ::= (DynError tag v srcloc) (BoundaryError L τ P srcloc) (UndefError x))
  (srcloc ::= (path-elem srcloc) (unbox τ) (set-box! τ) (primop τ) (x τ))
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

  (define T-fib (term
    (T (letrec (fib (→ Int Int)
               (T (λ (n Int)
                    (if (= n 0) 1 (if (= n 1) 1
                      (let (prev2 (Box Int) (T (box 1)))
                        (let (prev1 (Box Int) (T (box 1)))
                          (letrec (loop (→ Int Int)
                                  (T (λ (n Int)
                                       (let (curr Int (T (+ (unbox prev1) (unbox prev2))))
                                         (if (= n 0)
                                           curr
                                           (let (blah Int (T (set-box! prev2 (unbox prev1))))
                                             (let (bb Int (T (set-box! prev1 curr)))
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
    (check-pred v? (term (mon T (→ Int Int) (R (λ (x TST) x)) (foo (→ Int Int)))))
    (check-pred P? (term (T (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #f))) ((car ff) 4)))))
    (check-pred P? R-fib)
    (check-pred e? (term (pre-mon T Int (T (set-box!  (mon T (Box Int) (R (box z)) (x (Box Int))) 4)) (y Int))))
    (check-false (v? (term (box 3))))
    (check-false (v? (term (pre-mon T Int (T (set-box! (box 3) 4)) (y Int)))))
    (check-pred v? (term (mon T Int (T 4) (y Int))))
  )
)

;; -----------------------------------------------------------------------------

(define-judgment-form μTR
  #:mode (well-typed I)
  #:contract (well-typed P)
  [
   (infer-type () P τ)
   ---
   (well-typed P)])

(define-judgment-form μTR
  #:mode (check-type I I I)
  #:contract (check-type Γ P τ)
  [
   (infer-type Γ (R e) TST)
   ---
   (check-type Γ (R e) τ)]
  [
   (infer-type Γ (T e) τ_actual)
   (subtype τ_actual τ)
   ---
   (check-type Γ (T e) τ)])

(define-judgment-form μTR
  #:mode (infer-type I I O)
  #:contract (infer-type Γ P τ)
  [
   --- R-I-Int
   (infer-type Γ (R integer) TST)]
  [
   --- T-I-Int
   (infer-type Γ (T integer) Int)]
  [
   --- R-I-Bool
   (infer-type Γ (R boolean) TST)]
  [
   --- T-I-Bool
   (infer-type Γ (T boolean) Bool)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (cons e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   ---
   (infer-type Γ (T (cons e_0 e_1)) (Pair τ_0 τ_1))]
  [
   (infer-type Γ (R e) τ_e)
   ---
   (infer-type Γ (R (car e)) TST)]
  [
   (infer-type Γ (T e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (T (car e)) τ_0)]
  [
   (infer-type Γ (R e) τ)
   ---
   (infer-type Γ (R (cdr e)) TST)]
  [
   (infer-type Γ (T e) (Pair τ_0 τ_1))
   ---
   (infer-type Γ (T (cdr e)) τ_1)]
  [
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e) τ_cod)
   --- R-I-λ
   (infer-type Γ (R (λ (x TST) e)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ_dom)})
   (infer-type Γ_x (T e) τ_cod)
   --- T-I-λ
   (infer-type Γ (T (λ (x τ_dom) e)) (→ τ_dom τ_cod))]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   --- R-I-App
   (infer-type Γ (R (e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where (→ τ_dom τ_cod) τ_0)
   (type= τ_dom τ_1)
   --- T-I-App
   (infer-type Γ (T (e_0 e_1)) τ_cod)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (R x) TST)]
  [
   (where τ #{type-env-ref Γ x})
   ---
   (infer-type Γ (T x) τ)]
  [
   ;; NOTE: the `let`-annotation is bad for R but good for T
   ;; - T components need to be protected from R contexts via their types
   ;; - it's easier to ask for annotation on let
   ;;   than to reconstruct the type from the T-component at runtime
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x TST)})
   (infer-type Γ_x (R e_body) τ_body)
   --- R-I-Let
   (infer-type Γ (R (let (x τ P) e_body)) TST)]
  [
   (check-type Γ P τ)
   (where Γ_x #{type-env-set Γ (x τ)})
   (infer-type Γ_x (T e_body) τ_body)
   --- T-I-Let
   (infer-type Γ (T (let (x τ P) e_body)) τ_body)]
  [
   (where Γ_x #{type-env-set Γ (x τ)})
   (check-type Γ_x P τ)
   (infer-type Γ_x (R e_body) τ_body)
   --- R-I-LetRec
   (infer-type Γ (R (letrec (x τ P) e_body)) TST)]
  [
   (where Γ_x #{type-env-set Γ (x τ)})
   (check-type Γ_x P τ)
   (infer-type Γ_x (T e_body) τ_body)
   --- T-I-LetRec
   (infer-type Γ (T (letrec (x τ P) e_body)) τ_body)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (binop e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (binop e_0 e_1)) Int)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (= e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (type= τ_0 Int)
   (type= τ_1 Int)
   ---
   (infer-type Γ (T (= e_0 e_1)) Bool)]
  [
   (infer-type Γ (R e) τ)
   --- R-I-Box
   (infer-type Γ (R (box e)) TST)]
  [
   (infer-type Γ (T e) τ) ;; no need to generalize
   --- T-I-Box
   (infer-type Γ (T (box e)) (Box τ))]
  [
   (infer-type Γ (R e) τ)
   --- R-I-MakeBox
   (infer-type Γ (R (make-box e)) TST)]
  [
   (infer-type Γ (T e) τ)
   --- T-I-MakeBox
   (infer-type Γ (T (make-box e)) (Box τ))]
  [
   (infer-type Γ (R e) τ)
   --- R-I-Unbox
   (infer-type Γ (R (unbox e)) TST)]
  [
   (infer-type Γ (T e) (Box τ))
   --- T-I-Unbox
   (infer-type Γ (T (unbox e)) τ)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   --- R-I-SetBox
   (infer-type Γ (R (set-box! e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where (Box τ) τ_0)
   (type= τ τ_1)
   --- T-I-SetBox
   (infer-type Γ (T (set-box! e_0 e_1)) τ_1)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   (infer-type Γ (R e_2) τ_2)
   ---
   (infer-type Γ (R (if e_0 e_1 e_2)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (infer-type Γ (T e_2) τ_2)
   (where τ_3 #{make-union τ_1 τ_2})
   ---
   (infer-type Γ (T (if e_0 e_1 e_2)) τ_3)]
  [
   (infer-type Γ (R e_0) τ_0)
   (infer-type Γ (R e_1) τ_1)
   ---
   (infer-type Γ (R (and e_0 e_1)) TST)]
  [
   (infer-type Γ (T e_0) τ_0)
   (infer-type Γ (T e_1) τ_1)
   (where τ_2 #{make-union τ_0 τ_1})
   ---
   (infer-type Γ (T (and e_0 e_1)) τ_2)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (mon R τ P srcloc)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (mon T τ P srcloc)) τ)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (R (pre-mon R τ P srcloc)) TST)]
  [
   (check-type Γ P τ)
   ---
   (infer-type Γ (T (pre-mon T τ P srcloc)) τ)]
  [
   (side-condition ,(raise-user-error 'infer-type "dyn-check not allowed in source terms ~a" (term (L (dyn-check tag e srcloc)))))
   ---
   (infer-type Γ (L (dyn-check tag e srcloc)) TST)]
)

(define-metafunction μTR
  check-type# : P τ -> boolean
  [(check-type# P τ)
   #true
   (judgment-holds (check-type () P τ))]
  [(check-type# P τ)
   #false])

(define-metafunction μTR
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
     ((infer-type# (T (if (and #true #true) (+ 1 1) (+ 2 2))))
      Int)
     ((infer-type# (R (let (f TST (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      TST)
     ((infer-type# (T (let (f (→ Int Int) (R (λ (x TST) (if (= x 1) 1 #false)))) (f 1))))
      Int)
     ((infer-type# (T (if 1 2 #false)))
      (U Bool Int))
    )
  )

  (test-case "well-typed"
    (check-judgment-holds*
     (well-typed (T (λ (x Int) 2)))
     (infer-type () (T (λ (x Int) 3)) (→ Int Int))
     (check-type () (T (λ (x Int) 3)) (→ Int Int))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (src (→ Int Int))) 7)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (check-type () (T 1) Int)
     (check-type () (T 1) (U Int (Pair Int Int)))
     (well-typed (T (if 1 2 (cons 2 3))))
     (check-type () (T (and 1 #true)) (U Bool Int))
     (well-typed (T (if (λ (x Int) x) 1 0)))
     (well-typed (T (let (x Int (T 1)) (let (y Int (T 2)) (+ x y)))))
     (well-typed (T (let (h (→ Bool Bool)
                         (R (let (g (→ Int Int)
                                    (T (let (f (→ Int Int)
                                               (R (λ (x TST) x)))
                                         f)))
                              g)))
                   (h #true))))
     (well-typed (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (src (→ Int Int))) 7)))
     (well-typed (R (car (λ (x TST) x))))
     (well-typed (R (car 3)))
     (well-typed (R (car (cons 1 2))))
     (well-typed (T (car (cons 1 2))))
     (well-typed (T (λ (x Int) (+ x 1))))
     (well-typed (R (let (f (→ Int Int) (T (λ (x Int) (+ x 1)))) (f 3))))
     (well-typed (R (unbox 3)))
     (well-typed (R (+ 1 (make-box 3))))
     (well-typed (R (make-box (λ (x TST) (+ 2 2)))))
     (well-typed (T (make-box (λ (x Bool) (+ 2 2)))))
     (well-typed (T (+ 1 (unbox (box 4)))))
     (well-typed (T (+ 1 (unbox (make-box 4)))))
     (well-typed (T (let (x (Box Int) (R (box #true))) (+ 1 (unbox x)))))
     (well-typed (R (letrec (fact (→ Int Int) (R (λ (n TST) (if (= n 0) n (* n (fact (- n 1))))))) (fact 6))))
     (well-typed (T (letrec (fact (→ Int Int) (T (λ (n Int) (if (= n 0) n (* n (fact (- n 1))))))) (fact 6))))
     (well-typed (T (letrec (x (Box Int) (R (box 3))) x)))
     (well-typed (T (letrec (x (Box Int) (R (box 3)))
                      (let (y Int (T (set-box! x 4)))
                        y))))
     (well-typed (T (letrec (x (Box Int) (R (make-box 3)))
                      (let (y Int (T (set-box! x 4)))
                        y))))
     (well-typed (T (letrec (x (Box Int) (R (box 3)))
                      (let (y Int (T (set-box! x 4)))
                        (+ y (unbox x))))))
     (well-typed ,R-fib)
     (well-typed ,T-fib)
    )

    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (R (dyn-check Int 3 (x Int)))))))
    (check-exn #rx"dyn-check not allowed"
      (λ () (term (well-typed (T (dyn-check → (λ (x Int) 3) (f Int)))))))

  )

  (test-case "not-well-typed"
    (check-not-judgment-holds*
     (well-typed (T (car 1)))
     (well-typed (T (set-box! 1 1)))
     (well-typed (T (unbox (λ (x Int) x))))
     (well-typed (T (unbox 1)))
     (well-typed (T (set-box! (box 0) (box 4))))
     (well-typed (T (let (b (Box Int) (R (box 1))) (set-box! b #false))))
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- evalution

(define -->μTR
  (reduction-relation μTR
    #:domain A
;; -- MON
    [-->
     [ρ (in-hole E (pre-mon R τ_ctx (T v) srcloc))]
     [ρ (in-hole E v)]
     PreMon-T->R-Flat
     (judgment-holds (flat T τ_ctx))]
    [-->
     [ρ (in-hole E (pre-mon R τ_ctx (T v) srcloc))]
     [ρ (in-hole E (mon R τ_ctx (T v) srcloc))]
     (judgment-holds (non-flat T τ_ctx))]
    [-->
     [ρ (in-hole E (pre-mon L_m τ (L_m v) srcloc))]
     [ρ (in-hole E v)]
     PreMon-NoBoundary]
    [-->
     [ρ (in-hole E (pre-mon T τ_ctx (R v) srcloc))]
     [ρ (in-hole E v_+)]
     PreMon-R->T-MaybeOk
     (where v_+ #{dynamic-typecheck T τ_ctx (R v) srcloc ρ})]
    [-->
     [ρ (in-hole E (pre-mon T τ_ctx (R v) srcloc))]
     RuntimeError
     PreMon-R->T-Error
     (where RuntimeError #{dynamic-typecheck T τ_ctx (R v) srcloc ρ})]
;; -- APP
    [-->
     [ρ (in-hole E ((λ (x) e) v_1))]
     [ρ (in-hole E (substitute e x v_1))]
     App-Beta]
    [-->
     [ρ (in-hole E ((mon L_ctx τ_ctx (L_λ v) srcloc) v_1))]
     [ρ (in-hole E e_cod)]
     App-Mon
     (where (→ τ_dom τ_cod) τ_ctx)
     (where P_dom (L_λ (v (pre-mon L_λ τ_dom (L_ctx v_1) (dom srcloc)))))
     (where e_cod (pre-mon L_ctx τ_cod P_dom (cod srcloc)))]
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
     [ρ (in-hole E (unbox (mon L (Box τ) (L_m v_m) srcloc)))]
     [ρ (in-hole E (pre-mon L τ (L_m (unbox v_m)) (unbox srcloc)))]
     Unbox-Mon]
    [-->
     [ρ (in-hole E (set-box! (box x) v))]
     [ρ_v (in-hole E v)]
     SetBox
     (where ρ_v #{runtime-env-update-box ρ x v})]
    [-->
     [ρ (in-hole E (set-box! (mon L (Box τ) (L_m v_m) srcloc) v))]
     [ρ (in-hole E (set-box! v_m (pre-mon L_m τ (L v) (set-box! srcloc))))]
     SetBox-Mon] ;; bring `v_m` into the box's language,
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

(define -->μTR*
  (make--->* -->μTR))

(define-metafunction μTR
  eval : P  -> any
  [(eval P)
   #{eval* P #false}])

(define-metafunction μTR
  eval* : P boolean -> any
  [(eval* P boolean_keeptrace)
   any
   (judgment-holds (well-typed P))
   (where P_c #{minimal-completion# P})
   (where e_c #{erasure# P_c})
   (where any_init #{load e_c})
   (where any ,(if (term boolean_keeptrace)
                 (apply-reduction-relation* -->μTR (term any_init) #:all? #t)
                 (let ([final (-->μTR* (term any_init))])
                 (when (*debug*) (printf "FINAL STATE ~a~n" final))
                   (term #{unload ,final}))))]
  [(eval* P boolean_keeptrace)
   ,(raise-user-error 'eval "trouble eval'ing ~a" (term e_c))
   (judgment-holds (well-typed P))
   (where P_c #{minimal-completion# P})
   (where e_c #{erasure# P_c})]
  [(eval* P boolean_keeptrace)
   ,(raise-user-error 'eval "trouble erasing let from ~a" (term P_c))
   (judgment-holds (well-typed P))
   (where P_c #{minimal-completion# P})]
  [(eval* P _)
   ,(raise-user-error 'eval "trouble completing ~a" (term P))
   (judgment-holds (well-typed P))]
  [(eval* P _)
   ,(raise-user-error 'eval "typechecking failed ~a" (term P))])

(define-metafunction μTR
  load : e -> [ρ e]
  [(load e)
   (#{runtime-env-init} e)])

(define-metafunction μTR
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
      ((eval (R (pre-mon R Int (T 6) (boundary Int))))
       6)
      ((eval (R ((mon R (→ Int Int) (T (λ (x Int) 2)) (boundary (→ Int Int))) 7)))
       2)
      ((eval (R (let (b TST (R (box 3)))
                  (let (f TST (R (λ (x TST) (unbox b))))
                    (let (dontcare TST (R (set-box! b 4)))
                      (f 1))))))
       4)
    )
  )

  (test-case "eval:simple:T"
    (check-mf-apply*
     [(eval (T 4))
      4]
     ((eval (T (if (and #true (= 4 2)) (+ 1 1) (+ 2 2))))
      4)
     [(eval (T #true))
      #true]
     [(eval (T (+ 2 2)))
      4]
     [(eval (T ((λ (x Int) x) 1)))
      1]
     [(eval (T ((λ (x Int) (+ x 1)) 1)))
      2]
     [(eval (T (if ((λ (x Bool) x) #true) 1 0)))
      1]
     [(eval (T (if #false (+ 6 6) 0)))
      0]
     [(eval (T (let (x Int (T 1))
                 (let (y Int (T 2))
                   (+ x y)))))
      3]
     [(eval (T (let (negate (→ Bool Bool) (T (λ (x Bool) (if x #false #true))))
                 (let (b Bool (T #false))
                   (negate (negate b))))))
      #false]
     [(eval (T (let (x Int (T 4))
                 (let (add-x (→ Int Int) (T (λ (y Int) (+ y x))))
                   (let (x Int (T 5))
                     (add-x x))))))
      9]
     [(eval (T (cons (+ 2 2) (+ 1 1))))
      (cons 4 2)]
     [(eval (T (+ 2 (cdr (cons #false 4)))))
      6]
     [(eval (T (unbox (box 3))))
      3]
     [(eval (T (set-box! (box 3) 4)))
      4]
     [(eval (T (if (λ (x (Box Int)) x) 1 0)))
      1]
    )
  )

  (test-case "eval:simple:T:fail"
    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (T ((λ (x Int) (+ x 1)) #false))})))

    (check-exn #rx"typechecking failed"
      (λ () (term (eval (T (let (x Bool (T (+ 2 5))) x)))))))

  (test-case "apply-R-in-T"
    (check-mf-apply*
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x 1))))
                 (f 3))))
      4]
     [(eval (T (let (f (→ Int Bool) (R (λ (x TST) (if (= 0 x) #false #true))))
                 (f 3))))
      #true]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) #false))) (f 1))))
      (BoundaryError T Int (R #false) (cod (f (→ Int Int))))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError Int #f (dom (cod (+ (→ Int (→ Int Int))))))]
     [(eval (T (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError Int #t (dom (+ (→ Int (→ Int Int)))))]
     [(eval (T (let (f (→ Int (Box Int)) (R (λ (x TST) (box x))))
                 (f 3))))
      (mon T (Box Int) (R (box 3)) (cod (f (→ Int (Box Int)))))]
     ((eval (T (let (f (→ Int Int) (R (λ (x TST) #false))) (f 3))))
      (BoundaryError T Int (R #false) (cod (f (→ Int Int)))))
     ((eval (T (let (f (→ Int Int) (R (λ (x TST) (+ x #false)))) (f 3))))
      (DynError Int #false (dom (cod (+ (→ Int (→ Int Int)))))))
     ((eval (T (let (f (→ Int Int) (R (λ (x TST) (+ #true #false)))) (f 3))))
      (DynError Int #true (dom (+ (→ Int (→ Int Int))))))
    )
  )

  (test-case "apply-T-in-R"
    (check-mf-apply*
     [(eval (R (let (f (→ Int Int) (T (λ (x Int) (+ x 1)))) (f 3))))
      4]
     [(eval (R (let (f (→ Int Bool) (T (λ (x Int) (if (= 0 x) #false #true)))) (f 3))))
      #true]
     [(eval (R (let (f (→ Int Int) (T (λ (x Int) (+ x 4)))) (f #true))))
      (BoundaryError T Int (R #true) (dom (f (→ Int Int))))]
    )

    (check-exn #rx"typechecking failed"
      (λ () (term #{eval (R (let (f (→ Int Int) (T (λ (x Int) #false))) (f 1)))})))
  )

  (test-case "eval:box"
    (check-mf-apply*
     ((eval (R (let (x TST (R (box 3))) 0)))
       0)
     ((eval (R (let (x TST (R (box 3))) x)))
      (box 3))
     ((eval (R (letrec (x TST (R (box 3))) x)))
       (box 3))
     ;; TODO cross-boundary
     ((eval (R (let (x TST (R (box 3))) (unbox x))))
       3)
     ((eval (R (let (x TST (R (box 3))) (+ 1 (unbox x)))))
       4)
     ((eval (R (let (x TST (R (box 3)))
                (let (z TST (R (unbox x)))
                 (let (y TST (R (set-box! x 4)))
                   (+ z (unbox x)))))))
       7)
     ((eval (T (let (x (Box Int) (R (make-box 3)))
                 (let (y Int (T (set-box! x 4)))
                   (+ y (unbox x))))))
      8)
     ((eval (T (letrec (x (Box Int) (R (box 3)))
                 (let (y Int (T (set-box! x 4)))
                   (+ y (unbox x))))))
       8)
    )

  )

  (test-case "eval:R:III"
    (check-mf-apply*
     ((eval (R (pre-mon R (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b2 (→ Int Int)))))
      (mon R (→ Int Int) (T (mon T (→ Int Int) (R (λ (x) x)) (b1 (→ Int Int)))) (b2 (→ Int Int))))
     ((eval (R (letrec (fact TST (R (λ (n TST) (if (= 0 n) 1 (* n (fact (- n 1))))))) (fact 6))))
      720)
     ((eval ,R-fib)
      8)
    )
  )

  (test-case "double-wrap"
    (check-mf-apply*
     ((eval (T (let (h (→ Bool Bool)
                       (R (let (g (→ Int Int)
                                  (T (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h #true))))
      (BoundaryError T Int (R #true) (dom (g (→ Int Int)))))
     ((eval (T (let (h (→ Int Int)
                       (R (let (g (→ Int Int)
                                  (T (let (f (→ Int Int)
                                             (R (λ (x TST) x)))
                                       f)))
                            g)))
                 (h 5))))
      5)))

  (test-case "more-R-in-T"
    (check-mf-apply*
     ((eval (T (let (ff (Pair (→ Int Int) Bool) (R (cons (λ (x TST) (+ x x)) #false)))
                 ((car ff) 4))))
      8)
     ((eval (T (let (ff (Pair (→ Bool Bool) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      #false)
     ((eval (T (let (ff (Pair (→ Bool Int) Bool) (R (cons (λ (x TST) x) #false)))
                 ((car ff) (cdr ff)))))
      (BoundaryError T Int (R #false) (cod (car (ff (Pair (→ Bool Int) Bool))))))
     ((eval (T (let (ff (→ Int (U Bool Int)) (R (λ (x TST) (if (= x 0) #false x))))
                 (let (gg (→ (U Bool Int) Int) (R (λ (x TST) 900)))
                   (+ (gg (ff 0))
                      (gg (ff 1)))))))
      1800)
    )
  )

  (test-case "boxof-R-in-T"
    (check-mf-apply*
     [(eval (T (let (b (Box Int) (R (box 1)))
                 (let (_dontcare Int (T (set-box! b 2)))
                   (unbox b)))))
      2]
     ((eval (T (let (b (Box Int) (R (box #false)))
                   0)))
      (BoundaryError T (Box Int) (R (box #false)) (b (Box Int))))
    )
  )

  (test-case "boxof-T-in-R"
    (check-mf-apply*
     [(eval (R (let (b (Box Int) (T (box 1)))
                 (unbox b))))
      1]
     [(eval (R (let (b (Box Int) (T (box 1)))
                 (set-box! b 4))))
      4]
     [(eval (R (let (bb (Box (Box Int)) (T (box (box 1))))
                 (let (_dontcare Int (R (set-box! (unbox bb) 777)))
                   (unbox (unbox bb))))))
      777]
     [(eval (R (let (b (Box Int) (T (box 1)))
                 (set-box! b #f))))
      (BoundaryError T Int (R #f) (set-box! (b (Box Int))))]
     [(eval (R (let (bb (Box (Box Int)) (T (box (box 1))))
                 (let (_dontcare Bool (R (set-box! (unbox bb) #false)))
                   (unbox (unbox bb))))))
      (BoundaryError T Int (R #false) (set-box! (unbox (bb (Box (Box Int))))))]
    )
  )

  (test-case "box:error"
    (check-mf-apply*
     ((eval (T (let (x (Box Int) (R 42)) #false)))
      (BoundaryError T (Box Int) (R 42) (x (Box Int))))
     ((eval (T (let (x (Box Int) (R (box #true))) #false)))
      (BoundaryError T (Box Int) (R (box #true)) (x (Box Int))))
    )
  )

  (test-case "well-typed-programs-run-faster"
    (define (check-shorter-trace t1 t2)
      (define-values [trace1 trace2]
          (values (term #{eval* ,t1 #true}) (term #{eval* ,t2 #true})))
      (check < (length trace1) (length trace2)))

    (check-shorter-trace (term (T (+ 2 2))) (term (R (+ 2 2))))
  )
)

;; =============================================================================
;; === less interesting from here on
;; =============================================================================

;; -----------------------------------------------------------------------------
;; --- type helpers

(define-judgment-form μTR
  #:mode (type= I I)
  #:contract (type= τ τ)
  [
   (side-condition ,(α=? (term #{type-normalize τ_0}) (term #{type-normalize τ_1})))
   --- Refl
   (type= τ_0 τ_1)])

(define-metafunction μTR
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

(define-judgment-form μTR
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

(define-metafunction μTR
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

(define-judgment-form μTR
  #:mode (well-tagged I I)
  #:contract (well-tagged v tag)
  [
   ---
   (well-tagged integer Int)]
  [
   ---
   (well-tagged boolean Bool)]
  [
   ---
   (well-tagged Λ →)]
  [
   ---
   (well-tagged (box _) Box)]
  [
   ---
   (well-tagged (cons _ _) Pair)]
  [
   (tag= #{tag-only τ} tag)
   ---
   (well-tagged (mon _ τ _ _) tag)]
  [
   (well-tagged v tagk)
   --- Tag-U
   (well-tagged v (U tagk_0 ... tagk tagk_1 ...))])

(define-judgment-form μTR
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

(define-metafunction μTR
  type-env-set : Γ (x τ) -> Γ
  [(type-env-set Γ (x τ))
   ,(cons (term (x τ)) (term Γ))])

(define-metafunction μTR
  type-env-ref : Γ x -> any
  [(type-env-ref Γ x)
   ,(for/first ([xτ (in-list (term Γ))]
                #:when (eq? (term x) (car xτ)))
      (cadr xτ))])

(define-metafunction μTR
  runtime-env-init : -> ρ
  [(runtime-env-init)
   ()])

(define-metafunction μTR
  runtime-env-set : ρ x any -> ρ
  [(runtime-env-set ρ x (BOX v))
   ,(cons (term (x (BOX v))) (term ρ))]
  [(runtime-env-set ρ x UNDEF)
   ,(cons (term (x UNDEF)) (term ρ))])

(define-metafunction μTR
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

(define-metafunction μTR
  runtime-env-ref-box : ρ x -> (BOX v)
  [(runtime-env-ref-box ρ x)
   (BOX v)
   (where (BOX v) #{runtime-env-ref ρ x})]
  [(runtime-env-ref-box ρ x)
   ,(raise-arguments-error 'runtime-env-ref-box "bad location in box"
      "location" (term x)
      "value" (term #{runtime-env-ref ρ x})
      "env" (term ρ))])

(define-metafunction μTR
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

(define-metafunction μTR
  runtime-env-update : ρ x v -> ρ
  [(runtime-env-update (RB_0 ... (x UNDEF) RB_1 ...) x v)
   (RB_0 ... (x (LETREC v)) RB_1 ...)]
  [(runtime-env-update (RB_0 ... (x (BOX v_x)) RB_1 ...) x v)
   (RB_0 ... (x (BOX v)) RB_1 ...)]
  [(runtime-env-update ρ x v)
   ,(raise-arguments-error 'runtime-env-ref "unbound variable" "var" (term x) "env" (term ρ))])

(define-metafunction μTR
  runtime-env-update-box : ρ x v -> ρ
  [(runtime-env-update-box ρ x v)
   #{runtime-env-update ρ x v}
   (where (BOX v_x) #{runtime-env-ref-box ρ x})]
  [(runtime-env-update-box ρ x v)
   ,(raise-arguments-error 'runtime-env-update "bad location"
     "location" (term x)
     "value" (term #{runtime-env-ref ρ x})
     "env" (term ρ))])

(define-metafunction μTR
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
(define-metafunction μTR
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
(define-judgment-form μTR
  #:mode (flat I I)
  #:contract (flat L τ)
  [
   ---
   (flat L TST)]
  [
   ---
   (flat T Int)]
  [
   ---
   (flat T Bool)]
  [
   (flat T τ_0)
   (flat T τ_1)
   ---
   (flat T (Pair τ_0 τ_1))])

(define-judgment-form μTR
  #:mode (non-flat I I)
  #:contract (non-flat L τ)
  [
   (side-condition ,(not (judgment-holds (flat L τ))))
   ---
   (non-flat L τ)])

(module+ test
  (test-case "flat"
    (check-judgment-holds*
     (flat T Int)
     (flat T (Pair Int Int))

     (non-flat R Int)
     (non-flat T (→ Bool Bool))
     (non-flat T (Pair Int (Pair (→ Int Int) Int)))
    )

    (check-not-judgment-holds*
     (flat R Int)
     (flat T (→ Bool Bool))
     (flat T (Pair Int (Pair (→ Int Int) Int)))

     (non-flat T Int)
     (non-flat T (Pair Int Int))
    )
  )
)

;; -----------------------------------------------------------------------------
;; --- dynamic-typecheck

;; Bad design here, so need ρ. This function does 2 things
;; - checks that a value might be well-typed
;; - creates a monitored version of the value
;; This double-duty doesn't work for boxes, because
;; - to check a box, need to get current value of location
;; - the monitored box should NOT monitor the insides and NOT return a box with values substituted
(define-metafunction μTR
  dynamic-typecheck : L τ P srcloc ρ -> any ;; value or BoundaryError
  [(dynamic-typecheck R τ P srcloc ρ)
   ,(raise-user-error 'dynamic-typecheck "language R has no dynamic typechecker ~a ~a" (term e) (term τ))]
;; --- Int
  [(dynamic-typecheck T Int (L integer) srcloc ρ)
   integer]
  [(dynamic-typecheck T Int (L v) srcloc ρ)
   (BoundaryError T Int (L v) srcloc)]
;; --- Bool
  [(dynamic-typecheck T Bool (L boolean) srcloc ρ)
   boolean]
  [(dynamic-typecheck T Bool (L v) srcloc ρ)
   (BoundaryError T Bool (L v) srcloc)]
;; --- Pair
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc ρ)
   RuntimeError
   (where RuntimeError #{dynamic-typecheck T τ_0 (L v_0) (car srcloc) ρ})]
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc ρ)
   RuntimeError
   (where RuntimeError #{dynamic-typecheck T τ_1 (L v_1) (cdr srcloc) ρ})]
  [(dynamic-typecheck T (Pair τ_0 τ_1) (L (cons v_0 v_1)) srcloc ρ)
   (cons v_0+ v_1+)
   (where v_0+ #{dynamic-typecheck T τ_0 (L v_0) (car srcloc) ρ})
   (where v_1+ #{dynamic-typecheck T τ_1 (L v_1) (cdr srcloc) ρ})]
;; --- U
  [(dynamic-typecheck T (U τk ...) (L v) srcloc ρ)
   ,(let loop ([tk* (term (τk ...))] [i 0])
      (if (null? tk*)
        (term (BoundaryError T (U τk ...) (L v) srcloc))
        (let ([x (term #{dynamic-typecheck T ,(car tk*) (L v) ((proj ,i) srcloc) ρ})])
          (if (RuntimeError? x)
            (loop (cdr tk*) (+ i 1))
            x))))]
;; --- Box
  [(dynamic-typecheck T (Box τ) (L (box x)) srcloc ρ)
   (mon T (Box τ) (L (box x)) srcloc)
   ;; IGNORE what's in the middle, it's just to catch runtime errors
   ;;  safe to ignore because dynamic _unbox_ installs monitors,
   ;;  and unbox will catch cases that this function cannot
   (where (BOX v) #{runtime-env-ref ρ x})
   (where e_dontcare #{dynamic-typecheck T τ (L v) (unbox srcloc) ρ})]
;; --- →
  [(dynamic-typecheck T (→ τ_dom τ_cod) (L Λ) srcloc ρ)
   (mon T (→ τ_dom τ_cod) (L Λ) srcloc)]
;; --- higher-order common (→ Box)
  [(dynamic-typecheck T τ P srcloc ρ)
   RuntimeError
   (where (L (mon L_mon τ_mon P_mon srcloc_mon)) P)
   (where TST τ_mon)
   (where RuntimeError #{dynamic-typecheck T τ P_mon srcloc ρ})]
  [(dynamic-typecheck T τ P srcloc ρ)
   (mon T τ P srcloc)
   (side-condition (or (judgment-holds (non-flat T τ)) (raise-user-error 'dynamic-typecheck "bad case")))
   (where (L (mon L_mon τ_mon P_mon srcloc_mon)) P)
   (judgment-holds (tag= #{tag-only τ_mon} #{tag-only τ}))]
  [(dynamic-typecheck T τ (L e) srcloc ρ)
   (BoundaryError T τ (L any) srcloc)
   (judgment-holds (non-flat T τ))
   (where any #{runtime-env-unload ρ e})]
;; --- TST
  [(dynamic-typecheck T TST (L v) srcloc ρ)
   v
   (side-condition (printf "WARNING: T expects value ~a to have TST~n" (term v)))])

(define-judgment-form μTR
  #:mode (proc? I)
  #:contract (proc? v)
  [
   ---
   (proc? (λ (x τ) e))]
  [
   (proc? v_1) ;; since mon always check constructor, could just check τ_0
   ---
   (proc? (mon L_0 τ_0 (L_1 v_1) srcloc))])

(define-judgment-form μTR
  #:mode (cons? I)
  #:contract (cons? v)
  [
   ---
   (cons? (cons e_0 e_1))])

(define-metafunction μTR
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
  [(tag-only TST)
   TST])

;; Add runtime checks to ensure safety
(define-judgment-form μTR
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
   (minimal-completion P_m P_mc)
   ---
   (minimal-completion (L (mon L_m τ_m P_m srcloc)) (L (mon L_m τ_m P_mc srcloc)))]
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
   (side-condition ,(raise-user-error 'minimal-completion "dyn-check not allowed in source programs ~a" (term (L (dyn-check tag e srcloc)))))
   ---
   (minimal-completion (L (dyn-check tag e srcloc)) (L (dyn-check tag e srcloc)))]
  [
   (minimal-completion P P_c)
   ---
   (minimal-completion (L (pre-mon L_m τ P srcloc)) (L (pre-mon L_m τ P_c srcloc)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-App
   (minimal-completion (R (e_0 e_1)) (R ((dyn-check → e_0c (#%app (→ TST TST))) e_1c)))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-App
   (minimal-completion (T (e_0 e_1)) (T (e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Car
   (minimal-completion (R (car e_0)) (R (car (dyn-check Pair e_0c (car (Pair TST TST))))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   --- T-Car
   (minimal-completion (T (car e_0)) (T (car e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   --- R-Cdr
   (minimal-completion (R (cdr e_0)) (R (cdr (dyn-check Pair e_0c (cdr (Pair TST TST))))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   --- T-Cdr
   (minimal-completion (T (cdr e_0)) (T (cdr e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   (where srcloc (binop (→ Int (→ Int Int))))
   --- R-Binop
   (minimal-completion (R (binop e_0 e_1)) (R (binop (dyn-check Int e_0c (dom srcloc)) (dyn-check Int e_1c (dom (cod srcloc))))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-Binop
   (minimal-completion (T (binop e_0 e_1)) (T (binop e_0c e_1c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   (where srcloc (= (→ Int (→ Int Bool))))
   --- R-=
   (minimal-completion (R (= e_0 e_1)) (R (= (dyn-check Int e_0c (dom srcloc)) (dyn-check Int e_1c (dom (cod srcloc))))))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-=
   (minimal-completion (T (= e_0 e_1)) (T (= e_0c e_1c)))]
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
   (minimal-completion (T e_0) (T e_0c))
   --- T-Unbox
   (minimal-completion (T (unbox e_0)) (T (unbox e_0c)))]
  [
   (minimal-completion (R e_0) (R e_0c))
   (minimal-completion (R e_1) (R e_1c))
   --- R-SetBox
   (minimal-completion (R (set-box! e_0 e_1)) (R (set-box! (dyn-check Box e_0c (set-box! (Box TST))) e_1c)))]
  [
   (minimal-completion (T e_0) (T e_0c))
   (minimal-completion (T e_1) (T e_1c))
   --- T-SetBox
   (minimal-completion (T (set-box! e_0 e_1)) (T (set-box! e_0c e_1c)))])

(define-metafunction μTR
  minimal-completion# : P -> P
  [(minimal-completion# P)
   P_+
   (judgment-holds (minimal-completion P P_+))])

(define-metafunction μTR
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

(define-metafunction μTR
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

(define-judgment-form μTR
  #:mode (erasure I O)
  #:contract (erasure P e)
  [
   ---
   (erasure (L integer) integer)]
  [
   ---
   (erasure (L boolean) boolean)]
  [
   (erasure (L e) e_e)
   ---
   (erasure (L (λ (x τ) e)) (λ (x) e_e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (cons e_0 e_1)) (cons e_0e e_1e))]
  [
   (erasure (L_e e) e_e)
   ---
   (erasure (L (mon L_m τ_m (L_e e) srcloc)) (mon L_m τ_m (L_e e_e) srcloc))]
  [
   ---
   (erasure (L x) x)]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (e_0 e_1)) (e_0e e_1e))]
  [
   (erasure (L_x e_x) e_xe)
   (erasure (L e) e_c)
   ---
   (erasure (L (let (x τ (L_x e_x)) e)) (let (x (pre-mon L τ (L_x e_xe) (#{xerox x} τ))) e_c))]
  [
   (erasure (L_x e_x) e_xe)
   (erasure (L e) e_c)
   ---
   (erasure (L (letrec (x τ (L_x e_x)) e))
            (letrec (x τ (pre-mon L τ (L_x e_xe) (#{xerox x} τ))) e_c))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   (erasure (L e_2) e_2e)
   ---
   (erasure (L (if e_0 e_1 e_2)) (if e_0e e_1e e_2e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (and e_0 e_1)) (and e_0e e_1e))]
  [
   (erasure (L e) e_e)
   ---
   (erasure (L (car e)) (car e_e))]
  [
   (erasure (L e) e_e)
   ---
   (erasure (L (cdr e)) (cdr e_e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (binop e_0 e_1)) (binop e_0e e_1e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (= e_0 e_1)) (= e_0e e_1e))]
  [
   (erasure (L e_0) e_0e)
   ---
   (erasure (L (box e_0)) (make-box e_0e))]
  [
   (erasure (L e_0) e_0e)
   ---
   (erasure (L (make-box e_0)) (make-box e_0e))]
  [
   (erasure (L e_0) e_0e)
   ---
   (erasure (L (unbox e_0)) (unbox e_0e))]
  [
   (erasure (L e_0) e_0e)
   (erasure (L e_1) e_1e)
   ---
   (erasure (L (set-box! e_0 e_1)) (set-box! e_0e e_1e))]
  [
   (erasure (L e) e_e)
   ---
   (erasure (L (dyn-check tag e srcloc)) (dyn-check tag e_e srcloc))]
  [
   (erasure (L_m e_m) e_me)
   ---
   (erasure (L (pre-mon L_ctx τ_ctx (L_m e_m) srcloc)) (pre-mon L_ctx τ_ctx (L_m e_me) srcloc))])

(define-metafunction μTR
  erasure# : P -> e
  [(erasure# P)
   e
   (judgment-holds (erasure P e))])

(define-judgment-form μTR
  #:mode (well-formed-monitor I)
  #:contract (well-formed-monitor v)
  [
   (well-tagged Λ #{tag-only τ})
   --- λ
   (well-formed-monitor (mon L τ (L_v Λ) _))]
  [
   (well-tagged (box any) #{tag-only τ})
   --- box
   (well-formed-monitor (mon L τ (L_v (box any)) _))]
  [
   (tag= #{tag-only τ} #{tag-only τ_m})
   (well-formed-monitor (mon L_m τ_m (L_mm v_mm) srcloc))
   --- recur
   (well-formed-monitor (mon L τ (L_v (mon L_m τ_m (L_mm v_mm) srcloc)) _))])

(define-judgment-form μTR
  #:mode (truthy I)
  #:contract (truthy v)
  [
   (side-condition ,(not (equal? (term v) #false)))
   ---
   (truthy v)])

(module+ test
  (test-case "dynamic-typecheck"
    (check-mf-apply*
     ((dynamic-typecheck T Int (R 4) (x Int) ())
      4)
     ((dynamic-typecheck T (→ Int Int) (R (λ (x Int) 3)) (f (→ Int Int)) ())
      (mon T (→ Int Int) (R (λ (x Int) 3)) (f (→ Int Int))))
     ((dynamic-typecheck T (→ Bool Bool) (T (λ (x Bool) #false)) (f (→ Bool Bool)) ())
      (mon T (→ Bool Bool) (T (λ (x Bool) #false)) (f (→ Bool Bool))))
     ((dynamic-typecheck T (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b3 (→ Int Int)) ())
      (mon T (→ Int Int) (T (mon T (→ Int Int) (R (λ (x TST) x)) (b1 (→ Int Int)))) (b3 (→ Int Int))))
     ((dynamic-typecheck T (Pair Int Int) (R (cons 1 1)) (x (Pair Int Int)) ())
      (cons 1 1))
     ((dynamic-typecheck T (Pair Int Bool) (R (cons 2 #false)) (x (Pair Int Bool)) ())
      (cons 2 #false))
     ((dynamic-typecheck T (Pair (→ Bool Bool) Bool) (R (cons (λ (x TST) x) #true)) (x (Pair (→ Bool Bool) Bool)) ())
      (cons (mon T (→ Bool Bool) (R (λ (x TST) x)) (car (x (Pair (→ Bool Bool) Bool)))) #true))
     ((dynamic-typecheck T (Pair Int Int) (R (cons 1 #false)) (x (Pair Int Int)) ())
      (BoundaryError T Int (R #false) (cdr (x (Pair Int Int)))))
     ((dynamic-typecheck T Bool (R 4) (x Bool) ())
      (BoundaryError T Bool (R 4) (x Bool)))
     ((dynamic-typecheck T (U Bool Int) (R 3) (x (U Bool Int)) ())
      3)
     ((dynamic-typecheck T (U Bool Int) (R #false) (x (U Bool Int)) ())
      #false)
     ((dynamic-typecheck T (U (→ Int Int) Int) (R 3) (x (U (→ Int Int) Int)) ())
      3)
     ((dynamic-typecheck T (U (→ Int Int) Int) (R (λ (x TST) 3)) (x (U (→ Int Int) Int)) ())
      (mon T (→ Int Int) (R (λ (x TST) 3)) ((proj 0) (x (U (→ Int Int) Int)))))
     ((dynamic-typecheck T (Box Int) (R (box z)) (x (Box Int)) ((z (BOX 3))))
      (mon T (Box Int) (R (box z)) (x (Box Int))))
     ((dynamic-typecheck T (Box (Pair Bool (→ Int Int))) (R (box q)) (f (Box (Pair Bool (→ Int Int)))) ((q (BOX (cons #true (λ (x Int) x))))))
      (mon T (Box (Pair Bool (→ Int Int))) (R (box q)) (f (Box (Pair Bool (→ Int Int))))))
    )
  )

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
     ((minimal-completion# (T 1))
      (T 1))
     ((minimal-completion# (R #true))
      (R #true))
     ((minimal-completion# (T #true))
      (T #true))
     ((minimal-completion# (R (λ (x TST) 4)))
      (R (λ (x TST) 4)))
     ((minimal-completion# (T (λ (x TST) 4)))
      (T (λ (x TST) 4)))
     ((minimal-completion# (R (cons 1 1)))
      (R (cons 1 1)))
     ((minimal-completion# (T (cons 1 1)))
      (T (cons 1 1)))
     ((minimal-completion# (R free-vars))
      (R free-vars))
     ((minimal-completion# (T freedom))
      (T freedom))
     ((minimal-completion# (R (mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
      (R (mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
     ((minimal-completion# (T (mon T (→ Int Int) (R (λ (x TST) (+ x 1))) (f (→ Int Int)))))
      (T (mon T (→ Int Int) (R (λ (x TST) (+ (dyn-check Int x ,d+) (dyn-check Int 1 ,dc+)))) (f (→ Int Int)))))
     ((minimal-completion# (R (pre-mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
      (R (pre-mon R (→ Int Int) (T (λ (x Int) x)) (f (→ Int Int)))))
     ((minimal-completion# (T (pre-mon T (→ Int Int) (R (λ (x TST) (+ x 1))) (f (→ Int Int)))))
      (T (pre-mon T (→ Int Int) (R (λ (x TST) (+ (dyn-check Int x ,d+) (dyn-check Int 1 ,dc+)))) (f (→ Int Int)))))
     ((minimal-completion# (R (let (x Int (T (+ 2 2))) (+ x x))))
      (R (let (x Int (T (+ 2 2))) (+ (dyn-check Int x ,d+) (dyn-check Int x ,dc+)))))
     ((minimal-completion# (T (let (x Int (R (+ 2 2))) (+ x x))))
      (T (let (x Int (R (+ (dyn-check Int 2 ,d+) (dyn-check Int 2 ,dc+)))) (+ x x))))
     ((minimal-completion# (R (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (R (if (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)))))
     ((minimal-completion# (T (if (+ 1 1) (+ 1 1) (+ 1 1))))
      (T (if (+ 1 1) (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (and (+ 1 1) (+ 1 1))))
      (R (and (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)) (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+)))))
     ((minimal-completion# (T (and (+ 1 1) (+ 1 1))))
      (T (and (+ 1 1) (+ 1 1))))
     ((minimal-completion# (R (let (n1 TST (R #false)) n1)))
      (R (let (n1 TST (R #false)) n1)))
     ((minimal-completion# (R (= #true 2)))
      (R (= (dyn-check Int #true ,d=) (dyn-check Int 2 ,dc=))))
     ((minimal-completion# (R (f x)))
      (R ((dyn-check → f (#%app (→ TST TST))) x)))
     ((minimal-completion# (T (f x)))
      (T (f x)))
     ((minimal-completion# (R (car 1)))
      (R (car (dyn-check Pair 1 (car (Pair TST TST))))))
     ((minimal-completion# (T (car 1)))
      (T (car 1)))
     ((minimal-completion# (R (cdr 1)))
      (R (cdr (dyn-check Pair 1 (cdr (Pair TST TST))))))
     ((minimal-completion# (T (cdr 1)))
      (T (cdr 1)))
     ((minimal-completion# (R (+ 1 1)))
      (R (+ (dyn-check Int 1 ,d+) (dyn-check Int 1 ,dc+))))
     ((minimal-completion# (R (* 1 1)))
      (R (* (dyn-check Int 1 ,d*) (dyn-check Int 1 ,dc*))))
     ((minimal-completion# (R (- 1 1)))
      (R (- (dyn-check Int 1 ,d-) (dyn-check Int 1 ,dc-))))
     ((minimal-completion# (T (- 1 1)))
      (T (- 1 1)))
     ((minimal-completion# (T (* 1 1)))
      (T (* 1 1)))
     ((minimal-completion# (T (+ 1 1)))
      (T (+ 1 1)))
     ((minimal-completion# (R (= 1 1)))
      (R (= (dyn-check Int 1 ,d=) (dyn-check Int 1 ,dc=))))
     ((minimal-completion# (T (= 1 1)))
      (T (= 1 1)))
     ((minimal-completion# (R (box (+ 3 3))))
      (R (box (+ (dyn-check Int 3 ,d+) (dyn-check Int 3 ,dc+)))))
     ((minimal-completion# (T (box (+ 3 3))))
      (T (box (+ 3 3))))
     ((minimal-completion# (R (unbox (box 2))))
      (R (unbox (dyn-check Box (box 2) (unbox (Box TST))))))
     ((minimal-completion# (T (unbox (box 2))))
      (T (unbox (box 2))))
     ((minimal-completion# (R (set-box! (box 1) 2)))
      (R (set-box! (dyn-check Box (box 1) (set-box! (Box TST))) 2)))
     ((minimal-completion# (T (set-box! (box 1) 2)))
      (T (set-box! (box 1) 2)))
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
     ((erasure# (T 4))
      4)
     ((erasure# (R #true))
      #true)
     ((erasure# (R (cons 1 2)))
      (cons 1 2))
     ((erasure# (T (pre-mon T Int (T 3) (x Int))))
      (pre-mon T Int (T 3) (x Int)))
     ((erasure# (R (pre-mon T Int (R 3) (x Int))))
      (pre-mon T Int (R 3) (x Int)))
     ((erasure# (T (pre-mon R Int (T 3) (x Int))))
      (pre-mon R Int (T 3) (x Int)))
     ((erasure# (T (mon T Int (T 3) (x Int))))
      (mon T Int (T 3) (x Int)))
     ((erasure# (R (mon T Int (R 3) (x Int))))
      (mon T Int (R 3) (x Int)))
     ((erasure# (T (mon R Int (T 3) (x Int))))
      (mon R Int (T 3) (x Int)))
     ((erasure# (T (f x)))
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
     ((erasure# (T (= 3 3)))
      (= 3 3))
     ((erasure# (T (box 2)))
      (make-box 2))
     ((erasure# (T (make-box 2)))
      (make-box 2))
     ((erasure# (R (unbox 3)))
      (unbox 3))
     ((erasure# (R (set-box! (box 2) #false)))
      (set-box! (make-box 2) #false))
     ((erasure# (T (dyn-check Int 4 (x Int))))
      (dyn-check Int 4 (x Int)))
    )

    ;; TODO some issue with binding forms ... using weaker equality for now
    (check-mf-apply* #:is-equal? xerox=?
     ((erasure# (R (let (x (→ Int Int) (T (λ (y Int) (+ y 2)))) (x 3))))
      (let (x (pre-mon R (→ Int Int) (T (λ (y) (+ y 2))) (x (→ Int Int)))) (x 3)))
     ((erasure# (R (letrec (f (→ Int Int) (T (λ (y Int) (if (= 0 y) 0 (+ 1 (f 0)))))) (f 3))))
      (letrec (f (→ Int Int) (pre-mon R (→ Int Int) (T (λ (y) (if (= 0 y) 0 (+ 1 (f 0))))) (f (→ Int Int)))) (f 3)))
     ((erasure# (R (λ (x TST) (let (z (→ Int Int) (T (λ (y Int) y))) (z 45)))))
      (λ (x)
        (let (z (pre-mon R (→ Int Int) (T (λ (y) y)) (z (→ Int Int)))) (z 45))))
    )
  )

  (test-case "well-formed-monitor"
    (check-judgment-holds*
     (well-formed-monitor (mon R (→ Int Int) (T (λ (x) 3)) (f (→ Int Int))))
     (well-formed-monitor (mon R (Box Int) (T (box z)) (f (Box Int))))
     (well-formed-monitor (mon R (→ Int Int)
      (T (mon R (→ Bool Bool) (T (λ (x) 3)) (g (→ Bool Bool))))
      (f (→ Int Int))))
    )
    (check-not-judgment-holds*
     (well-formed-monitor (mon R Int (T 4) (f Int)))
     (well-formed-monitor (mon R (→ Int Int) (T (box z)) (f (→ Int Int))))
    )
  )
)
