#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - if NEPLS, need to clarify there's a paper here
;; - asumu text style package?
;; - abstraction for HE1
;; - abstraction for 'main results' slide
;; - abstraction for typed/untyped world slide ... boundary-crossing
;; - abstraction for S/D definition
;; - page numbers, customize! (pslide macro?)

(require
  "src/gt-system.rkt"
  pict pict/convert
  ppict/2
  scribble-abbrevs/pict
  slideshow/code
  plot/no-gui plot/utils
  racket/draw racket/runtime-path
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in racket/list make-list flatten))

;; =============================================================================

(define PAGENUM #true)
(define TITLESTR "A Spectrum of Type Soundness and Performance")

(define (string->color str)
  (or (send the-color-database find-color str)
      (raise-argument-error 'string->color "color-name?" str)))

(define (triplet->color rgb)
  (make-object color% (car rgb) (cadr rgb) (caddr rgb)))

(define BROWN (string->color "chocolate"))
(define GREEN (string->color "mediumseagreen"))
(define BLUE (string->color "cornflowerblue"))
(define DARK-BLUE syntax-icon-color)
(define RED (string->color "firebrick"))
(define WHITE (string->color "Snow"))
(define RAY-COLOR RED)
(define BOX-COLOR (string->color "bisque"))
(define FF-COLOR (string->color "forestgreen"))
(define BLACK (string->color "black"))
(define GREY (string->color "gray"))
(define DARK-GREY (string->color "DarkSlateGray"))
(define DYN-COLOR WHITE)
(define STAT-COLOR DARK-GREY)

(define FILE-RATIO 5/6) ;; TODO nonsense
(define PLOT-RATIO 3/4) ;; TODO nonsense

(define (make-> str)
  (define tag (string->symbol (format "->~a" str)))
  (tag-pict (text (format "→~a" str) '() 20) tag))

(define ->racket (make-> "racket")) ;; TODO racket logo
(define ->H (make-> "H"))
(define ->E (make-> "E"))
(define ->1 (make-> "1"))

(define-syntax-rule (define-static-pict pict-name pict-path)
  (begin
    (define-runtime-path internal-pict-name pict-path)
    (define pict-name (scale-to-fit (bitmap internal-pict-name) 80 80))))

(define-static-pict racket-logo "./src/racket-logo.png")
(define-static-pict neu-logo "./src/neu-seal.png")

(define (do-show)
  (set-page-numbers-visible! PAGENUM)
  (parameterize ([current-main-font "Avenir"]
                 [current-font-size 32]
                 #;[current-titlet string->title]
                 #;[*current-tech* #true]
                )
    ;(sec:title)
    ;(sec:folklore-I)
    (sec:gt-landscape)
    ;(sec:main-result)
    ;(sec:embeddings)
    ;(sec:implementation)
    ;(sec:graph)
    ;(sec:conclusion)
    ;(sec:folklore-II)
    (sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

(define (sec:title)
  (pslide
    ;; TODO racket-logo title slide ... make package for that
    @text[TITLESTR (current-main-font) (+ (current-font-size) 10)]
    @t{Ben Greenman & Matthias Felleisen}
    (hc-append 40 @t{PLT} racket-logo)
    (hc-append 40 @t{Northeastern University} neu-logo))
  (void))

(define (sec:folklore-I)
  (pslide
    #:title "Folklore"
    ;; TODO think about these, then ask matthias
    @item{Type soundness is all-or-nothing}
    @item{Adding types can only improve performance}
    @comment{
    })
  (void))

(define (group-gt-systems-by sel <)
  (define g** (filter-not null? (group-by sel all-system*)))
  (sort g** < #:key (compose1 sel car)))

(define (make-categories-pict title sel elem< #:show-label? [pre-show-label? #true])
  (define title-pict (t (format "Typed/Untyped Languages (~a)" title)))
  (define gt** (group-gt-systems-by sel elem<))
  (define num-groups (length gt**))
  (define show-label? (if (< num-groups 10) pre-show-label? #f))
  (define names-v10 9)
  (define names-v1 (/ names-v10 10))
  (define-values [nat->x nat->y]
    (cond
      [(< num-groups 4)
       (define x-offset (/ 1 (+ 1 num-groups)))
       (values (lambda (x)
                 (* x-offset x))
               (lambda (y)
                 (- 1 names-v1)))]
      [else
       (define x-offset (/ 1 (+ 1 num-groups)))
       (values (lambda (x)
                 (* x-offset x))
               (lambda (y)
                 (- names-v1 (/ (+ 1 (modulo (+ 2 (* 3 y)) names-v10)) 10))))]))
  (parameterize ((current-font-size (- (current-font-size) 10)))
    (vl-append
      title-pict
      (ppict-do
        (make-gtspace-bg)
        #:set (for/fold ((p ppict-do-state))
                        ((i (in-naturals 1))
                         (gt* (in-list gt**)))
                (define cat (sel (car gt*)))
                (define name* (make-stack #:v 10 #:bg (blank) (map gt-system-name gt*)))
                (define x-pos (nat->x i))
                (define y-pos (nat->y i))
                (ppict-add
                  (ppict-go
                    (if show-label?
                      (ppict-add (ppict-go p (coord x-pos 0.04))
                                 (add-border (t (format "~a" cat))))
                      p)
                    (coord x-pos y-pos 'ct))
                  name*))))))

(define (sec:gt-landscape)
  ;; TODO add header slide? I think not
  (pslide
    #:alt [(make-categories-pict "by Date" gt-system-year <)]
    #:alt [(make-categories-pict "by Host Language" gt-system-host-lang (lambda (x y) #t))]
    #:alt [(make-categories-pict "Academia vs. Industry" gt-system-source gt-system-source< #:show-label? #false)]
    #:alt [(make-categories-pict "Sound vs. Unsound" gt-system-embedding%E (lambda (x y) (eq? x 'E)) #:show-label? #false)]
    (make-categories-pict "Alive vs. Dead" gt-system-name%TR (lambda (x y) (string=? y "Typed Racket")) #:show-label? #false))
  (pslide
    ;; TODO prettier
    @t{All bad!})
  (void))

(define (sec:main-result)
  (pslide
    (make-embeddings-pict)
    #:next
    #:go (coord 1/2 1/2)
    #:alt [(file-icon (* FILE-RATIO 400) 400 "honeydew")]
    #:go (coord 1/2 1/2)
    (make-boundary-pict))
  (main-results-slide)
  (void))

(define (sec:embeddings)
  (pslide
    (make-section-header "Model"))
  (embedding:warmup)
  (embedding:H)
  (embedding:E)
  (embedding:1)
  (embedding:end)
  (void))

(define (embedding:warmup)
  (pslide
    @t{Types}
    @t{τ = Nat | Int | τ × τ | τ → τ}
    @t{Nat <: Int}
    #:next
    @t{Values}
    @t{v = n | i | ⟨v,v⟩ | λ(x)e}
    @t{n ⊂ i}
    #:next
    @t{e = .... | dyn τ e | stat τ e}
    @comment{
    })
  (pslide
    @hb-append[40 (make-sig-pict @t{⊢ e : τ}) (make-sig-pict @t{⊢ e})]
    @hb-append[
      40
      @inferrule[@t{⊢ e}
                 @t{⊢ dyn τ e : τ}]
      @inferrule[@t{⊢ e : τ}
                 @t{⊢ stat τ e}]])
  (pslide
    @t{f (dyn (Nat × Nat) ⟨-1,-2⟩)}
    #:next
    @t{Γ = f : Nat × Nat → Nat}
    @inferrule[@t{...} ;; show derivation up to use of ⊢ _ ?
               @t{Γ ⊢ f (dyn (Nat × Nat) ⟨-1, -2⟩) : Nat}])
  (pslide
    (make-boundary-pict #:left (hc-append @t{f} (make-hole))
                        #:right @t{⟨-1, -2⟩}
                        #:arrow @t{Nat}))
  (void))

(define (embedding:H)
  (pslide
    ;; TODO highlight H
    (make-embeddings-pict))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2)
    (big-x-icon))
  (pslide
    (make-sig-pict (make-step @t{dyn τ v} ->H @t{v}))
    (make-step @t{dyn Nat n} ->H @t{n})
    (make-step @t{dyn Int i} ->H @t{i})
    (make-step @t{dyn (τ0 × τ1) ⟨v0, v1⟩} ->H @t{⟨dyn τ0 v0, dyn τ1 v1⟩})
    (make-step @t{dyn (τd → τc) λ(x)e} ->H @t{λ(y)(stat τc ((λ(x)e) (dyn τd y)))})
    (make-step @t{dyn t v} ->H (little-x-icon)))
  (void))

(define (embedding:E)
  (pslide
    ;; TODO highlight E
    (make-embeddings-pict H-system*))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2)
    (big-check-icon))
  (pslide
    (make-sig-pict (make-step @t{dyn τ v} ->E @t{v}))
    (make-step @t{dyn Nat v} ->E @t{v})
    (make-step @t{dyn Int v} ->E @t{v})
    (make-step @t{dyn (τ0 × τ1) v} ->E @t{v})
    (make-step @t{dyn (τd → τc) v} ->E @t{v}))
  (void))

(define (embedding:1)
  (pslide
    ;; TODO highlight 1
    (make-embeddings-pict H-system* E-system*))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2)
    (big-check-icon))
  (transient-dyn-slide)
  (pslide
    #:title "Transient Invariant"
    (make-step @t{(λ(x:t)e) v} ->1 @t{e{x/v}})
    @t{if and only if ⊢ v : constructor-of(t)})
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/5)
    @t{f = λ(x)(first x)})
  (transient-dyn-slide)
  (void))

(define (embedding:end)
  (pslide
    #:alt [(make-embeddings-pict H-system* E-system* reticulated)
           (make-embeddings-pict H-system* E-system* 1-system*)]
    (make-embeddings-pict all-system*))
  (void))

(define (sec:implementation)
  (pslide
    (make-section-header "Implementation"))
  (pslide
    #:alt [(make-embeddings-pict all-system*)]
    (make-embeddings-pict all-system* new-system*))
  (pslide
    #:go (coord 1/2 2/5 'ct)
    #:alt [(vc-append (make-TR-stack)
                      (make-step @t{e+} ->racket @t{...}))]
    #:go (coord 2/5 2/5 'ct)
    (make-TR-H-stack)
    #:go (coord 3/5 2/5 'ct)
    (make-TR-E-stack)
    #:go (coord 4/5 2/5 'ct)
    (make-TR-1-stack)
    #:go (coord 1/2 4/5 'ct)
    (make-step @t{e+} ->racket @t{...}))
  (pslide
    #:go (coord 1/10 1/2 'ct)
    (make-mixed-typed-program 0)
    #:next
    #:go (coord 3/10 2/7 'ct)
    (make-mixed-typed-program 1)
    #:next
    #:go (coord 4/10 4/7 'ct)
    (make-mixed-typed-program 3)
    #:go (coord 8/10 1/2 'ct)
    (make-mixed-typed-program 8))
  (pslide
    #:title "Experiment"
    ;; TODO show details? names? size? yes please a table would be great
    @t{10 benchmark programs}
    @t{(range of sizes)}
    @t{Measure all mixed-typed combinations})
  (void))

(define (sec:graph)
  (pslide
    (make-section-header "Results"))
  (pslide
    #:title "`Typical Program'"
    #:alt [(make-overhead-plot '())]
    #:alt [(make-overhead-plot '(H))]
    #:alt [(make-overhead-plot '(H E))]
    (make-overhead-plot '(H E 1))
    ;; MORE RESEARCH NECESSARY
    )
  (void))

(define (sec:conclusion)
  (pslide
    (make-section-header "Conclusions")
    #:next
    @t{for: theory, systems, practice})
  (pslide
    #:title "Conclusions: for Theoreticians"
    @item{Soundness for a pair of languages is different than soundness for one language; requires a pair of theorems}
    @item{Useful to model different systems as different semantics instead of different compilers}
    @item{Compare semantics via simulation proofs}
    ;; what does confined, or Siek/Wadler, do to compare?
    )
  (pslide
    #:title "Conclusion: for Language Builders"
    @item{higher-order : large cost at boundaries, enables full optimizations}
    @item{first-order (with untyped values) : small cost in typed code, can trust type constructors}
    ;; confident can work for micro-benchmarks, less sure itll scale
    @item{More to learn!}
    )
  (pslide
    #:title "Conclusion: for Programmers"
    @item{Erasure (and others) helps for writing code}
    @item{Higher-order helps debugging}
    @item{First-order is a best effort}
    )
  (void))

(define (sec:folklore-II)
  (pslide
    #:title "Folklore"
    @item{Type soundness is all-or-nothing}
    @item{Adding types can only improve performance})
  (pslide
    #:title "Revised Folklore"
    @item{Type soundness is about invariants, may not be desirable} ;; TODO re-word
    @item{Enforcing soundness adds a cost}
    ;; @item{Perf ~ Inv(t) * Opt/Dyn} ;; is this pundit equation really going to help anyone? this is still supposed to be a science talk
    )
  (pslide
    (make-section-header "The End"))
  (main-results-slide)
  (void))

(define (sec:extra)
  (pslide)
  ;; TODO
  #;(QA:kafka)
  #;(QA:...)
  #;(actual scatter plots)
  (void))

;; -----------------------------------------------------------------------------

(define (main-results-slide)
  (pslide
    @t{1 mixed-typed surface language}
    @t{3 semantics}
    ;; controlled experiment ... scientific results
    @t{MODEL: 3 pairs of soundness theorems}
    @t{IMPL: 3 datasets for the same benchmark programs}
    @t{EXAMPLES: 3 consequences for each program}
    @comment{
      in particular start with one surface language that admits
      typed code and untyped code, then define three ways of running a surface expression
      we call these strategies [higher-order erasure first-order] together they provide
      a nice foundation for understanding the literature
    })
  #;(pslide
    #:title "Scientific Foundation for Typed/Untyped Interaction"
    @item{1 language, static + dynamic typing}
    @item{3 formal semantics}
    @item{3 **pairs** of type soundness theorems}
    @item{3 models, 3 implementations}
    @comment{
    })
  (void))

(define (make-sig-pict p)
  (define sig-scale 1/10)
  (define sig-color BLUE)
  (define w+ (scale-* (pict-width p) sig-scale))
  (define h+ (scale-* (pict-height p) sig-scale))
  (cc-superimpose
    (filled-rounded-rectangle w+ h+ #:color sig-color)
    p))

(define (scale-* n s)
  (+ n (* n s)))

(define (make-boundary-pict #:left [left-pict #f] #:right [right-pict #f] #:arrow [arrow-pict (blank)])
  (define x-offset 1/7)
  (ppict-do
    (blank (/ client-w 2) (/ client-h 2))
    #:go (coord x-offset 1/2)
    (let ([stat-pict (tag-pict (make-component-file STAT-COLOR) 'stat-file)])
      (maybe-superimpose stat-pict left-pict))
    #:go (coord (- 1 x-offset) 1/2)
    (let ([dyn-pict (tag-pict (make-component-file DYN-COLOR) 'dyn-file)])
      (maybe-superimpose dyn-pict right-pict))
    #:set (let ((p ppict-do-state))
            (pin-arrows-line 10 p
                             (find-tag p 'stat-file) rc-find
                             (find-tag p 'dyn-file) lc-find
                             #:label arrow-pict))))

(define (maybe-superimpose base new)
  (if new
    (cc-superimpose base new)
    base))

(define (make-component-file c)
  (define h 180)
  (file-icon (* FILE-RATIO h) h c))

(define (make-gtspace-bg)
  (define mw (* 2 margin))
  (define mh (* 4 mw))
  (cellophane (filled-rectangle (- client-w mw) (- client-h mh) #:color "darkcyan") 0.2))

(define (make-base-embeddings-pict)
  (ppict-do
    (make-gtspace-bg)
    #:go (coord 1/4 1/4)
    (make-embedding-box ->H RED)
    #:go (coord 3/4 1/2)
    (make-embedding-box ->E BLUE)
    #:go (coord 1/4 3/4)
    (make-embedding-box ->1 GREEN)))

(define (make-embedding-box -> color)
  (ppict-do
    (filled-rectangle 100 100 #:color color)
    #:go (coord 1/2 1/2)
    ->))

(define (make-embeddings-pict . gt-system-tree)
  ;; TODO draw the tree nodes!!
  ;(define gt* (flatten gt-system-tree))
  ;(define H* (filter/embedding 'H gt*))
  ;(define E* (filter/embedding 'E gt*))
  ;(define 1* (filter/embedding '1 gt*))
  ;(define HE-system* (filter/embedding '(H E) gt*))
  ;(define 1E-system* (filter/embedding '(E 1) gt*))
  (make-base-embeddings-pict))

(define (transient-dyn-slide)
  (pslide
    (make-sig-pict (make-step @t{dyn τ v} ->1 @t{v}))
    (make-step @t{dyn Nat n} ->1 @t{n})
    (make-step @t{dyn Int i} ->1 @t{i})
    (make-step @t{dyn (τ0 × τ1) ⟨v0, v1⟩} ->1 @t{⟨v0, v1⟩})
    (make-step @t{dyn (τd → τc) λ(x)e} ->1 @t{λ(x)e})
    (make-step @t{dyn t v} ->1 (little-x-icon))))

(define (comment . stuff*)
  (blank 0 0))

(define (inferrule top bot)
  (vc-append 10
             top
             (hline (pict-width bot) 10)
             bot))

(define (make-hole)
  ;; so ugly, its incredible
  (define x @t{x})
  (filled-rectangle (pict-width x) (pict-height x) #:color WHITE))

(define (big-x-icon)
  (make-icon x-icon #:height 80))

(define (little-x-icon)
  (make-icon x-icon #:height 30))

(define (big-check-icon)
  (make-icon check-icon #:height 80))

(define (small-tau-icon)
  (t "τ"))

(define (make-icon i #:height h)
  (bitmap (i #:material plastic-icon-material #:height h)))

(define (make-step lhs -> rhs)
  (hc-append 20 lhs -> rhs))

(define (make-stack #:v [v 2] #:color [color BOX-COLOR] #:bg [pre-bg-pict #f] txt*)
  (define bg-pict (or pre-bg-pict (filled-rectangle 200 100 #:color color)))
  (for/fold ([acc (blank)])
            ([txt (in-list txt*)])
    (vc-append v
               acc
               (cc-superimpose
                 bg-pict
                 (t txt)))))

(define (make-example-boundary-pict)
  (make-boundary-pict #:left (hc-append @t{f} (make-hole))
                      #:right @t{⟨-1, -2⟩}
                      #:arrow @t{Nat}))

(define (make-typed-racket-stack title)
  (make-labeled-stack title
                      '("expand" "typecheck" "optimize" "enforce τ")
                      #:color BOX-COLOR))

(define (make-TR-stack)
  (make-typed-racket-stack "Typed Racket (TR-H)"))

(define (make-TR-H-stack)
  (make-typed-racket-stack "TR-H"))

(define (make-TR-E-stack)
  (make-labeled-stack "TR-E"
                      '("expand" "typecheck" "erase")
                      #:color RED))

(define (make-TR-1-stack)
  (make-labeled-stack "TR-1"
                      '("expand" "typecheck" "defend")
                      #:color BLUE))

(define (make-labeled-stack title txt* #:color c)
  (vc-append (t title)
             (make-stack txt* #:color c)))

(define make-mixed-typed-program
  (let ((rng (make-pseudo-random-generator)))
    (lambda (num-types)
      (define h 100)
      (parameterize ((current-pseudo-random-generator rng))
        (random-seed 11)
        (ppict-do
          (file-icon (* FILE-RATIO h) h "honeydew")
          #:set (for/fold ((p ppict-do-state))
                          ((_ (in-range num-types)))
                  (ppict-add (ppict-go p (coord (random) (random))) (small-tau-icon))))))))

(define (make-overhead-plot e*)
  (define w 500)
  (define x-min 0)
  (define x-max pi)
  (parameterize ((plot-x-ticks no-ticks)
                 (plot-y-ticks no-ticks))
    (plot-pict
      (for/list ((e (in-list e*))
                 (i (in-naturals 1)))
        (function (make-embedding-function e x-min x-max)
                  #:color i))
      #:width 500
      #:height (* PLOT-RATIO w)
      #:x-min x-min
      #:x-max x-max
      #:y-min 0
      #:y-max (* 10 (+ 1 (order-of-magnitude x-max)))
      #:x-label "Overhead vs. Untyped"
      #:y-label "Num. Type Ann.")))

(define (make-embedding-function e x-min x-max)
  (case e
    ((H)
     (lambda (n) (add1 (* 10 (sin n)))))
    ((E)
     (lambda (n) 1))
    ((1)
     (lambda (n) (add1 n)))
    (else
      (raise-argument-error 'make-embedding-line "embedding?" e))))

(define (rectangle/2t width height
                      #:border-width [border-width 1]
                      #:border-color [border-color BLACK]
                      #:color-1 [color-1 WHITE]
                      #:color-2 [color-2 BLACK])
  ;; thank you asumu https://www.asumu.xyz/blog/2018/03/31/making-the-most-of-lang-slideshow/
  (dc (λ (dc dx dy)
        (define old-brush
          (send dc get-brush))
        (define old-pen
          (send dc get-pen))
        (define gradient
          (make-object
           linear-gradient%
           dx dy
           dx (+ dy height)
           `((0 ,(make-object color% color-1))
             (1 ,(make-object color% color-2)))))
        (send dc set-brush
          (new brush% [gradient gradient]))
        (send dc set-pen
          (new pen% [width border-width]
                    [color border-color]))
        (send dc draw-rectangle dx dy width height)
        (send dc set-brush old-brush)
        (send dc set-pen old-pen))
      width height))

(define (client-w/margin)
  (+ client-w (* 2 margin)))

(define make-section-header
  (let ([ix (box 1)])
    (lambda (str)
      (define i (unbox ix))
      (set-box! ix (add1 i))
      (cc-superimpose
        (rectangle/2t (client-w/margin) 300 #:color-1 (triplet->color (->brush-color i)) #:color-2 "white")
        (text str "Fira Sans, Heavy" 60)))))

(define (gt-system-name%TR gt)
  (define n (gt-system-name gt))
  (if (string=? n "Typed Racket")
    n
    ""))

(define (gt-system-embedding%E gt)
  (define e (gt-system-embedding gt))
  (if (eq? e 'E)
    e
    'NA))

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit)

  (test-case "yolo"
    (check-true #true)))
