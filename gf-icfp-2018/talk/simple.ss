#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - if NEPLS, need to clarify there's a paper here
;; - asumu text style package?
;; - leif stacks package?
;; - abstraction for HE1
;; - abstraction for 'main results' slide
;; - abstraction for typed/untyped world slide ... boundary-crossing
;; - abstraction for S/D definition
;; - page numbers, customize! (pslide macro?)

(require
  "src/gt-system.rkt"
  pict
  pict/convert
  ppict/2
  ppict/slideshow2
  slideshow/code
  racket/draw racket/runtime-path
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in racket/list make-list flatten))

;; =============================================================================

(define PAGENUM #true)
(define TITLESTR "A Spectrum of Type Soundness and Performance")

(define (string->color str)
  (or (send the-color-database find-color str)
      (raise-argument-error 'string->color "color-name?" str)))

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

(define (make-> str)
  (define tag (string->symbol (format "->~a" str)))
  (tag-pict (text (format "→~a" str) '() 20) tag))

(define ->H (make-> "H"))
(define ->E (make-> "E"))
(define ->1 (make-> "1"))

(define (do-show)
  (set-page-numbers-visible! PAGENUM)
  (parameterize ([current-main-font "Avenir"]
                 [current-font-size 32]
                 #;[current-titlet string->title]
                 #;[*current-tech* #true]
                )
;    (sec:title)
;    (sec:folklore-I)
;    (sec:gt-system-pre)
;    (sec:main-result)
;    (sec:embeddings)
    (sec:implementation)
#;    (sec:graph)
#;    (sec:folklore-II)
#;    (sec:conclusion)

    ;(sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

(define (sec:title)
  (pslide
    ;; TODO racket-logo title slide ... make package for that
    @text[TITLESTR (current-main-font) (+ (current-font-size) 10)]
    @t{Ben Greenman & Matthias Felleisen}
    @t{PLT @"@" Northeastern University}
    @comment{
hello this paper is about gradual typing but this talk is really about two
pieces of folklore ....
    })
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

(define (sec:gt-system-pre)
  (pslide
    #:title "(by date)"
    #:go (coord 0 0)
    (make-gtspace-bg)
    #:go (coord 1/2 1/2)
    (let ([by-date* (sort all-system* < #:key gt-system-year)])
      (for/fold ((acc (blank 10 0)))
                ((x (in-list by-date*)))
        (hc-append 10 acc (gt-system->pict x)))))
  (pslide
    #:title "(by language)"
    #:go (coord 0 0)
    (make-gtspace-bg)
    #:go (coord 1/2 1/2)
    (let ([by-lang** (group-by gt-system-host-lang all-system*)])
      (for/fold ((acc (blank 10 0)))
                ((x* (in-list by-lang**)))
        (hc-append 10 acc (apply vl-append (map gt-system->pict x*))))))
  (pslide
    #:title "(by academia vs industry)"
    #:go (coord 0 0)
    (make-gtspace-bg)
    #:go (coord 1/2 1/2)
    (let ([academic* (filter/source 'A all-system*)]
          [industry* (filter/source 'I all-system*)]
          [both* (filter/source '(A I) all-system*)])
      (hc-append 10
                 (apply vl-append (map gt-system->pict academic*))
                 (apply vl-append (map gt-system->pict both*))
                 (apply vl-append (map gt-system->pict industry*)))))
  (pslide
    #:title "(by sound vs. unsound)"
    #:go (coord 0 0)
    (make-gtspace-bg)
    #:go (coord 1/2 1/2)
    (hc-append 50
               (apply vl-append (map gt-system->pict E-system*))
               (apply vl-append (map gt-system->pict (append H-system* 1-system* HE-system* 1E-system*)))))
  (pslide
    #:title "(by performance)"
    #:go (coord 1/2 1/2)
    (make-gtspace-bg)
    #:go (coord 1/2 1/2)
    (let ([dead* (filter-not/perf 90 all-system*)]
          [alive* (filter/perf 90 all-system*)])
      (hc-append 50 (apply vl-append (map gt-system->pict alive*))
                    (apply vl-append (map gt-system->pict dead*)))))
  (pslide
    @t{All bad})
  (void))

(define (sec:main-result)
  (pslide
    (make-embeddings-pict)
    #:next
    #:go (coord 1/2 1/2)
    #:alt [(file-icon (* 5/6 400) 400 "honeydew")]
    #:go (coord 1/2 1/2)
    (make-boundary-pict))
  (main-results-slide)
  (void))

(define (sec:embeddings)
  (pslide
    @t{Model})
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
  (pslide
    (make-sig-pict (make-step @t{dyn τ v} ->E @t{v}))
    (make-step @t{dyn τ v} ->E @t{v}))
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
    (make-embeddings-pict H-system* E-system* 1-system*))
  (pslide
    (make-embeddings-pict all-system*))
  (void))

(define (sec:implementation)
  (pslide
    @t{Implementation})
  (pslide
    #:alt [(make-embeddings-pict all-system*)]
    (make-embeddings-pict all-system* new-system*))

  ;; TR-N pipeline
  ;; TR-e pipeline
  ;; TR-1 pipeline
  ;; how to measure
  ;; benchmarks overview
  ;;  - as bullet points or a table? or garph to show size???
  (void))

(define (sec:graph)
  (pslide
    #:title "`Typical Program'"
    @t{TBA}
    @comment{
      gee lets just use plot!
      H first
      E next
      1 last
      intersections
    })
  (void))

(define (sec:folklore-II)
  (pslide
    #:title "Folklore"
    @item{Type soundness is all-or-nothing}
    @item{Adding types can only improve performance}
    @comment{
      ONLY true for single language
    })
  (pslide
    #:title "Revised Folklore"
    @item{Type soundness is about invariants, may not be desirable}
    @item{Perf ~ Inv(t) * Opt/Dyn}
    @comment{
      ONLY true for single language
    })
  (void))

(define (sec:conclusion)
  (pslide
    @t{conclusions}
    )
  (pslide
    @t{for theoretician}
    @comment{
      theorems too simplistic ... 2 languages!
    })
  (pslide
    @t{for language implementor}
    @comment{
      complicated landscape, subject to change, more to be done!
      vague rule of thumb based on our eval ... use your judgment and do a controlled experiment
      ??
    })
  (pslide
    @t{for developer}
    @comment{
      3 kinds of boundaries
      letting things through
      when violation occurs where to look?
    })
  (pslide
    ;; main slide
    #:title "Scientific Foundation for Typed/Untyped Interaction"
    @item{1 language, static + dynamic typing}
    @item{3 formal semantics}
    @item{3 **pairs** of type soundness theorems}
    @item{3 models, 3 implementations}
    @comment{
the end thank you
    })
  (void))

(define (sec:extra)
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
  (file-icon (* 5/6 h) h c))

(define (make-gtspace-bg)
  (cellophane (filled-rectangle client-w client-h #:color "darkcyan") 0.2))

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

(define (make-icon i #:height h)
  (bitmap (i #:material plastic-icon-material #:height h)))

(define (make-step lhs -> rhs)
  (hc-append 20 lhs -> rhs))

(define (make-example-boundary-pict)
  (make-boundary-pict #:left (hc-append @t{f} (make-hole))
                      #:right @t{⟨-1, -2⟩}
                      #:arrow @t{Nat}))

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit)

  (test-case "yolo"
    (check-true #true)))
