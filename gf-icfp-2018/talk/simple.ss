#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - if NEPLS, need to clarify there's a paper here ... also 17 min
;; - page numbers, customize! (pslide macro?)
;; - add micro/macro dyn/not knobs for ICFP

(require
  "src/gt-system.rkt" "src/constant.rkt"
  pict pict/convert pict/balloon
  ppict/2
  scribble-abbrevs/pict
  slideshow-text-style
  slideshow/code
  plot/no-gui plot/utils
  racket/draw
  racket/list
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style)

;; =============================================================================

;; -----------------------------------------------------------------------------

(define (do-show)
  (set-page-numbers-visible! PAGENUM)
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size 32]
                 [current-titlet string->title]
                 #;[*current-tech* #true]
                )
    (void)
    ;(sec:title)
    ;(sec:folklore-I)
    (sec:gt-landscape)
    ;(sec:kafka) ;; shout out for NEPLS
    ;(sec:main-result)
    ;(sec:embeddings)
    ;(sec:implementation)
    ;(sec:graph)
    ;(sec:conclusion)
    ;(sec:folklore-II)
    ;(pslide (make-section-header "The End"))
    ;(main-results-slide)
    ;(sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

(define (make-plt-title-background _w _h)
  (define w (* 4/5 client-w))
  (scale-to-fit (cellophane (bitmap racket-logo.png) WATERMARK-ALPHA) w w))

(define (string->title str)
  (colorize (text str TITLE-FONT 55) BLACK))

(define (sec:title)
  (pslide
    #:go (coord 1/5 2/5)
    (make-plt-title-background client-w client-h)
    #:go (coord 7/8 8/10)
    (scale-to-fit (cellophane (bitmap neu-logo.png) WATERMARK-ALPHA) 300 300)
    #:go (coord SLIDE-LEFT 1/2 'lb)
    @titlet{A Spectrum of Type Soundness}
    @titlet{and Performance}
    #:go (coord SLIDE-RIGHT SLIDE-BOTTOM 'rb)
    (vl-append 10
               @t{Ben Greenman & Matthias Felleisen}
               @t{Northeastern University}))
  (void))

(define (sec:folklore-I)
  (make-folklore-slide)
  (void))

(define (sec:gt-landscape)
  (define lambda-pict (large-lambda-icon))
  (define tau (large-tau-icon))
  (define dyn-file (make-dyn-file lambda-pict))
  (pslide
    (make-section-header "Migratory Typing"))
  (pslide
    #:go (coord 1/2 1/2)
    #:alt [dyn-file
           #:next
           #:go (at-find-pict 'dyn-file lc-find 'rc #:abs-x -10)
           tau]
    (hc-append 40 (make-stat-file tau) dyn-file))
  (make-gtspace-slide)
  (make-gtspace-slide
    all-system*)
  (make-gtspace-slide
    all-system*
    #:title '("by Date" "Oldest" "Newest")
    #:layout year-gt-layout)
  (make-gtspace-slide
    all-system*
    #:title '("by Creator" "Academia" "Industry")
    #:layout creator-gt-layout)
  (make-gtspace-slide
    all-system*
    #:title '("by Theory" "Sound" "Unsound")
    #:layout theory-gt-layout)
  (make-gtspace-slide
    all-system*
    #:title '("by Performance" "Not Dead" "Dead")
    #:layout performance-gt-layout)
  (pslide
    ;; TODO prettier ... outline-flash ?
    @titlet{Chaos!})
  (void))

(define (sec:kafka)
  ;; TODO prettier
  (pslide
    #:go (coord SLIDE-LEFT 1/2 'lb)
    @t{KafKa: Gradual Typing for Objects}
    @t{Chung, Li, Zappa Nardelli, Vitek}
    @t{ECOOP 2018}))

(define (sec:main-result)
  (pslide
    (make-embeddings-pict))
  (pslide
    #:go (coord 1/2 1/2)
    #:alt [(make-mixed-typed-program 6 #:height 200)]
    #:alt [(make-boundary-pict #:left (large-tau-icon) #:right (large-lambda-icon) #:arrow #false)]
    (make-boundary-pict #:left (large-tau-icon) #:right (large-lambda-icon) #:arrow (make-large-focus-icon)))
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
  (define x-offset 1/20)
  (pslide
    #:go (coord x-offset 1/5 'lt)
    ;;@t{Types}
    @t{τ = Nat | Int | τ × τ | τ → τ}
    @t{Nat <: Int}
    #:next
    #:go (coord (- 1 x-offset) 1/5 'rt)
    ;;@t{Values}
    @t{v = n | i | ⟨v,v⟩ | λ(x)e | λ(x:τ)e}
    @t{n ⊂ i}
    #:next
    #:go (coord 1/2 2/5)
    @t{e = .... | dyn τ e | stat τ e}
    #:next
    ;;@hb-append[40 (make-sig-pict @t{⊢ e : τ}) (make-sig-pict @t{⊢ e})]
    #:go (coord 1/2 3/5)
    @hb-append[
      100
      @inferrule[@t{⊢ e}
                 @t{⊢ dyn τ e : τ}]
      @inferrule[@t{⊢ e : τ}
                 @t{⊢ stat τ e}]])
  (pslide
    #:go (coord 1/2 1/5)
    @t{f (dyn (Nat × Nat) ⟨-1,-2⟩)}
    #:next
    #:go (coord 1/2 2/5 'ct)
    @inferrule[@t{...} ;; show derivation up to use of ⊢ _ ?
               (hb-append 10
                 (text "f : Nat × Nat → Nat" (current-main-font) (- (current-font-size) 6))
                 @t{⊢ f (dyn (Nat × Nat) ⟨-1, -2⟩) : Nat})])
  (pslide
    (make-example-boundary-pict))
  (void))

(define (embedding:H)
  (pslide
    #:alt [(make-embeddings-pict)]
    (make-embeddings-pict #:highlight 'H))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2 'cb)
    (big-x-icon))
  (pslide
    #:go (coord 1/15 1/5 'lt)
    (make-sig-pict (make-step @t{dyn τ v} ->H @t{v}))
    #:go (coord 2/15 3/10 'lt)
    (make-embedding-table
      (list
        @t{dyn Nat n} ->H @t{n}
        @t{dyn Int i} ->H @t{i}
        @t{dyn (τ0 × τ1) ⟨v0, v1⟩} ->H @t{⟨dyn τ0 v0, dyn τ1 v1⟩}
        @t{dyn (τd → τc) λ(x)e} ->H @t{λ(y:τd)(dyn τc ((λ(x)e) (stat τd y)))}
        @t{dyn τ v} ->H (little-x-icon))))
  (void))

(define (embedding:E)
  (pslide
    #:alt [(make-embeddings-pict)]
    #:alt [(make-embeddings-pict H-system*)]
    (make-embeddings-pict H-system* #:highlight 'E))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2 'cb)
    (big-check-icon))
  (pslide
    #:go (coord 1/15 1/5 'lt)
    (make-sig-pict (make-step @t{dyn τ v} ->E @t{v}))
    #:go (coord 2/15 3/10 'lt)
    (make-embedding-table
      (list
        @t{dyn Nat v} ->E @t{v}
        @t{dyn Int v} ->E @t{v}
        @t{dyn (τ0 × τ1) v} ->E @t{v}
        @t{dyn (τd → τc) v} ->E @t{v})))
  (void))

(define (embedding:1)
  (pslide
    #:alt ((make-embeddings-pict H-system*))
    #:alt ((make-embeddings-pict H-system* E-system*))
    (make-embeddings-pict H-system* E-system* #:highlight '1))
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/2 'cb)
    (big-check-icon))
  (transient-dyn-slide)
  #;(pslide
    #:title "Transient Invariant"
    (make-step @t{(λ(x:t)e) v} ->1 @t{e{x/v}})
    @t{if and only if ⊢ v : constructor-of(t)})
  (pslide
    (make-example-boundary-pict)
    #:next
    #:go (coord 1/2 1/5 'rt)
    @t{f = λ(x)(first x)})
  (transient-dyn-slide)
  (void))

(define (embedding:end)
  (pslide
    #:alt [(make-embeddings-pict H-system* E-system*)]
    #:alt [(make-embeddings-pict H-system* E-system* reticulated)]
    #:alt [(make-embeddings-pict H-system* E-system* 1-system*)]
    (make-embeddings-pict all-system*))
  (void))

(define (sec:implementation)
  (pslide
    (make-section-header "Experiment"))
  (pslide
    #:alt [(make-embeddings-pict all-system*)]
    (make-embeddings-pict all-system* new-system*))
  (pslide
    #:go (coord 1/2 1/5 'ct)
    #:alt [(vc-append (make-TR-stack)
                      (make-step @t{e+} ->racket @t{...}))]
    #:go (coord 1/8 1/5 'ct)
    (make-TR-H-stack)
    #:go (coord 1/2 1/5 'ct)
    (make-TR-E-stack)
    #:go (coord 7/8 1/5 'ct)
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
    @item{10 benchmark programs, 2-10 modules each}
    @item{Measure all mixed-typed combinations}
    @item{Compare overhead to untyped})
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
  (define-values [w h] (two-column-dims))
  (pslide
    (make-section-header "Conclusions")
    #:next
    @t{for: theory, systems, practice})
  (pslide
    #:title "Conclusions: for Theoreticians"
    (hc-append
      (ppict-do
        (blank w h)
        #:go (coord 1/10 3/10 'lt)
        @t{Soundness for a pair of languages}
        @t{is different than soundness for}
        @t{one language!})
  ;; @item{Useful to model different systems as different semantics instead of different compilers}
  ;  @item{Compare semantics via simulation proofs}
  ;  ;; what does confined, or Siek/Wadler, do to compare?
      (scale-to-fit
        (make-boundary-pict #:h 2/7 #:left (large-tau-icon) #:right (large-lambda-icon))
        w h))
    )
  (pslide
    #:title "Conclusions: for Language Implementors"
    (hc-append
      (ppict-do
        (blank w h)
        #:go (coord 1/10 3/10 'lt)
        @t{- How to predict overhead?}
        #:go (coord 1/10 4/10 'lt)
        @t{- Possible to change}
        @t{  landscape?})
      (scale-to-fit
        (make-overhead-plot '(H E 1))
        w h)))
  (pslide
    #:title "Conclusion: for Programmers"
    #:go (coord 1/10 1/5 'lt)
    @t{Invariants help catch bugs}
    #:go (coord 1/10 2/5 'lt)
    (hc-append 20 (scale (make-H-box) 3/4) @t{enforces types})
    #:go (coord 1/10 3/5 'lt)
    (hc-append 20 (scale (make-E-box) 3/4) @t{enforces nothing})
    #:go (coord 1/10 4/5 'lt)
    (hc-append 20 (scale (make-1-box) 3/4) @t{enforces type constructors})
    ;#:go (coord 1/10 6/10 'lt)
    #;@t{Many examples in the paper})
  (void))

(define (sec:folklore-II)
  (make-folklore-slide #:answers? #true)
  (void))

(define (sec:extra)
  (pslide)
  ;; TODO
  #;(QA:kafka)
  #;(QA:...)
  #;(actual scatter plots)
  (void))

;; -----------------------------------------------------------------------------

(define (two-column-dims)
  (values (/ client-w 2) (* 3/4 client-h)))

(define (main-results-slide)
  (define-values [w h] (two-column-dims))
  (define p/2 (blank w h))
  (pslide
    #:title "Contributions"
    #:go (coord 1/2 1/2)
    (hc-append
      (scale-to-fit
        (vc-append -40
          (make-boundary-pict #:h 2/7 #:left (large-tau-icon) #:right (large-lambda-icon))
          (hc-append 40 (make-H-box) (make-E-box) (make-1-box)))
        w h)
      (ppict-do
        p/2
        #:go (coord 0 3/10 'lt)
        @t{First systematic comparison of:}
        #:go (coord 0 4/10 'lt)
        @t{- type soundness theorems}
        #:go (coord 0 5/10 'lt)
        @t{- performance of mixed-}
        @t{  typed programs}
        ;#:go (coord 0 7/10 'lt)
        ;@t{Examples to illustrate the}
        ;@t{consequence for developers}
        )))
  (void))

(define (make-sig-pict p)
  (define sig-scale 2/10)
  (define sig-color LIGHT-BLUE)
  (define w+ (scale-* (pict-width p) sig-scale))
  (define h+ (scale-* (pict-height p) sig-scale))
  (cc-superimpose
    (filled-rounded-rectangle w+ h+ #:color sig-color)
    p))

(define (scale-* n s)
  (+ n (* n s)))

(define (make-boundary-pict #:left [left-pict #f]
                            #:right [right-pict #f]
                            #:h [x-offset 1/7]
                            #:arrow [arrow-pict (blank)])
  (ppict-do
    (blank (/ client-w 2) (/ client-h 2))
    #:go (coord x-offset 1/2)
    (make-stat-file left-pict)
    #:go (coord (- 1 x-offset) 1/2)
    (make-dyn-file right-pict)
    #:set (let ((p ppict-do-state))
            (if arrow-pict
              (pin-arrows-line 10 p
                               (find-tag p 'stat-file) rc-find
                               (find-tag p 'dyn-file) lc-find
                               #:y-adjust-label (+ 8 (pict-height arrow-pict))
                               #:label arrow-pict)
              p))))

(define (maybe-superimpose base new)
  (if new
    (cc-superimpose base new)
    base))

(define (make-component-file c)
  (define h 180)
  (file-icon (* FILE-RATIO h) h c))

(define (make-stat-file [super #f])
  (maybe-superimpose (tag-pict (make-component-file STAT-COLOR) 'stat-file) super))

(define (make-dyn-file [super #f])
  (maybe-superimpose (tag-pict (make-component-file DYN-COLOR) 'dyn-file) super))

(define (gt->pict gt)
  (define txt-p (text (gt-system-name gt) (current-main-font) 22))
  (define w (+ 10 (pict-width txt-p)))
  (define h (+ 10 (pict-height txt-p)))
  (cc-superimpose
    (filled-rectangle w h #:color "Gainsboro" #;"Light Steel Blue" #;"Orange")
    txt-p))

(define (add-gt-system* base gt* [pre-f-layout #f])
  (define gt-layout (or pre-f-layout random-gt-layout))
  (ppict-do base #:set (gt-layout ppict-do-state gt*)))

(define (random-gt-layout base gt*)
  (define p* (map gt->pict gt*))
  (define-values [base-w base-h] (values (pict-width base) (pict-height base)))
  (define x-sep 20)
  (define y-sep 100)
  (define x-base POOL-X-BASE)
  (define y-base POOL-Y-BASE)
  (for/fold ((acc base)
             (prev-x #false)
             (prev-y #false)
             #:result acc)
            ((p (in-list p*)))
          (define-values [x y align]
            (cond
              [(and prev-x (<= (+ prev-x (pict-width p)) base-w))
               (values prev-x prev-y (random-l-align))]
              [else
               (values x-base (if prev-y (+ prev-y y-sep) y-base) (random-l-align))]))
          (define c (coord (/ x base-w) (/ y base-h) align))
          (values (ppict-do acc #:go c p) (+ x (pict-width p) x-sep) y)))

(define (year-gt-layout base gt*)
  (define gt** (group-gt-systems-by gt* gt-system-year <=))
  (define x-base (/ POOL-X-BASE (pict-width base)))
  (define y-base (/ POOL-X-BASE (pict-height base)))
  (define x-offset (/ 1 (add1 (length gt**))))
  (define (get-y i)
    (vector-ref '#(0 8/30 19/30) (modulo i 3)))
  (ppict-do
    base
    #:set (for/fold ((acc ppict-do-state))
                    ((g* (in-list gt**))
                     (i (in-naturals)))
            (ppict-do
              acc
              #:go (coord (+ x-base (* i x-offset)) (+ y-base (get-y i)) 'lt)
              (gt*->pict g*)))))

(define (gt*->pict g*)
  (apply vc-append 8 (map gt->pict g*)))

(define (creator-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-source gt-system-source<)))

(define (theory-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-embedding%E (lambda (x y) (eq? y 'E)))))

(define (performance-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-name%TR (lambda (x y) (string=? y "Typed Racket")))))

(define (histogram-gt-layout base gt**)
  (define num-groups (length gt**))
  (define x-base (/ POOL-X-BASE (pict-width base)))
  (define y-base (/ POOL-X-BASE (pict-height base)))
  (define align*
    (if (< num-groups 2)
      '(lt)
      (append '(lt) (make-list (- num-groups 2) 'ct) '(rt))))
  (ppict-do
    base
    #:set (for/fold ((acc ppict-do-state))
                    ((x (in-list (linear-seq x-base (- 1 x-base) num-groups)))
                     (align (in-list align*))
                     (g* (in-list gt**)))
            (define h?-append (if (eq? align 'lt) hb-append ht-append))
            (ppict-do
              acc
              #:go (coord x y-base align)
              (let loop ([g* g*])
                ;; TODO 10 is magic number
                (if (< (length g*) 10)
                  (gt*->pict g*)
                  (let-values ([(a* b*) (split-at g* 10)])
                    (h?-append 4 (gt*->pict a*) (loop b*)))))))))

(define (label-text str)
  (define b (blank 10 0))
  (hc-append b (text str TITLE-FONT 26) b))

(define (make-gtspace-bg gt* [gt-layout #f])
  (define h (- client-h (* 2 1/5 client-h)))
  (define w (- client-w (* 2 SLIDE-LEFT client-w)))
  (cc-superimpose
    (cellophane (filled-rectangle (+ (* 2 margin) client-w) (+ margin h) #:color "DarkKhaki") 0.4)
    (add-gt-system* (filled-rounded-rectangle w h -1/5 #:color "AliceBlue") gt* gt-layout)))

(define (make-gtspace-slide [gt* '()] #:title [title #f] #:layout [gt-layout #f])
  (define top-margin -6)
  (define x-margin 40)
  (define arrow-size 12)
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
    (if title (blank) (text "Typed/Untyped Languages" TITLE-FONT 50))
    #:go (coord 1/2 1/2)
    (tag-pict (make-gtspace-bg gt* gt-layout) POOL-TAG)
    #:set (let ((p ppict-do-state))
            (if title
              (let ([left-label (label-text (cadr title))]
                    [right-label (label-text (caddr title))]
                    [center-label (label-text (car title))])
                (ppict-do p
                          #:go (at-find-pict POOL-TAG lt-find 'lb #:abs-y top-margin #:abs-x x-margin)
                          left-label
                          #:go (at-find-pict POOL-TAG rt-find 'rb #:abs-y top-margin #:abs-x (- x-margin))
                          right-label
                          #:go (at-find-pict POOL-TAG ct-find 'cb #:abs-y top-margin)
                          center-label
                          #:set (let ((p ppict-do-state))
                                  (pin-arrow-line
                                    arrow-size
                                    (pin-arrow-line
                                      arrow-size
                                      p
                                      center-label
                                      lc-find
                                      left-label
                                      rc-find)
                                    center-label
                                    rc-find
                                    right-label
                                    lc-find))))
              p))))

(define (make-base-embeddings-pict highlight)
  (ppict-do
    (make-gtspace-bg)
    #:go (coord 1/4 1/4)
    (maybe-highlight (make-H-box) (eq? highlight 'H))
    #:go (coord 3/4 1/2)
    (maybe-highlight (make-E-box) (eq? highlight 'E))
    #:go (coord 1/3 3/4)
    (maybe-highlight (make-1-box) (eq? highlight '1))))

(define (make-H-box)
  (make-embedding-box ->H LIGHT-RED))

(define (make-E-box)
  (make-embedding-box ->E GREEN))

(define (make-1-box)
  (make-embedding-box ->1 BLUE))

(define (maybe-highlight p yes?)
  (if yes?
    (let ((w (pict-width p))
          (h (pict-height p))
          (margin 20))
      (cc-superimpose
        (filled-rectangle (+ w margin) (+ h margin) #:color HIGHLIGHT-COLOR #:draw-border? #false)
        p))
    p))

(define (make-embedding-box -> color)
  (ppict-do
    (filled-rectangle 100 100 #:color color)
    #:go (coord 1/2 1/2)
    (scale -> 2)))

(define (make-embeddings-pict #:highlight [highlight #f] . gt-system-tree)
  (define gt* (flatten gt-system-tree))
  (define H* (filter/embedding 'H gt*))
  (define E* (filter/embedding 'E gt*))
  (define 1* (filter/embedding '1 gt*))
  (define HE-system* (filter/embedding '(H E) gt*))
  (define 1E-system* (filter/embedding '(E 1) gt*))
  (define p0 (make-base-embeddings-pict highlight))
  (define H-pos (find-tag p0 '->H))
  (define E-pos (find-tag p0 '->E))
  (define 1-pos (find-tag p0 '->1))
  (define margin 50)
  (parameterize ((current-font-size (- (current-font-size) 10)))
    (ppict-do
      p0
      #:go (at-find-pict H-pos lt-find 'rc #:abs-x (- margin))
      (make-name-stack H*)
      #:go (at-find-pict E-pos rt-find 'lc #:abs-x margin)
      (make-name-stack E*)
      #:go (at-find-pict 1-pos lt-find 'rt #:abs-x (- margin))
      (if (null? 1*)
        (blank)
        (make-name-stack (cons reticulated (filter-not/name "Reticulated" 1*))))
      #:set (let ((p ppict-do-state)
                  (HE-pict (make-name-stack HE-system*))
                  (1E-pict (make-name-stack 1E-system*)))
              (pin-line
                (pin-line
                  p
                  H-pos rc-find E-pos lt-find
                  #:y-adjust-label (- (/ (pict-height HE-pict) 2))
                  #:style (if (null? HE-system*) 'transparent 'short-dash)
                  #:label HE-pict)
                1-pos rc-find E-pos lb-find
                #:y-adjust-label (pict-height 1E-pict)
                #:style (if (null? 1E-system*) 'transparent 'short-dash)
                #:label 1E-pict)))))

(define (make-name-stack gt*)
  (make-stack #:v 10 #:bg (blank) (map gt-system-name gt*)))

(define (transient-dyn-slide)
  (pslide
    #:go (coord 1/15 1/5 'lt)
    (make-sig-pict (make-step @t{dyn τ v} ->1 @t{v}))
    #:go (coord 2/15 3/10 'lt)
    (make-embedding-table
      (list
        @t{dyn Nat n} ->1 @t{n}
        @t{dyn Int i} ->1 @t{i}
        @t{dyn (τ0 × τ1) ⟨v0, v1⟩} ->1 @t{⟨v0, v1⟩}
        @t{dyn (τd → τc) λ(x)e} ->1 @t{λ(x)e}
        @t{dyn τ v} ->1 (little-x-icon)))))

(define (comment . stuff*)
  (blank 0 0))

(define (inferrule top bot)
  (vc-append 10
             top
             (hline (pict-width bot) 10)
             bot))

(define (apply-to-hole f-pict)
  (hc-append 20 f-pict (make-hole)))

(define (make-hole)
  (define x @t{X})
  (define w (pict-width x))
  (filled-rectangle w w #:color GREY))

(define (big-x-icon)
  (make-icon x-icon #:height 80))

(define (little-x-icon)
  (make-icon x-icon #:height 30))

(define (big-check-icon)
  (make-icon check-icon #:height 80))

(define (small-tau-icon)
  (make-icon tau-icon #:height 40))

(define (large-tau-icon)
  (make-icon tau-icon #:height 90))

(define (tau-icon #:color [c TAU-COLOR] #:height [h (default-icon-height)] #:material [m (default-icon-material)])
  (text-icon "t" (make-font #:weight 'bold) #:color c #:height h #:material m))

(define (small-lambda-icon)
  (make-icon lambda-icon #:height 40))

(define (large-lambda-icon)
  (make-icon lambda-icon #:height 90))

(define (make-large-focus-icon)
  (make-icon magnifying-glass-icon #:height 90))

(define (make-small-focus-icon)
  (make-icon magnifying-glass-icon #:height 50))

(define (make-icon i #:height h)
  (bitmap (i #:material plastic-icon-material #:height h)))

(define (make-step lhs -> rhs)
  (hc-append 20 lhs -> rhs))

(define (make-embedding-table p*)
  (table
    3
    p*
    lc-superimpose
    cc-superimpose
    20 20))

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
  (make-boundary-pict #:left (apply-to-hole @t{f})
                      #:right @dyn-text{⟨-1, -2⟩}
                      #:arrow @t{Nat}))

(define (make-typed-racket-stack title)
  (make-labeled-stack title
                      '("expand" "typecheck" "optimize" "enforce τ")
                      #:color LIGHT-RED))

(define (make-TR-stack)
  (make-typed-racket-stack "Typed Racket (TR-H)"))

(define (make-TR-H-stack)
  (make-typed-racket-stack "TR-H"))

(define (make-TR-E-stack)
  (make-labeled-stack "TR-E"
                      '("expand" "typecheck" "erase")
                      #:color GREEN))

(define (make-TR-1-stack)
  (make-labeled-stack "TR-1"
                      '("expand" "typecheck" "defend")
                      #:color BLUE))

(define (make-labeled-stack title txt* #:color c)
  (vc-append (t title)
             (make-stack txt* #:color c)))

(define (make-mixed-typed-program num-types #:height [h 100])
  (random-seed 12)
  (define x* (linear-seq 0.1 0.9 num-types))
  (define y* (shuffle x*))
  (ppict-do
    (file-icon (* FILE-RATIO h) h "honeydew")
    #:set (for/fold ((p ppict-do-state))
                    ((x (in-list x*))
                     (y (in-list y*)))
            (ppict-add (ppict-go p (coord x y)) (small-tau-icon)))))

(define random-l-align
  (let ((state (box 0))
        (a* '#(lt lc lb)))
    (lambda ()
      (vector-ref a* (begin0 (modulo (unbox state) 3)
                             (set-box! state (+ (unbox state) 1))))))
  #;(case (random 3)
    [(0)
     'lt]
    [(1)
     'lc]
    [(2)
     'lb]
    [else
     (raise-user-error 'random-l-align "bad")]))

(define (make-overhead-plot e*)
  (define w 500)
  (define x-min 0)
  (define x-max pi)
  (parameterize ((plot-x-ticks no-ticks)
                 (plot-y-ticks no-ticks)
                 (plot-font-size (current-font-size)))
    (plot-pict
      (for/list ((e (in-list e*))
                 (c (in-list (list LIGHT-RED GREEN BLUE))))
        (function (make-embedding-function e x-min x-max)
                  #:width (* 15 (line-width))
                  #:alpha 0.6
                  #:color c))
      #:width 700
      #:height (* PLOT-RATIO w)
      #:x-min x-min
      #:x-max x-max
      #:y-min 0
      #:y-max (* 10 (+ 1 (order-of-magnitude x-max)))
      #:y-label "Overhead vs. Untyped"
      #:x-label "Num. Type Ann.")))

(define (make-embedding-function e x-min x-max)
  (case e
    ((H)
     (lambda (n) (max (if (< n 2) 1 0.4) (+ 0.5 (* 10 (sin n))))))
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
        (titlet str)))))

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

(define (dyn-text str)
  (text str (cons DYN-TEXT-COLOR (current-main-font)) (current-font-size)))

(define (neu)
  (hc-append 40 @t{Northeastern University}
             (scale-to-fit (bitmap neu-logo.png) 60 60)))

(define make-folklore-slide
  (let ([q1 "Is type soundness all-or-nothing?"]
        [q1-h 2/10]
        [a1 '("What invariants should the" "language guarantee?")]
        ;;
        [q2 "Can adding types slow down a program?"]
        [q2-h 5/10]
        [a2 '("Yes, through interaction with" "untyped code (or data)")])
    (lambda (#:answers? [answers? #false])
      (if answers?
        (pslide
          #:go (coord SLIDE-LEFT q1-h 'lt)
          (make-rumor-pict 'left q1)
          #:go (coord SLIDE-LEFT q2-h 'lt)
          (make-rumor-pict 'left q2)
          #:next
          #:go (coord SLIDE-RIGHT 31/100 'rt)
          (make-rumor-pict 'right a1)
          #:go (coord SLIDE-RIGHT 61/100 'rt)
          (make-rumor-pict 'right a2))
        (pslide
          #:go (coord SLIDE-LEFT q1-h 'lt)
          (make-rumor-pict 'left q1)
          #:go (coord SLIDE-LEFT q2-h 'lt)
          (make-rumor-pict 'left q2))))))

(define (string*->text str*)
  (if (string? str*)
    (t str*)
    (apply vl-append (map string*->text str*))))

(define (make-rumor-pict direction str*)
  (define balloon-tail-param 8)
  (define-values [spike +- c]
    (case direction
      [(left)
       (values 'sw - q-color)]
      [(right)
       (values 'se + a-color)]
      [else
       (raise-argument-error 'make-rumor-pict "direction?" direction)]))
  (define str-pict (string*->text str*))
  (define str-w (pict-width str-pict))
  (define str-h (pict-height str-pict))
  (define balloon-w (+ str-w 70))
  (define balloon-h (+ str-h 40))
  (ppict-do
    (balloon-pict (balloon balloon-w balloon-h balloon-tail-param spike (+- balloon-tail-param) balloon-tail-param c))
    #:go (coord 1/20 1/2 'lc)
    str-pict))

(define (group-gt-systems-by gt* sel <)
  (define g** (filter-not null? (group-by sel gt*)))
  (sort g** < #:key (compose1 sel car)))

(define (make-categories-pict title sel elem< #:show-label? [pre-show-label? #true])
  (define title-pict (t (format "Typed/Untyped Languages~a" (if title (string-append " (" title ")") ""))))
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

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit)

  (test-case "yolo"
    (check-true #true)))
