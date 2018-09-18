#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - add micro/macro dyn/not knobs for ICFP
;; - change desktop backgroup (and non-mirror background)

(require
  gf-icfp-2018/talk/src/gt-system gf-icfp-2018/talk/src/constant
  pict pict/convert pict/balloon pict/shadow
  ppict/2
  scribble-abbrevs/pict
  slideshow/code
  plot/no-gui plot/utils
  racket/draw
  racket/list
  (only-in racket/string string-split)
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in scribble/base url))
(require file/glob)

;; =============================================================================

(define current-component-ratio (make-parameter 1))

(define MAIN-CONTRIB-COORD (coord MAIN-CONTRIB-X 1/4 'lt))
(define -MAIN-CONTRIB-COORD (coord SLIDE-RIGHT 1/4 'rt))
(define ARROW-COORD (coord 1/2 1/2 'cb))

(define (do-show)
  (set-page-numbers-visible! #false)
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size 32]
                 [current-titlet string->title])
    (void)
    ;(sec:title)
    (sec:folklore-I)
    ;(sec:migratory-typing)
    ;(sec:gt-landscape)
    ;(sec:main-result)
    ;(pslide (make-section-header "Model"))
    ;(sec:embedding:warmup)
    ;(sec:embedding:H)
    ;(sec:embedding:1)
    ;(sec:embedding:E)
    ;(sec:embedding:end)
    ;(sec:soundness)
    ;(sec:implementation)
    ;(sec:performance)
    ;(sec:conclusion)
    ;(sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

(define (make-plt-title-background _w _h)
  (define w (* 4/5 client-w))
  (scale-to-fit (cellophane (bitmap racket-logo.png) WATERMARK-ALPHA) w w))

(define (string->title str #:size [size 55] #:color [color BLACK])
  (colorize (text str TITLE-FONT size) color))

(define (sec:title)
  (pslide
    #:go (coord 1/5 2/5)
    (make-plt-title-background client-w client-h)
    #:go (coord 7/8 8/10)
    (scale-to-fit (cellophane (bitmap neu-logo.png) WATERMARK-ALPHA) 300 300)
    #:go (coord SLIDE-LEFT 1/2 'lb)
    (vl-append 20
               (titlet "A Spectrum of Type Soundness")
               (titlet "and Performance"))
    #:go (coord SLIDE-RIGHT SLIDE-BOTTOM 'rb)
    (vl-append 15
               @t{Ben Greenman & Matthias Felleisen}
               @t{Northeastern University}))
  (void))

(define (sec:folklore-I)
  (make-folklore-slide)
  (void))

(define (sec:migratory-typing)
  (define lambda-pict (large-lambda-icon))
  (define tau (large-tau-icon))
  (define dyn-file (make-dyn-file lambda-pict))
  (pslide
    (make-section-header "Migratory Typing"))
  (pslide
    #:go (coord SLIDE-LEFT MAIN-CONTRIB-Y 'lt)
    @t{Step 0: un(i)typed language}
    #:go (coord 1/2 1/4 'ct)
    dyn-file)
  (pslide
    #:go (coord SLIDE-LEFT MAIN-CONTRIB-Y 'lt)
    @t{Step 1: idiomatic type system}
    #:go (coord 1/2 1/4 'ct)
    dyn-file
    #:go (at-find-pict 'dyn-file lc-find 'rc #:abs-x -10)
    tau)
  (pslide
    #:go (coord SLIDE-LEFT MAIN-CONTRIB-Y 'lt)
    @t{Step 2: mixed-typed language}
    #:go (coord 1/2 1/4 'ct)
    (stat-dyn/arrow))
  (void))

(define (sec:gt-landscape)
  (make-gtspace-slide)
  (pslide
    #:go (coord 1/2 1/2)
    (tag-pict (make-gtspace-bg all-system* random-gt-layout) POOL-TAG)
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
    #:alt [(heading-text "Typed/Untyped Languages")]
    ;; TODO add callouts
    (t "I am sound"))
  (pslide
    #:go (coord 1/2 1/2)
    (t "No more unsubstantiated claims")
    (t "Time to do science"))
  (void))

(define (sec:main-result)
  (define-values [model-pict0 impl-pict0] (make-model/impl-pict))
  (define contrib-0-pict
    (contrib*->pict
      '("Uniform Model:"
        ""
        "- one mixed-typed language"
        ""
        "- one surface type system"
        ""
        "- three semantics")))
  (define contrib-1-pict
    (contrib*->pict
      '("Soundness:" ;spectrum of?
        ""
        "- three evaluation-level"
        "  type systems"
        ""
        "- three notions of type"
        "  soundness")))
  ;; implications for programmer? ... 'soundness' is a little early, no?
  (define contrib-2-pict
    (contrib*->pict
      '("Performance:"
        ""
        "- Racket syntax/types"
        ""
        "- three compilers"
        ""
        "- systematic experiment")))
  (define model-pict
    (cc-superimpose
      (blank (pict-width contrib-1-pict) 0)
      (scale-for-column model-pict0)))
  (define model-pict- (scale model-pict 9/10))
  (define impl-pict (scale (cc-superimpose (blank 0 (pict-height model-pict-)) (scale-for-column impl-pict0)) 9/10))
  (pslide
    #:go (coord SLIDE-LEFT MAIN-CONTRIB-Y 'lt)
    @t{One mixed-typed language ...}
    #:go (coord 1/2 30/100 'ct)
    model-pict
    #:go (at-find-pict 'stat-file rb-find 'lc #:abs-x 2)
    (filled-rectangle 60 10 #:color "white" #:draw-border? #false)
    #:go (at-find-pict 'stat-file rb-find 'ct)
    (filled-rectangle 500 300 #:color "white" #:draw-border? #false))
  (pslide
    #:go (coord SLIDE-LEFT MAIN-CONTRIB-Y 'lt)
    @t{One mixed-typed language ... three semantics}
    #:go (coord 1/2 30/100 'ct)
    model-pict)
  (pslide
    #:go (coord 1/5 25/100 'lt)
    (let ([box+text (lambda (b t) (hc-append 20 b t))])
      (vl-append
        20
        (box+text (make-H-box) @t{higher-order semantics})
        (box+text (make-1-box) @t{first-order semantics})
        (box+text (make-E-box) @t{erasure semantics}))))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{Contributions (1/3)}
    #:go MAIN-CONTRIB-COORD
    (main-contrib-append
      model-pict-
      contrib-0-pict))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{Contributions (2/3)}
    #:go MAIN-CONTRIB-COORD
    (main-contrib-append
      model-pict-
      contrib-1-pict))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{Contributions (3/3)}
    #:go MAIN-CONTRIB-COORD
    #:alt [model-pict-
           #:go ARROW-COORD
           (large-right-arrow)]
    #:alt [model-pict-
           #:go ARROW-COORD
           (large-right-arrow)
           #:go -MAIN-CONTRIB-COORD
           impl-pict]
    contrib-2-pict
    #:go -MAIN-CONTRIB-COORD
    impl-pict)
  (define (big-text str)
    (text str TITLE-FONT 38))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{Contributions}
    #:go (coord SLIDE-LEFT 1/4 'lt)
    (contrib*->pict '(
      "- Uniform model"
      ""
      "- Spectrum of type soundness"
      ""
      "- Full-fledged implementation"))
    #:go (coord 1/2 6/10 'ct)
    (vc-append
      10
      (big-text "First apples-to-apples soundness")
      (big-text "and performance comparisons")))
  (void))

(define (sec:embedding:warmup)
  (define x-offset 1/20)
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    ;;@t{Types}
    (vl-append 10
               @t{τ = Nat | Int | τ × τ | τ ⇒ τ}
               @t{Nat <: Int})
    #:next
    #:go (coord SLIDE-LEFT 27/100 'lt)
    ;;@t{Values}
    (vl-append 10
               @t{v = n | i | ⟨v,v⟩ | λ(x)e | λ(x:τ)e}
               @t{n ⊂ i})
    #:next
    #:go (coord SLIDE-LEFT 45/100 'lt)
    @t{e = .... | dyn τ e | stat τ e}
    #:next
    #:go (coord 50/100 60/100 'ct)
    (let* ((dyn-pict @inferrule[@t{⊢ e} @t{⊢ dyn τ e : τ}])
           (stat-pict @inferrule[@t{⊢ e : τ} @t{⊢ stat τ e}])
           (stat-pict (cc-superimpose (blank (pict-width dyn-pict) 0) stat-pict)))
      ;; TODO add signatures ... I guess using pslide
      @hb-append[140 (tag-pict dyn-pict 'dyn-rule) (tag-pict stat-pict 'stat-rule)])
    #:go (at-find-pict 'dyn-rule lt-find 'rc #:abs-x 30)
    (make-sig-pict "⊢ e : τ")
    #:go (at-find-pict 'stat-rule lt-find 'rc #:abs-x 30)
    (make-sig-pict "⊢ e"))
  (define types-pict
    (vl-append 10
      @t{fib  : Nat ⇒ Nat}
      @t{norm : Nat × Nat ⇒ Nat}
      @t{map  : (Nat ⇒ Nat) ⇒ Nat × Nat ⇒ Nat × Nat}))
  (pslide
    #:go (coord 1/2 SLIDE-TOP 'ct)
    (vc-append
      100
      (insert-brace @t|{Γ = }| types-pict)
      (table 2 (list
        @t{Γ ⊢ fib  (dyn Nat -1)} @t{: Nat}
        @t{Γ ⊢ norm (dyn Nat × Nat ⟨-1,-2⟩)} @t{: Nat}
        @t{Γ ⊢ map  (dyn (Nat ⇒ Nat) (λ(x)-x)) y} @t{: Nat × Nat})
             lb-superimpose cb-superimpose 25 10)))
  (pslide
    (make-example-boundary-pict))
  (void))

(define (insert-brace p0 p1)
  ;(define b (text "{" (current-main-font) 70)) ;}
  (hc-append 25 p0 #;b p1))

(define (sec:embedding:H)
  (define arrow-target 'arrow-target)
  (pslide
    #:alt [(make-embeddings-pict)]
    (make-embeddings-pict #:highlight 'H))
  (make-H-example-slide)
  (make-example-detail-slide
    'H
    (make-boundary-pict #:left (hole-append @t{map} (small-monitor-icon) @t{y})
                        #:right @dyn-text{λ(x)-x}
                        #:arrow @t/crunch{Nat ⇒ Nat})
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (hole-append (small-monitor-icon) @t{1})
                          #:right (hc-append 2 (parameterize ((current-font-size 24)) @dyn-text{(λ(x)-x)}) (make-hole))
                          #:arrow @t{Nat}
                          #:reverse? #true))
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (make-hole)
                          #:right @dyn-text{-1}
                          #:arrow (tag-pict @t{Nat} arrow-target)))
    #:arrow-label (cons arrow-target (big-x-icon)))
  (void))

(define (sec:embedding:1)
  (define y-sep 6)
  (define arrow-style-1 'dot)
  (pslide
    #:alt ((make-embeddings-pict))
    #:alt ((make-embeddings-pict H-system*))
    (make-embeddings-pict H-system* #:highlight '1))
  (make-1-example-slide)
  (make-example-detail-slide
    '1
    (make-boundary-pict #:left (hole-append @t{norm} (small-check-icon))
                        #:right @dyn-text{⟨-1,-2⟩}
                        #:arrow @t/crunch{Nat × Nat})
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (hole-append @t{snd} (small-check-icon))
                          #:right @dyn-text{⟨-1,-2⟩}
                          #:arrow (blank)
                          #:arrow-style arrow-style-1
                          #:reverse? #true))
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (make-hole)
                          #:right @dyn-text{-2}
                          #:arrow-style arrow-style-1
                          #:arrow @t{Nat/Int})))
  (make-example-detail-slide
    '1
    (make-boundary-pict #:left (hole-append @t{map} (small-check-icon) @t{y})
                        #:right @dyn-text{λ(x)-x}
                        #:arrow @t/crunch{Nat ⇒ Nat})
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (hole-append (small-check-icon) @t{1})
                          #:right (hc-append 2 (parameterize ((current-font-size 24)) @dyn-text{(λ(x)-x)}) (make-hole))
                          #:arrow (blank)
                          #:arrow-style arrow-style-1
                          #:reverse? #true))
    (parameterize ((current-component-ratio 3/4))
      (make-boundary-pict #:left (make-hole)
                          #:right @dyn-text{-1}
                          #:arrow-style arrow-style-1
                          #:arrow (tag-pict @t{Nat/Int} 'lbl-2))))
  (void))

(define (sec:embedding:E)
  (define (add-arrow str)
    (hc-append 20 (arrow EVAL-ARROW-SIZE 0) (t str)))
  (pslide
    #:alt [(make-embeddings-pict H-system*)]
    #:alt [(make-embeddings-pict H-system* reticulated)]
    #:alt [(make-embeddings-pict H-system* 1-system*)]
    (make-embeddings-pict H-system* 1-system* #:highlight 'E))
  (make-E-example-slide)
  (define the-bomb (small-bomb-icon))
  (define (make-fib in-hole)
    (make-boundary-pict #:left (hole-append @t{fib} in-hole)
                        #:right @dyn-text{-1}
                        #:arrow @t{Nat}))
  (make-example-detail-slide
    'E
    (make-fib (cc-superimpose (blank (pict-width the-bomb) (pict-height the-bomb))
                              (small-check-icon)))
    (blank))
  (make-example-detail-slide
    'E
    (make-fib (small-bomb-icon))
    (vl-append 20
               (add-arrow "error?")
               (add-arrow "diverges?")
               (add-arrow "0")
               (add-arrow "???")))
  (let ((bb (lt-superimpose (vl-append (blank 0 30) (hc-append (blank 40 0) (big-bomb-icon)))
                            (big-check-icon))))
    (make-E-example-slide (make-example-boundary-pict bb bb bb)))
  (void))

(define (sec:embedding:end)
  (pslide
    #:alt [(make-embeddings-pict H-system* 1-system* E-system*)]
    (make-embeddings-pict all-system*))
  (void))

(define (sec:soundness)
  ;; TODO still droopy, things overall still look shitty
  (define model-pict
    (let-values (((mp _) (make-model/impl-pict)))
      (scale (scale-for-column mp) 9/10)))
  (define type-pict*
    (let* ([vdash* (map scale-for-bullet (list ⊢H ⊢1 ⊢E))]
           [t* (map (lambda (str) (if str (t str) #f)) '("τ" #f "K(τ)"))])
      (for/list ((vdash (in-list vdash*))
                 (t-pict (in-list t*))
                 (c (in-list (list H-COLOR 1-COLOR E-COLOR))))
        (define t+ (if t-pict (vl-append 6 (hc-append (t ":") t-pict) (blank)) (blank)))
        (define p (hc-append 2 vdash (hc-append (t "e") t+)))
        (vl-append p (filled-rectangle (pict-width p) 4 #:draw-border? #f #:color c)))))
  (define model-pict+
    (ppict-do
      model-pict
      #:set (for/fold ((acc ppict-do-state))
                      ((tag (in-list '(->H ->1 ->E)))
                       (type-pict (in-list type-pict*)))
              (ppict-do
                acc
                #:go (at-find-pict tag cb-find 'ct #:abs-y 30)
                type-pict))))
  (pslide
    (make-section-header "Soundness"))
  (make-folklore-slide #:q2? #false #:answers? #false)
  (make-folklore-slide #:q2? #false #:answers? #true)
  (define sound-text-pict
    (apply
      vl-append
      60
      (for/list ((sym (in-list '(H 1 E)))
                 (descr (in-list '(("progress & preservation"
                                    "for types")
                                   ("progress & preservation"
                                    "for type constructors")
                                   "progress & preservation"))))
        (define-values [txt bx] (symbol->name+box sym))
        (ht-append (lb-superimpose (blank 42 26) (scale-to-fit bx 30 30))
                   (string*->text descr)))))
  (pslide
    #:go MAIN-CONTRIB-COORD
    #:alt [model-pict]
    #:alt [model-pict+]
    model-pict+
    #:go -MAIN-CONTRIB-COORD
    sound-text-pict)
  (void))

(define (sec:implementation)
  (define-values [model-pict impl-pict]
    (let-values (((mp ip) (make-model/impl-pict)))
      (values (scale (scale-for-column mp) 9/10)
              (scale (scale-for-column ip) 9/10))))
  (pslide
    (make-section-header "Implementation"))
  (pslide
    #:go MAIN-CONTRIB-COORD
    model-pict
    #:go ARROW-COORD
    (large-right-arrow)
    #:go -MAIN-CONTRIB-COORD
    impl-pict)
  ;; implementation
  (define box*
    (list (make-TR-H-box) (make-TR-1-box) (make-TR-E-box)))
  (define x* '(1/5 1/2 4/5))
  (define stack-y 1/4)
  (pslide
    #:set (for/fold ((acc ppict-do-state))
                    ((b (in-list box*))
                     (x (in-list x*)))
            (ppict-do acc #:go (coord x SLIDE-TOP 'ct) b))
    #:next
    #:go (coord (car x*) stack-y 'ct)
    (make-TR-H-stack)
    #:next
    #:go (coord (cadr x*) stack-y 'ct)
    (tag-pict (make-TR-1-stack) 'TR-1)
    #:go (coord (caddr x*) stack-y 'ct)
    (make-TR-E-stack)
    #:next
    #:go (at-find-pict 'TR-1 cb-find 'ct #:abs-y 10)
    (vl-append (blank 0 20) (t "Optimize?")))
  (void))

(define (sec:performance)
  (pslide
    (make-section-header "Performance"))
  (make-folklore-slide #:q1? #false #:answers? #false)
  (pslide
    #:go (coord SLIDE-LEFT 1/4 'lt)
    @t{- 10 benchmark programs}
    #:go (coord SLIDE-LEFT (+ 1/4 1/10) 'lt)
    @t{- 2 to 10 modules each}
    #:go (coord SLIDE-LEFT (+ 1/4 2/10) 'lt)
    @t{- 4 to 1024 configurations each}
    #:go (coord SLIDE-LEFT (+ 1/4 3/10) 'lt)
    @t{- compare overhead to untyped}
    #:go (coord 1/2 (+ 1/4 4/10) 'ct)
    @url{docs.racket-lang.org/gtp-benchmarks})
  (make-overhead-plot-slide '())
  (pslide (make-scatterplots-pict))
  (make-folklore-slide #:q1? #false #:answers? #true)
  (define perf-plot-pict
    (let ((w (* 40/100 client-w)))
      (scale-to-fit (make-overhead-plot '(H 1 E) #:legend? #false) w w)))
  (define perf-text-pict
    (vl-append
      (blank 30)
      (apply
        vl-append
        60
        (for/list ((sym (in-list '(H 1 E)))
                   (descr (in-list '(("add types to remove all"
                                      "critical boundaries")
                                     "add types sparingly"
                                     ("add types anywhere,"
                                      "doesn't matter")))))
          (define-values [txt bx] (symbol->name+box sym))
          (ht-append (lb-superimpose (blank 55 26) (scale-to-fit bx 40 40))
                     (string*->text descr))))))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{For Performance}
    #:go MAIN-CONTRIB-COORD
    #:alt [perf-plot-pict]
    perf-plot-pict
    #:next
    #:go -MAIN-CONTRIB-COORD
    perf-text-pict)
  (void))

(define (make-scatterplots-pict)
  (scale-to-fit (bitmap cache-scatterplots.png) client-w client-h))

(define (sec:conclusion)
  (define (make-spectrum-delimiter)
    (filled-rectangle 6 20 #:color "black" #:draw-border? #f))
  (define spectrum-line-width 10)
  (define spectrum-x-offset 4)
  (define spectrum-H-offset 30)
  (define spectrum-E-offset (- spectrum-x-offset))
  (define spectrum-1-offset (- (* 25/100 client-w)))
  (define gt-pict (vl-append (heading-text ">") (blank 0 20)))
  (define model-pict
    (let-values (([model-pict0 impl-pict0] (make-model/impl-pict)))
      (scale (scale-for-column model-pict0) 9/10)))
  (pslide
    (make-section-header "Implications"))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @heading-text{For Theory}
    #:go (coord SLIDE-LEFT 1/2)
    (tag-pict (make-spectrum-delimiter) 'all-rect)
    #:go (coord SLIDE-RIGHT 1/2)
    (tag-pict (make-spectrum-delimiter) 'none-rect)
    #:set (let ((p ppict-do-state))
            (pin-line p (find-tag p 'all-rect) rc-find (find-tag p 'none-rect) lc-find
                      #:label (tag-pict (blank) 'lbl-tag)
                      #:line-width spectrum-line-width))
    #:go (at-find-pict/below 'lbl-tag #:abs-y (* 3.5 spectrum-line-width))
    (heading-text "Type violations discovered" 38)
    #:go (at-find-pict 'all-rect rb-find 'lt #:abs-x spectrum-x-offset)
    (label-text "All")
    #:go (at-find-pict 'none-rect lb-find 'rt #:abs-x spectrum-E-offset)
    (label-text "None")
    #:next
    #:go (at-find-pict 'all-rect rt-find 'lb #:abs-x spectrum-H-offset)
    (tag-pict (make-H-box) 'H-box)
    #:go (at-find-pict 'none-rect lt-find 'rb #:abs-x spectrum-E-offset)
    (tag-pict (make-E-box) 'E-box)
    #:go (at-find-pict 'none-rect lt-find 'rb #:abs-x spectrum-1-offset)
    (tag-pict (make-1-box) '1-box)
    #:set (let ((p ppict-do-state))
            (pin-line p (find-tag p 'H-box) rb-find (find-tag p '1-box) lb-find
                      #:label gt-pict
                      #:style 'transparent))
    #:set (let ((p ppict-do-state))
            (pin-line p (find-tag p '1-box) rb-find (find-tag p 'E-box) lb-find
                      #:label gt-pict
                      #:style 'transparent)))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    (heading-text "Special Thanks")
    #:go (coord 1/2 1/4 'ct)
    (arrange-authors (padded-bitmap 140) ack* 100 20 #true))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    #:go MAIN-CONTRIB-COORD
    model-pict
    #:go -MAIN-CONTRIB-COORD
    (contrib*->pict '(
      "- one surface language"
      ""
      "- three notions of"
      "  type soundness"
      ""
      "- full-fledged"
      "  implementation")))
  (void))

(define (sec:extra)
  (pslide (make-embeddings-pict all-system*))
  (make-H-example-slide)
  (make-1-example-slide)
  (make-E-example-slide)
  (pslide (make-scatterplots-pict))
  (make-kafka-slide)
  (void))

;; -----------------------------------------------------------------------------

(define (make-H-example-slide [bp #f])
  (define b-pict (or bp (make-example-boundary-pict (big-x-icon) (big-x-icon) (big-monitor-icon))))
  (make-?-example-slide "higher-order" (make-H-box) b-pict))

(define (make-E-example-slide [bp #f])
  (define b-pict (or bp (make-example-boundary-pict (big-check-icon) (big-check-icon) (big-check-icon))))
  (make-?-example-slide "erasure" (make-E-box) b-pict))

(define (make-1-example-slide [bp #f])
  (define b-pict (or bp (make-example-boundary-pict (big-x-icon) (big-check-icon) (big-check-icon))))
  (make-?-example-slide "first-order" (make-1-box) b-pict))

(define (make-?-example-slide name lbl b-pict)
  (define y-sep 6)
  (pslide
    #:go (coord 1/2 SLIDE-TOP 'ct #:abs-y y-sep)
    b-pict
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
    (t name)
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt #:abs-y y-sep)
    lbl))

(define (neu)
  (hc-append 40 @t{Northeastern University}
             (scale-to-fit (bitmap neu-logo.png) 60 60)))

(define (dyn-text str)
  (text str (cons DYN-TEXT-COLOR (current-main-font)) (current-font-size)))

(define (two-column-dims)
  (values (/ client-w 2) (* 3/4 client-h)))

(define (make-model/impl-pict)
  (define-values [w h] (two-column-dims))
  (define (smaller p)
    (scale-to-fit p (- w 80) (- h 80)))
  (define tu-pict (stat-dyn/arrow))
  (define m (smaller (make-1-on-3 tu-pict (make-H-box) (make-1-box) (make-E-box))))
  (define i
    (let* ((h (pict-height tu-pict))
           (rkt-pict (scale-to-fit (bitmap racket-logo.png) h h)))
      (smaller (make-1-on-3 rkt-pict (make-TR-H-box) (make-TR-1-box) (make-TR-E-box)))))
  (values m i))

(define (contrib*->pict str*)
  (for/fold ((p (blank)))
            ((str (in-list str*))
             (i (in-naturals)))
    (vl-append 10 p (if (pict? str) str (t str)))))

(define (main-contrib-append a b #:x-shift [x 0])
  (ht-append (+ x 10) a b))

(define (scale-* n s)
  (+ n (* n s)))

(define (make-boundary-pict #:left [left-pict #f]
                            #:right [right-pict #f]
                            #:h [x-offset 1/7]
                            #:arrow [arrow-pict (blank)]
                            #:arrow-style [arrow-style 'solid]
                            #:reverse? [reverse? #false])
  (define sf (make-stat-file left-pict))
  (define df (make-dyn-file right-pict))
  (define (make-arrow p src-tag src-find dst-tag dst-find)
    (pin-arrow-line 13 p
                    (find-tag p src-tag) src-find
                    (find-tag p dst-tag) dst-find
                    #:line-width 4
                    #:style arrow-style
                    #:label arrow-pict))
  (ppict-do
    (blank (/ client-w 2) (pict-height sf))
    #:go (coord x-offset 1/2)
    sf
    #:go (coord (- 1 x-offset) 1/2)
    df
    #:set (let ((p ppict-do-state))
            (if arrow-pict
              (if reverse?
                (make-arrow p 'stat-file rc-find 'dyn-file lc-find)
                (make-arrow p 'dyn-file lc-find 'stat-file rc-find))
              p))))

(define (maybe-superimpose base new)
  (if new
    (cc-superimpose base new)
    base))

(define (make-component-file c)
  (define h 180)
  (file-icon (* FILE-RATIO h) (* (current-component-ratio) h) c))

(define (make-stat-file [super #f])
  (maybe-superimpose (tag-pict (make-component-file STAT-COLOR) 'stat-file) super))

(define (make-dyn-file [super #f])
  (maybe-superimpose (tag-pict (make-component-file DYN-COLOR) 'dyn-file) super))

(define (gt->pict gt)
  (define mt? (gt-system-mt? gt))
  (define str
    (gt-system-name gt))
  (define-values [fg-color bg-color]
    (if mt?
      (values "black" "Gainsboro")
      (values "white" "Dim Gray")))
  (define txt-p
    (colorize (text str (current-main-font) 22) fg-color))
  (define w (+ 10 (pict-width txt-p)))
  (define h (+ 10 (pict-height txt-p)))
  (tag-pict
    (cc-superimpose
      (filled-rectangle w h #:color bg-color)
      txt-p)
    (string->symbol str)))

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
  (define-values [x-base y-base] (get-pool-margins base))
  (define x-offset (/ 1 (add1 (length gt**))))
  (define (get-y i)
    (vector-ref '#(0 30/100 59/100) (modulo i 3)))
  (ppict-do
    base
    #:set (for/fold ((acc ppict-do-state))
                    ((g* (in-list gt**))
                     (i (in-naturals)))
            (ppict-do
              acc
              #:go (coord (+ x-base (* i x-offset)) (+ y-base (get-y i)) 'lt)
              (gt*->pict g*)))))

(define (histogram-gt-layout base gt**)
  (define x-sep -2)
  (define num-groups (length gt**))
  (define-values [x-base y-base] (get-pool-margins base))
  (define max-in-column
    (let ((h-1 (* 1.2 (pict-height (gt->pict typed-racket))))
          (max-h (- (pict-height base) (* 2 y-base))))
      (- (exact-floor (/ max-h h-1)) 1)))
  (define align*
    (if (< num-groups 2)
      '(lt)
      (append '(lt) (make-list (- num-groups 2) 'ct) '(rt))))
  (define color*
    '("LightSteelBlue" "PaleGreen")) ;; "LightCoral" "Thistle" ... too close in black/white
  (ppict-do
    base
    #:set (for/fold ((acc ppict-do-state))
                    ((x (in-list (linear-seq x-base (- 1 x-base) num-groups)))
                     (align (in-list align*))
                     (g* (in-list gt**))
                     (bg-c (in-cycle (in-list color*))))
            (define h?-append (if (eq? align 'lt) hb-append ht-append))
            (ppict-do
              acc
              #:go (coord x y-base align)
              (let loop ([g* g*])
                (cond
                  [(null? g*)
                   (blank)]
                  [(< (length g*) max-in-column)
                   (gt*->pict g* #:bg-color bg-c)]
                  [else
                   (let-values ([(a* b*) (split-at g* max-in-column)])
                     (h?-append x-sep (gt*->pict a* #:bg-color bg-c) (loop b*)))]))))))

(define (creator-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-source gt-system-source<)))

(define (theory-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-embedding%E (lambda (x y) (eq? y 'E)))))

(define (performance-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-name%TR (lambda (x y) (string=? y "Typed Racket")))))

(define (gt*->pict g* #:bg-color [bg-color #f])
  (define gt-pict (apply vc-append 8 (map gt->pict g*)))
  (define the-radius -0.09)
  (define margin 18)
  (define the-blur-x 10)
  (if bg-color
    (cc-superimpose
      (blur
        (filled-rounded-rectangle (+ margin (pict-width gt-pict))
                                  (+ margin (pict-height gt-pict))
                                  the-radius
                                  #:draw-border? #false
                                  #:color bg-color)
        the-blur-x the-blur-x)
      gt-pict)
    gt-pict))

(define (get-pool-margins base)
  (define x-base (/ (+ 10 POOL-X-BASE) (pict-width base)))
  (define y-base (/ POOL-X-BASE (pict-height base) 2))
  (values x-base y-base))

(define (label-text str)
  (define b (blank 10 0))
  (hc-append b (text str TITLE-FONT 26) b))

(define (heading-text str [size 50])
  (text str TITLE-FONT size))

(define (pool-dimensions)
  (define w (- client-w (* 2 SLIDE-LEFT client-w)))
  (define h (- client-h (* 2 1/5 client-h)))
  (values w h))

(define (make-gtspace-bg [gt* '()] [gt-layout #f])
  (define-values [w h] (pool-dimensions))
  (cc-superimpose
    (cellophane (filled-rectangle (+ (* 2 margin) client-w) (+ margin h) #:color "DarkKhaki") 0.4)
    (add-gt-system* (filled-rounded-rectangle w h -1/5 #:color "AliceBlue") gt* gt-layout)))

(define (make-gtspace-slide [gt* '()] #:title [title #f] #:layout [gt-layout #f] #:disclaimer [extra-pict (blank)])
  (define top-margin -6)
  (define x-margin 40)
  (define arrow-size 12)
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
    (if title (blank) (heading-text "Typed/Untyped Languages"))
    #:go (coord 1/2 1/2)
    (tag-pict (make-gtspace-bg gt* gt-layout) POOL-TAG)
    #:go (coord 1/2 9/10 'cb)
    extra-pict
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
  ;; TODO magic ratios
  (ppict-do
    (make-gtspace-bg)
    #:go (coord 30/100 1/4)
    (maybe-highlight (make-H-box) (eq? highlight 'H))
    #:go (coord 65/100 2/4)
    (maybe-highlight (make-E-box) (eq? highlight 'E))
    #:go (coord 40/100 3/4)
    (maybe-highlight (make-1-box) (eq? highlight '1))))

(define (add-bottom-margin m p)
  (vc-append p (blank 0 m)))

(define (add-top-margin m p)
  (vc-append (blank 0 m) p))

(define (make-1-on-3 pre-base-pict pre-a pre-b pre-c)
  (define m 4)
  (define anchor (blank 11 0))
  (define base-pict (cb-superimpose anchor (add-top-margin m pre-base-pict)))
  (define a (add-bottom-margin m pre-a))
  (define b (add-bottom-margin m pre-b))
  (define c (add-bottom-margin m pre-c))
  (define boxes (vc-append 40 base-pict (hc-append 40 a b c)))
  (for/fold ((acc boxes))
            ((tgt (in-list (list a b c)))
             (?-find (in-list (list lb-find cb-find rb-find))))
    (pin-line acc anchor ?-find tgt ct-find)))

(define H-COLOR LIGHT-RED)
(define 1-COLOR BLUE)
(define E-COLOR GREEN)

(define (make-H-box)
  (make-embedding-box ->H H-COLOR))

(define (make-1-box)
  (make-embedding-box ->1 1-COLOR))

(define (make-E-box)
  (make-embedding-box ->E E-COLOR))

(define (make-TR-H-box)
  (make-embedding-box ->TR-H LIGHT-RED))

(define (make-TR-E-box)
  (make-embedding-box ->TR-E GREEN))

(define (make-TR-1-box)
  (make-embedding-box ->TR-1 BLUE))

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
  (define 1* (filter/embedding '1 gt*))
  (define E* (filter/embedding 'E gt*))
  (define HE-system* (filter/embedding '(H E) gt*))
  (define 1E-system* (filter/embedding '(E 1) gt*))
  (define p0 (make-base-embeddings-pict highlight))
  (define H-pos (find-tag p0 '->H))
  (define 1-pos (find-tag p0 '->1))
  (define E-pos (find-tag p0 '->E))
  (define margin 30)
  (parameterize ((current-font-size (- (current-font-size) 10)))
    (ppict-do
      p0
      #:go (at-find-pict H-pos lt-find 'rc #:abs-y 10 #:abs-x (- margin))
      (gt*->pict (sort H* < #:key (compose1 string-length gt-system-name)))
      #:go (at-find-pict E-pos rt-find 'lc #:abs-x margin #:abs-y 30)
      (gt*->pict E*)
      #:go (at-find-pict 1-pos lt-find 'rt #:abs-x (- margin) #:abs-y -15)
      (if (null? 1*)
        (blank)
        (let-values (((a* b*) (split/2 (cons reticulated (filter-not/name "Reticulated" 1*)))))
          (let ([b-pict (gt*->pict b*)]
                [a-pict (gt*->pict a*)])
            (if (null? a*) b-pict (if (null? b*) a-pict (ht-append 10 b-pict a-pict))))))
      #:set (let ((p ppict-do-state)
                  (HE-pict (gt*->pict HE-system*))
                  (1E-pict (gt*->pict 1E-system*)))
              (pin-line
                (pin-line
                  p
                  H-pos rc-find E-pos lt-find
                  #:y-adjust-label (- (/ (pict-height HE-pict) 2))
                  #:style (if (null? HE-system*) 'transparent 'short-dash)
                  #:label HE-pict)
                1-pos rc-find E-pos lb-find
                #:y-adjust-label (/ (pict-height 1E-pict) 2)
                #:style (if (null? 1E-system*) 'transparent 'short-dash)
                #:label 1E-pict)))))

(define (make-name-stack gt*)
  (make-stack #:v 10 #:bg (blank) (map gt-system-name gt*)))

(define (comment . stuff*)
  (blank 0 0))

(define (inferrule top bot)
  (vc-append 10
             top
             (hline (pict-width bot) 10)
             bot))

(define (hole-append . p*)
  (apply hc-append 10 p*))

(define make-hole
  (let* ([x @t{X}]
         [w (pict-width x)])
    (lambda ()
      (filled-rectangle w w #:color GREY))))

(define (big-monitor-icon)
  (big-pause-icon))

(define (small-monitor-icon)
  (small-pause-icon))

(define-values [small-pause-icon big-pause-icon]
  (let* ([pause-color "DarkOrange"] ;; Orange Gold
         [pause-icon (lambda (#:height h #:material m)
                       (record-icon #:color "DarkOrange" #:material m #:height h))])
    (values
      (lambda ()
        (make-icon pause-icon #:height 30))
      (lambda ()
        (make-icon pause-icon #:height 80)))))

(define (big-lock-icon)
  (make-icon lock-icon #:height 80))

(define (big-x-icon)
  (make-icon x-icon #:height 80))

(define (big-?-icon)
  (define (make-? #:height h #:material m)
    (text-icon "?" #:height h #:material m #:color "black"))
  (make-icon make-? #:height 80))

(define (little-x-icon)
  (make-icon x-icon #:height 30))

(define (big-check-icon)
  (make-icon check-icon #:height 80))

(define (small-check-icon)
  (make-icon check-icon #:height 30))

(define (big-bomb-icon)
  (make-icon bomb-icon #:height 60))

(define (small-bomb-icon)
  (make-icon bomb-icon #:height 40))

(define large-right-arrow
  (let ([right-arrow-icon2
          (lambda (#:height h #:material m)
            (right-arrow-icon #:color run-icon-color #:height h #:material m))])
    (lambda ()
      (make-icon right-arrow-icon2 #:height 80))))

(define (small-tau-icon)
  (make-icon tau-icon #:height 40))

(define (large-tau-icon)
  (make-icon tau-icon #:height 90))

(define tau-font
  (make-font #:smoothing 'unsmoothed #:family 'roman #:weight 'semibold))

(define (tau-icon #:color [c TAU-COLOR] #:height [h (default-icon-height)] #:material [m (default-icon-material)])
  (text-icon "τ" tau-font #:color c #:height h #:material m))

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
  (define bg-pict (or pre-bg-pict (filled-rectangle 240 100 #:color color)))
  (define blank-bg-pict (blank 0 (pict-height bg-pict)))
  (for/fold ([acc (blank)])
            ([txt (in-list txt*)])
    (vc-append v
               acc
               (if txt
                 (cc-superimpose
                   bg-pict
                   (t txt))
                 blank-bg-pict))))

(define (at-find-pict/below t #:abs-y [abs-y 6])
  (at-find-pict t cb-find 'ct #:abs-y abs-y))

(define (make-example-boundary-pict [a0 (blank)] [a1 (blank)] [a2 (blank)])
  (ppict-do
    (examples-append
      (make-base-example 'lbl-0)
      (make-inductive-example 'lbl-1)
      (make-coinductive-example 'lbl-2))
    #:go (at-find-pict/below 'lbl-0)
    a0
    #:go (at-find-pict/below 'lbl-1)
    a1
    #:go (at-find-pict/below 'lbl-2)
    a2))

(define (make-base-example lbl)
  (define l0 (hole-append @t{fib} (make-hole)))
  (define r0 @dyn-text{-1})
  (make-boundary-pict #:left l0 #:right r0 #:arrow (tag-pict @t{Nat} lbl)))

(define (make-inductive-example lbl)
  (define l1 (hole-append @t{norm} (make-hole)))
  (define r1 @dyn-text{⟨-1,-2⟩})
  (make-boundary-pict #:left l1 #:right r1 #:arrow (tag-pict (t/crunch "Nat × Nat") lbl)))

(define (make-coinductive-example lbl)
  (define l2 (hole-append @t{map} (make-hole) @t{y}))
  (define r2 @dyn-text{λ(x)-x})
  (make-boundary-pict #:left l2 #:right r2 #:arrow (tag-pict (t/crunch "Nat ⇒ Nat") lbl)))

(define (t/crunch str)
  (define t* (map t (string-split str)))
  (hc-append 2 (car t*) (vl-append 10 (blank) (clip-ascent (clip-descent (cadr t*)))) (caddr t*)))

(define (make-typed-racket-stack title)
  (make-labeled-stack title
                      '("expand" "typecheck" "enforce t" "optimize")
                      #:color LIGHT-RED))

(define (make-TR-stack)
  (make-typed-racket-stack "Typed Racket (TR-H)"))

(define (make-TR-H-stack)
  (make-typed-racket-stack "TR-H"))

(define (make-TR-E-stack)
  (make-labeled-stack "TR-E"
                      '("expand" "typecheck" "erase t")
                      #:color GREEN))

(define (make-TR-1-stack)
  (make-labeled-stack "TR-1"
                      '("expand" "typecheck" "enforce K(t)")
                      #:color BLUE))

(define (make-labeled-stack title txt* #:color c)
  ;; ignores label
  (make-stack txt* #:color c))

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

(define (make-overhead-plot-slide e*)
  (parameterize ([current-font-size 26])
    (pslide
      #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
      @heading-text{How does adding types affect performance?}
      #:go MAIN-CONTRIB-COORD
      (make-overhead-plot e*))))

(define (make-overhead-plot e* #:legend? [legend? #true])
  (define w 500)
  (define x-min 0)
  (define x-max (+ (/ pi 10) pi))
  (define pp
    (parameterize ((plot-x-ticks no-ticks)
                   (plot-y-ticks no-ticks)
                   (plot-font-size (current-font-size)))
      (plot-pict
        (for/list ((e (in-list e*)))
          (define c (symbol->color e))
          (function (make-embedding-function e x-min x-max)
                    #:width (* 15 (line-width))
                    #:alpha PLOT-FN-ALPHA
                    #:color c))
        #:y-label #f ;;"Overhead vs. Untyped"
        #:x-label #f ;;"Num. Type Ann."
        #:width 700
        #:height (* PLOT-RATIO w)
        #:x-min x-min
        #:x-max x-max
        #:y-min 0
        #:y-max (* 10 (+ 1 (order-of-magnitude x-max))))))
  (define pp+axis (add-overhead-axis-labels (tag-pict pp 'the-plot)))
  (if legend?
    (ppict-do
      (hc-append 30 (blank) pp+axis)
      #:go (at-find-pict 'the-plot lb-find 'rb #:abs-x -10)
      (make-overhead-legend '(H 1 E)))
    pp+axis))

(define (symbol->color e)
  (case e
    ((H)
     LIGHT-RED)
    ((E)
     GREEN)
    ((1)
     BLUE)
    (else
      (raise-argument-error 'symbol->color "(or/c 'H 'E '1)" e))))

(define (make-overhead-legend e*)
  (define w (* 22/100 client-w))
  (for/fold ([acc (blank w 50)])
            ([e (in-list e*)])
    (vl-append 20 acc (make-embedding-legend e))))

(define (add-overhead-axis-labels pp)
  (define margin 20)
  (define y-label
    (vr-append (t "Overhead vs.")
               (t "Untyped")))
  (define x-label (t "Num. Type Annotations"))
  (ht-append margin y-label (vr-append margin (frame-plot pp) x-label)))

(define (frame-plot p)
  (add-axis-arrow (add-axis-arrow p 'x) 'y))

(define (add-axis-arrow p xy)
  (define find-dest
    (case xy
      ((x)
       rb-find)
      ((y)
       lt-find)
      (else (raise-argument-error 'add-axis-arrow "(or/c 'x 'y)" 1 p xy))))
  (pin-arrow-line 20 p p lb-find p find-dest #:line-width 6))

(define (make-embedding-function e x-min x-max)
  (case e
    ((H)
     (define pi/4 (/ 3.14 4))
     (define 3pi/4 (* 3.5 pi/4))
     (lambda (n)
       (cond
         [(< n pi/4)
          (max 1 (+ 0.9 (sin n)))]
         [(< n 3pi/4)
          10]
         [else
          0.4])))
    ((E)
     (lambda (n) 1))
    ((1)
     (lambda (n) (add1 n)))
    (else
      (raise-argument-error 'make-embedding-line "embedding?" e))))

(define (make-embedding-legend e)
  (define-values [txt bx] (symbol->name+box e))
  (define txt-pict (t txt))
  (hc-append 10 (scale-for-legend bx) txt-pict))

(define (scale-for-legend p)
  (define h 20)
  (scale-to-fit (cellophane p PLOT-FN-ALPHA) h h))

(define (rectangle/2t width height
                      #:border-width [border-width 1]
                      #:border-color [border-color BLACK]
                      #:color-1 [color-1 WHITE]
                      #:color-2 [color-2 BLACK])
  (X-rectangle/2t 'draw-rectangle width height #:border-width border-width #:border-color border-color #:color-1 color-1 #:color-2 color-2))

(define (rounded-rectangle/2t width height
                              #:radius [radius -0.25]
                              #:border-width [border-width 1]
                              #:border-color [border-color BLACK]
                              #:color-1 [color-1 WHITE]
                              #:color-2 [color-2 BLACK])
  (X-rectangle/2t 'draw-rounded-rectangle width height #:border-width border-width #:border-color border-color #:color-1 color-1 #:color-2 color-2))

(define (X-rectangle/2t X-draw width height
                        #:radius [radius -0.25]
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
        (case X-draw
          ((draw-rectangle)
           (send dc draw-rectangle dx dy width height))
          ((draw-rounded-rectangle)
           (send dc draw-rounded-rectangle dx dy width height radius))
          (else
            (raise-argument-error 'X-rectangle "draw method" X-draw)))
        (send dc set-brush old-brush)
        (send dc set-pen old-pen))
      width height))

(define (rectangle/label width height
                         #:border-width [border-width 1]
                         #:border-color [border-color BLACK]
                         #:color-1 [color-1 WHITE]
                         #:color-2 [color-2 BLACK])
  (dc (λ (dc dx dy)
        (define old-brush
          (send dc get-brush))
        (define old-pen
          (send dc get-pen))
        ;(define gradient
        ;  (make-object
        ;   linear-gradient%
        ;   dx dy
        ;   dx (+ dy height)
        ;   `((0 ,(make-object color% color-1))
        ;     (1 ,(make-object color% color-2)))))
        ;(send dc set-brush
        ;  (new brush% [gradient gradient]))
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

(define make-folklore-slide
  (let ([q1 "Is type soundness all-or-nothing?"]
        [q1-h 2/10]
        [a1 "No! (in a mixed-typed language)"]
        [q2 "How does type soundness affect performance?"]
        [q2-h 5/10]
        [a2 "See graphs"])
    (lambda (#:q1? [q1? #true] #:q2? [q2? #true] #:answers? [answers? #false])
      (pslide
        #:go (coord SLIDE-LEFT q1-h 'lt)
        (if q1? (make-rumor-pict 'left q1) (blank))
        #:go (coord SLIDE-RIGHT 31/100 'rt)
        (if (and q1? answers?) (make-rumor-pict 'right a1) (blank))
        #:go (coord SLIDE-LEFT q2-h 'lt)
        (if q2? (make-rumor-pict 'left q2) (blank))
        #:go (coord SLIDE-RIGHT 61/100 'rt)
        (if (and q2? answers?) (make-rumor-pict 'right a2) (blank))))))

(define (string*->text str*)
  (if (string? str*)
    (t str*)
    (apply vl-append (map string*->text str*))))

(define (make-rumor-pict direction str*)
  (define str-pict (string*->text str*))
  (define str-w (pict-width str-pict))
  (define str-h (pict-height str-pict))
  (define balloon-w (+ str-w 70))
  (define balloon-h (+ str-h 60))
  (define balloon-body-color "white")
  (define balloon-line-color "black")
  (define balloon-line-width 8)
  (define balloon-tail-param 8)
  ;(define-values [spike +- c]
  ;  (case direction
  ;    [(left)
  ;     (values 'sw - q-color)]
  ;    [(right)
  ;     (values 'se + a-color)]
  ;    [else
  ;     (raise-argument-error 'make-rumor-pict "direction?" direction)]))
  ;(ppict-do
  ;  (balloon-pict (balloon balloon-w balloon-h balloon-tail-param spike (+- balloon-tail-param) balloon-tail-param c))
  ;  #:go (coord 1/2 1/2 'cc)
  ;  str-pict)
  (define balloon-pict
    (cc-superimpose
      (rounded-rectangle/2t balloon-w balloon-h
                            #:radius -0.2
                            #:color-1 "whitesmoke"
                            #:color-2 balloon-body-color
                            #:border-color balloon-line-color #:border-width balloon-line-width)
      str-pict))
  (define triangle-pict
    (let* ([triangle-width 30]
           [triangle-height 50]
           [draw-fun (lambda (dc dx dy)
                       (define old-brush (send dc get-brush))
                       (define old-pen (send dc get-pen))
                       (send dc set-brush (new brush% [style 'solid] [color balloon-body-color]))
                       (let ((path (new dc-path%)))
                         (send dc set-pen (new pen% [width balloon-line-width] [color balloon-body-color]))
                         (send path move-to 0 0)
                         (send path line-to triangle-width 0)
                         (send dc draw-path path dx dy))
                       (let ((path (new dc-path%)))
                         (send dc set-pen (new pen% [width balloon-line-width] [color balloon-line-color]))
                         (send path move-to 0 0)
                         (send path line-to (/ triangle-width 2) triangle-height)
                         (send path line-to triangle-width 0)
                         (send dc draw-path path dx dy))
                       (send dc set-brush old-brush)
                       (send dc set-pen old-pen))])
    (dc draw-fun triangle-width triangle-height)))
  (define tag-v (- (/ balloon-line-width 6)))
  (define tag-h 20)
  (case direction
    ((left)
     (vl-append tag-v balloon-pict (hc-append tag-h (blank) triangle-pict)))
    ((right)
     (vr-append tag-v balloon-pict (hc-append tag-h triangle-pict (blank))))
    (else
      (raise-argument-error 'make-rumor-pict "direction?" 1 str* direction))))

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

(define (split/2 x*)
  (define len/2 (quotient (length x*) 2))
  (let loop ((x* x*)
             (n len/2))
    (cond
      [(null? x*)
       (values x* '())]
      [(= n 0)
       (values '() x*)]
      [else
       (define-values [a* b*] (loop (cdr x*) (sub1 n)))
       (values (cons (car x*) a*) b*)])))

(define (url str)
  (hyperlinkize (tt str)))

(define (scale-for-bullet p)
  (define scale-factor 1.6)
  (scale p scale-factor))

(define (make-disclaimer-pict str)
  (text str (current-main-font) (- (current-font-size) 4)))

(define (author->pict name+img)
  (define name (car name+img))
  (define img (bitmap (cdr name+img)))
  (define margin 2)
  (hc-append 6
             (cc-superimpose (filled-rectangle (+ margin (pict-width img)) (+ margin (pict-height img)) #:color ECOOP-RED) img)
             (t name)))

(define (arrange-authors a->pict x* [x-sep 40] [y-sep 10] [flip? #false])
  (define-values [a* b*] (split/2 x*))
  (define col (if flip? hc-append vl-append))
  (define row (if flip? vl-append ht-append))
  (parameterize ([current-font-size 26])
    (row
      x-sep
      (apply col y-sep (map a->pict a*))
      (apply col y-sep (map a->pict b*)))))

(define (padded-bitmap pad)
  (define bg (blank pad pad))
  (lambda (p)
    (cc-superimpose bg (bitmap p))))

(define (stat-dyn/arrow)
  (add-stat-dyn-arrow (hc-append 70 (make-stat-file (large-tau-icon)) (make-dyn-file (large-lambda-icon)))))

(define (add-stat-dyn-arrow p)
  (for/fold ((acc p))
            ((xxx (in-list '((stat-file dyn-file)))))
    (pin-arrows-line
      #:line-width ARROW-LINE-WIDTH
      ARROW-HEAD-SIZE
      acc
      (find-tag acc (car xxx))
      rc-find
      (find-tag acc (cadr xxx))
      lc-find)))

(define (examples-append . p*)
  (apply vl-append 30 p*))

(define (symbol->name+box sym)
  (case sym
    ((H)
     (values "higher-order" (make-H-box)))
    ((1)
     (values "first-order" (make-1-box)))
    ((E)
     (values "erasure" (make-E-box)))
    (else
      (raise-argument-error 'symbol->name+box "(or/c 'H '1 'E)" sym))))

(define (make-example-detail-slide e-sym pict-1 [pict-2 #f] [pict-3 #f] #:arrow-label [arrow-label #false])
  (define name-coord (coord SLIDE-LEFT SLIDE-TOP 'lb))
  (define box-coord (coord SLIDE-LEFT SLIDE-TOP 'lt #:abs-y 6))
  (define examples-coord (coord 1/2 SLIDE-TOP 'ct #:abs-y 6))
  (define-values [e-name e-box] (symbol->name+box e-sym))
  (cond
    [(and pict-2 pict-3)
     (pslide
       #:go name-coord
       (t e-name)
       #:go box-coord
       e-box
       #:go examples-coord
       (tag-pict pict-1 'pict-1)
       #:next
       #:go (at-find-pict 'pict-1 lb-find 'lt #:abs-y 20)
       (hc-append 20 (arrow EVAL-ARROW-SIZE 0) (tag-pict pict-2 'pict-2))
       #:next
       #:go (at-find-pict 'pict-2 cb-find 'ct #:abs-y 15)
       (vr-append 15 (hc-append (arrow EVAL-ARROW-SIZE (* 3/2 pi)) (blank 55 0)) pict-3)
       #:go (if arrow-label (at-find-pict/below (car arrow-label)) (coord 0 0))
       (if arrow-label (cdr arrow-label) (blank)))]
    [pict-2
     (pslide
       #:go name-coord
       (t e-name)
       #:go box-coord
       e-box
       #:go examples-coord
       (tag-pict pict-1 'pict-1)
       #:next
       #:go (at-find-pict 'pict-1 lb-find 'lt #:abs-y 20)
       pict-2)]
    [else
      (raise-argument-error 'make-example-detail-slide "pict?" 2 e-sym pict-1 pict-2 pict-3)]))

(define (make-sig-pict str)
  (define p (vl-append 8 (t str) (blank)))
  (cc-superimpose
    (rectangle (+ 15 (pict-width p)) (pict-height p))
    p))

(define (make-kafka-slide)
  (define x-base 15/100)
  (define ecoop-pict (string->title "ECOOP 2018" #:size 30 #:color WHITE))
  (define title-pict (string->title "KafKa: Gradual Typing for Objects" #:size 36))
  (define authors-pict (arrange-authors author->pict kafka-author*))
  (define box-w (exact-ceiling (+ 60 (max (pict-width title-pict) (pict-width authors-pict)))))
  (define box-h (exact-ceiling (+ 60 (pict-height title-pict) (pict-height authors-pict))))
  (define bw 2)
  (define the-box (filled-rectangle box-w box-h #:color BOX-COLOR #:border-width bw))
  (define lbl-h (exact-ceiling (* 3 (pict-height ecoop-pict))))
  (define the-label (filled-rounded-rectangle box-w lbl-h #:color ECOOP-RED #:border-width bw))
  (pslide
    #:go (coord 1/2 1/2 'cc)
    (tag-pict the-box 'the-box)
    #:go (at-find-pict 'the-box ct-find 'cc)
    (tag-pict the-label 'lbl-pict)
    #:go (at-find-pict 'lbl-pict rc-find 'rc #:abs-x -40 #:abs-y -20)
    ecoop-pict
    #:go (coord 1/2 1/2 'cc)
    the-box
    #:go (at-find-pict 'the-box lt-find 'lt #:abs-x 20 #:abs-y 20)
    (tag-pict title-pict 'title-pict)
    #:go (at-find-pict 'title-pict lb-find 'lt #:abs-x 6 #:abs-y 20)
    authors-pict)
  (void))

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit) )
