#lang at-exp slideshow

;; Slides for ICFP 2018

;; TODO
;; - be clearer about contribution, we did the semantics
;; - add micro/macro dyn/not knobs for ICFP

(require
  gf-icfp-2018/talk/src/gt-system gf-icfp-2018/talk/src/constant
  pict pict/convert pict/balloon
  ppict/2
  scribble-abbrevs/pict
  slideshow/code
  plot/no-gui plot/utils
  racket/draw
  racket/list
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in scribble/base url))

;; =============================================================================

(define (do-show)
  (set-page-numbers-visible! #false)
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size 32]
                 [current-titlet string->title])
    (void)
    (sec:title)
    (sec:folklore-I)
    (sec:migratory-typing)
    (sec:gt-landscape)
    (sec:kafka)
    (sec:main-result)
    (sec:embeddings)
    (sec:soundness)
    (sec:implementation)
    (sec:experiment)
    (sec:graph)
    (sec:conclusion)
    (pslide)
    (sec:extra)
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

(define (sec:migratory-typing)
  (define lambda-pict (large-lambda-icon))
  (define tau (large-tau-icon))
  (define dyn-file (make-dyn-file lambda-pict))
  (pslide
    (make-section-header "Migratory Typing"))
  (pslide
    #:go (coord SLIDE-LEFT 1/4 'lt)
    @t{Step 0: un(i)typed language}
    #:go (coord 1/2 1/2)
    dyn-file)
  (pslide
    #:go (coord SLIDE-LEFT 1/4 'lt)
    @t{Step 1: idiomatic type system}
    #:go (coord 1/2 1/2)
    dyn-file
    #:go (at-find-pict 'dyn-file lc-find 'rc #:abs-x -10)
    tau)
  (pslide
    #:go (coord SLIDE-LEFT 1/4 'lt)
    @t{Step 2: mixed-typed language}
    #:go (coord 1/2 1/2)
    (add-stat-dyn-arrow (hc-append 140 (make-stat-file tau) dyn-file)))
  (void))

(define (sec:gt-landscape)
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
    #:title '("by Claim" "Sound?" "Unsound")
    #:layout theory-gt-layout)
  (make-gtspace-slide
    all-system*
    #:title '("by Performance" "Alive?" "Dead")
    #:layout performance-gt-layout
    #:disclaimer (make-disclaimer-pict "(the word 'dead' is used here in a technical sense)"))
  (pslide
    @titlet{Chaos!})
  (void))

(define (sec:kafka)
  (define x-base 15/100)
  (define ecoop-pict (string->title "ECOOP 2018" #:size 30 #:color WHITE))
  (define title-pict (string->title "KafKa: Gradual Typing for Objects" #:size 36))
  (define authors-pict
    (arrange-authors author->pict kafka-author*))
  (define box-w (+ 60 (max (pict-width title-pict) (pict-width authors-pict))))
  (define box-h (+ 60 (pict-height title-pict) (pict-height authors-pict)))
  (define bw 2)
  (define the-box (filled-rectangle box-w box-h #:color BOX-COLOR #:border-width bw))
  (define lbl-h (* 3 (pict-height ecoop-pict)))
  (pslide
    #:go (coord 1/2 1/2 'cc)
    (tag-pict the-box 'the-box)
    #:go (at-find-pict 'the-box ct-find 'cc)
    (tag-pict (filled-rounded-rectangle box-w lbl-h #:color ECOOP-RED #:border-width bw) 'lbl-pict)
    #:go (at-find-pict 'lbl-pict rc-find 'rc #:abs-x -40 #:abs-y -20)
    ecoop-pict
    #:go (coord 1/2 1/2 'cc)
    the-box
    #:go (at-find-pict 'the-box lt-find 'lt #:abs-x 20 #:abs-y 20)
    (tag-pict title-pict 'title-pict)
    #:go (at-find-pict 'title-pict lb-find 'lt #:abs-x 6 #:abs-y 20)
    authors-pict)
  (void))

(define (sec:main-result)
  (pslide
    #:go (coord 1/5 25/100 'lt)
    (let ([box+text (lambda (b t) (hc-append 20 b t))])
      (vl-append
        20
        (box+text (make-H-box) @t{higher-order semantics})
        (box+text (make-1-box) @t{first-order semantics})
        (box+text (make-E-box) @t{erasure semantics}))))
  (main-results-slide)
  (void))

(define (sec:embeddings)
  (pslide
    (make-section-header "Model"))
  (embedding:warmup)
  (embedding:H)
  (embedding:1)
  (embedding:E)
  (embedding:end)
  (void))

(define (embedding:warmup)
  (define x-offset 1/20)
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    ;;@t{Types}
    (vl-append 10
               @t{τ = Nat | Int | τ × τ | τ → τ}
               @t{Nat <: Int})
    #:next
    #:go (coord SLIDE-LEFT 25/100 'lt)
    ;;@t{Values}
    (vl-append 10
               @t{v = n | i | ⟨v,v⟩ | λ(x)e | λ(x:τ)e}
               @t{n ⊂ i})
    #:next
    #:go (coord SLIDE-LEFT 40/100 'lt)
    @t{e = .... | dyn τ e | stat τ e}
    #:next
    ;;@hb-append[40 (make-sig-pict @t{⊢ e : τ}) (make-sig-pict @t{⊢ e})]
    #:go (coord 55/100 50/100 'ct)
    @hb-append[
      100
      @inferrule[@t{⊢ e}
                 @t{⊢ dyn τ e : τ}]
      @inferrule[@t{⊢ e : τ}
                 @t{⊢ stat τ e}]])
  (define (v-append . x*)
    (apply vl-append 10 x*))
  (define types-pict
    (vl-append 10
      @t{fib : Nat → Nat}
      @t{norm : Nat × Nat → Nat}
      @t{map : (Nat → Nat) → Nat × Nat → Nat × Nat}))
  (pslide
    #:go (coord 1/2 SLIDE-TOP 'ct)
    (vc-append
      100
      (hc-append 10
        @t{Γ =}
        (text "{" (current-main-font) (+ 40 (current-font-size))) ;}
        types-pict)
      (vl-append 25
        @t{Γ ⊢ fib (dyn Nat -1) : Nat}
        @t{Γ ⊢ norm (dyn Nat × Nat ⟨-1,-2⟩) : Nat}
        @t{Γ ⊢ map (dyn (Nat → Nat) (λ(x)e)) y : Nat × Nat})))
  (pslide
    (make-example-boundary-pict))
  (void))

(define (embedding:H)
  (pslide
    #:alt [(make-embeddings-pict)]
    (make-embeddings-pict #:highlight 'H))
  (make-H-example-slide)
  (void))

(define (embedding:1)
  (pslide
    #:alt ((make-embeddings-pict))
    #:alt ((make-embeddings-pict H-system*))
    (make-embeddings-pict H-system* #:highlight '1))
  (make-1-example-slide)
  (void))

(define (embedding:E)
  (pslide
    #:alt [(make-embeddings-pict H-system*)]
    #:alt [(make-embeddings-pict H-system* reticulated)]
    #:alt [(make-embeddings-pict H-system* 1-system*)]
    (make-embeddings-pict H-system* 1-system* #:highlight 'E))
  (make-E-example-slide)
  (void))

(define (embedding:end)
  (pslide
    #:alt [(make-embeddings-pict H-system* 1-system* E-system*)]
    (make-embeddings-pict all-system*))
  (void))

(define (sec:soundness)
  (define-values [model-pict impl-pict] (make-model/impl-pict))
  (define type-pict*
    (for/list ((p (in-list (list ⊢H ⊢1 ⊢E)))
               (str (in-list '("τ" #f "K(τ)"))))
      (hc-append 0 (scale-for-bullet p) (blank 2 0) (t "e") (if str (t (string-append ":" str)) (blank)))))
  (define model-pict+
    (ppict-do
      model-pict
      #:set (for/fold ((acc ppict-do-state))
                      ((tag (in-list '(->H ->1 ->E)))
                       (type-pict (in-list type-pict*)))
              (ppict-do
                acc
                #:go (at-find-pict tag cb-find 'ct #:abs-y 40)
                type-pict))))
  (define x-base MAIN-CONTRIB-X)
  (define y-base MAIN-CONTRIB-Y)
  (define my-blank (blank (pict-width impl-pict) 0))
  (make-folklore-slide #:q2? #false)
  (pslide
    #:go (coord x-base 1/2 'lc)
    #:alt [(main-contrib-append model-pict (contrib*->pict '("Same type soundness?")))]
    #:alt [(main-contrib-append model-pict (contrib*->pict '("Same type soundness?" "No!")))]
    (main-contrib-append model-pict+
                         (contrib*->pict
                           (add-between
                             (for/list ((type-pict (in-list type-pict*))
                                        (a (in-list (list ->H ->1 ->E))))
                               (hc-append (t "- ") type-pict (t " sound for ") (scale-for-bullet a)))
                             (blank)))))
  (void))

(define (sec:implementation)
  (define-values [model-pict impl-pict] (make-model/impl-pict))
  (define x-base MAIN-CONTRIB-X)
  (define y-base MAIN-CONTRIB-Y)
  (pslide
    (make-section-header "Implementation"))
  (pslide
    #:go (coord x-base 1/2 'lc)
    (main-contrib-append model-pict impl-pict))
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

(define (sec:experiment)
  (pslide
    (make-section-header "Experiment"))
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
  (void))

(define (sec:graph)
  (pslide
    (make-section-header "Results"))
  (make-overhead-plot-slide '())
  (make-overhead-plot-slide '(H 1 E))
  (pslide
    (make-scatterplots-pict))
  ;; TODO table of lo-hi performance, to better support prescriptions at the end
  ;(make-folklore-slide #:q1? #false)
  ;(make-overhead-plot-slide '(H 1 E))
  (void))

(define (make-scatterplots-pict)
  (scale-to-fit (bitmap cache-scatterplots.png) client-w client-h))

(define (sec:conclusion)
  (define-values [box-pict sup-pict]
    (let* ([sup-pict (text "⊃" (current-main-font) 40)]
           [b (blank (pict-width sup-pict) 0)])
      (values
        (hc-append 10 (make-H-box) b (make-1-box) b (make-E-box))
        (hc-append 10 (make-H-box) sup-pict (make-1-box) sup-pict (make-E-box)))))
  (define y-sep 30)
  (define soundness-pict
    (tag-pict
      (apply vl-append y-sep
        (for/list ((arr (in-list (list ->H ->1 ->E)))
                   (what (in-list (list "types" #f "type constructors"))))
          (ht-append (scale-for-bullet arr)
                     (if what
                       (vl-append 10
                                  (t " progress + preserves")
                                  (t (string-append " " what)))
                       (t " progress")))))

      'bullets))
  (define perf-pict
    (tag-pict
      (apply vl-append y-sep
        (for/list ((arr (in-list (list ->H ->1 ->E)))
                   (where (in-list (list "to 'packages'" "anywhere" "sparingly"))))
          (hc-append (scale-for-bullet arr)
                     (t (format " add types ~a" where)))))
      'perf))
  (pslide
    (make-section-header "Implications"))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @titlet{Theory Implications}
    #:go (coord SLIDE-LEFT 1/4 'lt)
    (main-contrib-append sup-pict soundness-pict)
    #:next
    #:go (at-find-pict 'bullets lb-find 'lt #:abs-y y-sep)
    (vl-append y-sep
               (hc-append (t "- ") (scale-for-bullet ->H) (t " refines ") (scale-for-bullet ->1))
               (hc-append (t "- ") (scale-for-bullet ->1) (t " refines ") (scale-for-bullet ->E))))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @titlet{Performance Implications}
    #:go (coord SLIDE-LEFT 1/4 'lt)
    (main-contrib-append
      perf-pict
      (let ((w (pict-width box-pict)))
        (scale-to-fit (make-overhead-plot '(H 1 E) #:legend? #false) w w))))
  (void))

(define (sec:folklore-II)
  (make-folklore-slide #:answers? #true)
  (void))

(define (sec:extra)
  (make-acks-slide)
  (make-H-example-slide)
  (make-1-example-slide)
  (make-E-example-slide)
  (pslide
    (make-embeddings-pict all-system*))
  (pslide
    (make-scatterplots-pict))
  (void))

;; -----------------------------------------------------------------------------

(define (make-H-example-slide)
  (make-?-example-slide "higher-order" (make-H-box) (big-x-icon) (big-x-icon) (big-lock-icon)))

(define (make-E-example-slide)
  (make-?-example-slide "erasure" (make-E-box) (big-check-icon) (big-check-icon) (big-check-icon)))

(define (make-1-example-slide)
  (make-?-example-slide "first-order" (make-1-box) (big-x-icon) (big-check-icon) (big-check-icon)))

(define (make-?-example-slide name lbl r0 r1 r2)
  (pslide
    (make-example-boundary-pict r0 r1 r2)
    #:go (coord SLIDE-TOP SLIDE-LEFT 'lt)
    (t name)
    (blank 0 10)
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
  (define tu-pict (add-stat-dyn-arrow (hc-append 70 (make-stat-file (large-tau-icon)) (make-dyn-file (large-lambda-icon)))))
  (define (smaller p) (scale-to-fit p (- w 80) (- h 80)))
  (define m (smaller (make-1-on-3 tu-pict (make-H-box) (make-1-box) (make-E-box))))
  (define i
    (let* ((h (pict-height tu-pict))
           (rkt-pict (scale-to-fit (bitmap racket-logo.png) h h)))
      (smaller (make-1-on-3 rkt-pict (make-TR-H-box) (make-TR-1-box) (make-TR-E-box)))))
  (values m i))

(define (contrib*->pict str*)
  (define-values [w h] (two-column-dims))
  (for/fold ((p (blank)))
            ((str (in-list str*))
             (i (in-naturals)))
    (vl-append 10 p (if (pict? str) str (t str)))))

(define (main-contrib-append a b #:x-shift [x 0])
  (ht-append (+ x 10) a b))

(define (main-results-slide)
  (define-values [model-pict0 impl-pict0] (make-model/impl-pict))
  (define x-base MAIN-CONTRIB-X)
  (define fig-coord (coord x-base 1/4 'lt))
  (define contrib-0-pict
    (contrib*->pict
      '("Model:"
        "- one mixed-typed language"
        "- one surface type system"
        "- three semantics")))
  (define contrib-1-pict
    (contrib*->pict
      '("Implementation:"
        "- Racket syntax/types"
        "- three compilers"
        "- the first controlled"
        "  performance experiment")))
  (define model-pict
    (cc-superimpose
      (blank (pict-width contrib-1-pict) 0)
      (scale-for-column model-pict0)))
  (define impl-pict (scale-for-column impl-pict0))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @titlet{Contributions (1/2)}
    #:go fig-coord
    (main-contrib-append
      model-pict
      contrib-0-pict))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @titlet{Contributions (2/2)}
    #:go fig-coord
    #:alt [(main-contrib-append model-pict (blank (pict-width impl-pict) 0))
           #:go (coord 1/2 1/2 'cb)
           (large-right-arrow)]
    #:alt [(main-contrib-append model-pict impl-pict)
           #:go (coord 1/2 1/2 'cb)
           (large-right-arrow)]
    (main-contrib-append
      contrib-1-pict
      impl-pict))
  (pslide
    #:go (coord 1/2 1/2)
    @t{First apples-to-apples soundness and performance comparisons"})
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
  (define sf (make-stat-file left-pict))
  (define df (make-dyn-file right-pict))
  (ppict-do
    (blank (/ client-w 2) (pict-height sf))
    #:go (coord x-offset 1/2)
    sf
    #:go (coord (- 1 x-offset) 1/2)
    df
    #:set (let ((p ppict-do-state))
            (if arrow-pict
              (pin-arrow-line 10 p
                              (find-tag p 'dyn-file) lc-find
                              (find-tag p 'stat-file) rc-find
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
  (cc-superimpose
    (filled-rectangle w h #:color bg-color)
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

(define (gt*->pict g* #:bg-color [bg-color #f])
  (define gt-pict (apply vc-append 8 (map gt->pict g*)))
  (define margin 8)
  (if bg-color
    (cc-superimpose
      (filled-rounded-rectangle (+ margin (pict-width gt-pict))
                                (+ margin (pict-height gt-pict))
                                -0.05
                                #:draw-border? #false
                                #:color bg-color)
      gt-pict)
    gt-pict))

(define (creator-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-source gt-system-source<)))

(define (theory-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-embedding%E (lambda (x y) (eq? y 'E)))))

(define (performance-gt-layout base gt*)
  (histogram-gt-layout base (group-gt-systems-by gt* gt-system-name%TR (lambda (x y) (string=? y "Typed Racket")))))

(define (get-pool-margins base)
  (define x-base (/ (+ 10 POOL-X-BASE) (pict-width base)))
  (define y-base (/ POOL-X-BASE (pict-height base) 2))
  (values x-base y-base))

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
  (define ISLAND-COLOR "LightSteelBlue")
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
                (if (< (length g*) max-in-column)
                  (gt*->pict g* #:bg-color ISLAND-COLOR)
                  (let-values ([(a* b*) (split-at g* max-in-column)])
                    (h?-append x-sep (gt*->pict a* #:bg-color ISLAND-COLOR) (loop b*)))))))))

(define (label-text str)
  (define b (blank 10 0))
  (hc-append b (text str TITLE-FONT 26) b))

(define (make-gtspace-bg [gt* '()] [gt-layout #f])
  (define h (- client-h (* 2 1/5 client-h)))
  (define w (- client-w (* 2 SLIDE-LEFT client-w)))
  (cc-superimpose
    (cellophane (filled-rectangle (+ (* 2 margin) client-w) (+ margin h) #:color "DarkKhaki") 0.4)
    (add-gt-system* (filled-rounded-rectangle w h -1/5 #:color "AliceBlue") gt* gt-layout)))

(define (heading-text str)
  (text str TITLE-FONT 50))

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

(define (make-H-box)
  (make-embedding-box ->H LIGHT-RED))

(define (make-E-box)
  (make-embedding-box ->E GREEN))

(define (make-1-box)
  (make-embedding-box ->1 BLUE))

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

(define (transient-dyn-slide)
  (pslide
    #:go (coord 1/15 1/5 'lt)
    (make-sig-pict (make-step @t{dyn t v} ->1 @t{v}))
    #:go (coord 2/15 3/10 'lt)
    (make-embedding-table
      (list
        @t{dyn Nat n} ->1 @t{n}
        @t{dyn Int i} ->1 @t{i}
        @t{dyn (t0 × t1) ⟨v0, v1⟩} ->1 @t{⟨v0, v1⟩}
        @t{dyn (td → tc) λ(x)e} ->1 @t{λ(x)e}
        @t{dyn t v} ->1 (little-x-icon)))))

(define (comment . stuff*)
  (blank 0 0))

(define (inferrule top bot)
  (vc-append 10
             top
             (hline (pict-width bot) 10)
             bot))

(define (hole-append . p*)
  (apply hc-append 20 p*))

(define make-hole
  (let* ([x @t{X}]
         [w (pict-width x)])
    (lambda ()
      (filled-rectangle w w #:color GREY))))

(define (big-lock-icon)
  (make-icon lock-icon #:height 80))

(define (big-x-icon)
  (make-icon x-icon #:height 80))

(define (little-x-icon)
  (make-icon x-icon #:height 30))

(define (big-check-icon)
  (make-icon check-icon #:height 80))

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

(define make-example-boundary-pict
  (lambda ([a0 (blank)] [a1 (blank)] [a2 (blank)])
    (let ([l0 (hole-append @t{fib} (make-hole))]
          [r0 @dyn-text{-1}]
          [l1 (hole-append @t{norm} (make-hole))]
          [r1 @dyn-text{⟨-1,-2⟩}]
          [l2 (hole-append @t{map} (make-hole) @t{y})]
          [r2 @dyn-text{λ(x)e}]
          [afp (lambda (t) (at-find-pict t cb-find 'ct #:abs-y 6))])
      (ppict-do
        (vc-append
          30
          (make-boundary-pict #:left l0 #:right r0 #:arrow (tag-pict @t{Nat} 'lbl-0))
          (make-boundary-pict #:left l1 #:right r1 #:arrow (tag-pict @t{Nat × Nat} 'lbl-1))
          (make-boundary-pict #:left l2 #:right r2 #:arrow (tag-pict @t{Nat → Nat} 'lbl-2)))
        #:go (afp 'lbl-0)
        a0
        #:go (afp 'lbl-1)
        a1
        #:go (afp 'lbl-2)
        a2))))

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
      #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
      @titlet{Typical program}
      #:go (coord (- SLIDE-LEFT 1/40) 1/5 'lt)
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
  (define pp+axis (add-overhead-axis-labels pp))
  (if legend?
    (ht-append 20 (make-overhead-legend e*) pp+axis)
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
  (define y-label (t "Overhead vs. Untyped"))
  (define x-label (t "Num. Type Annotations"))
  (vl-append margin y-label (vr-append margin (frame pp) x-label)))

(define (make-embedding-function e x-min x-max)
  (case e
    ((H)
     (define pi/4 (/ 3.14 4))
     (define 3pi/4 (* 3.5 pi/4))
     (lambda (n)
       (cond
         [(< n pi/4)
          (max 1 (+ 0.5 (sin n)))]
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
  (define-values [bx txt]
    (case e
      ((H)
       (values (make-H-box) "higher-order"))
      ((E)
       (values (make-E-box) "erasure"))
      ((1)
       (values (make-1-box) "first-order"))
      (else
        (raise-argument-error 'make-embedding-legend "embedding?" e))))
  (define txt-pict (t txt))
  (define h 20)
  (hc-append 10 (scale-to-fit (cellophane bx PLOT-FN-ALPHA) h h) txt-pict))

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
        [a1 '("What invariants should the" "language guarantee?")]
        ;;
        [q2 "How does type soundness affect performance?"]
        [q2-h 5/10]
        [a2 '("Yes, through interaction with" "untyped code (or data)")])
    (lambda (#:q1? [q1? #true] #:q2? [q2? #true] #:answers? [answers? #false])
      (if answers?
        (raise-user-error 'make-folklore-slide "#:answers? not implemented")
        #;(pslide
          #:go (coord SLIDE-LEFT q1-h 'lt)
          (make-rumor-pict 'left q1)
          #:go (coord SLIDE-LEFT q2-h 'lt)
          (make-rumor-pict 'left q2)
          #:go (coord SLIDE-RIGHT 31/100 'rt)
          (make-rumor-pict 'right a1)
          #:go (coord SLIDE-RIGHT 61/100 'rt)
          (make-rumor-pict 'right a2))
        (pslide
          #:go (coord SLIDE-LEFT q1-h 'lt)
          (if q1? (make-rumor-pict 'left q1) (blank))
          #:go (coord SLIDE-LEFT q2-h 'lt)
          (if q2? (make-rumor-pict 'left q2) (blank)))))))

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

(define (make-acks-slide)
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lb)
    (heading-text "Special Thanks")
    #:go (coord 1/2 1/4 'ct)
    (arrange-authors (padded-bitmap 140) ack* 100 20 #true)))

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

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit) )
