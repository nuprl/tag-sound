#lang at-exp slideshow

;; Slides for GRACE 2018
;;
;; Date: 2018-11-04 (sunday)
;; Time: 14:00 -- 14:20
;; Topic: ICFP + DLS talks ... mostly ICFP, switch to DLS
;; Abstract:
;;   The literature on gradual typing is filled with unscientific claims about
;;   different systems; in particular, about the guarantees of their types, their
;;   relative performance, and the degree to which they accommodate the needs of
;;   developers. This work attempts a scientific comparison on all three counts:
;;   soundness, performance, and developers’ preference.
;;
;;   The soundness and performance comparison is joint work with Matthias Felleisen.
;;   The preference comparison is joint work with Preston Tunnell Wilson, Justin
;;   Pombrio, and Shriram Krishnamurthi.
;;
;; Outline ... mostly performance? Boundaries, then performance. Maybe fish?

; TODO tim jones counterexamples to GG 
; (require/typed (id (-> Any String)))
; (define (f (x : Any))
;   ;; assuming type system doesn't reflect type of id, removing/changing types affects semantics
;   (with-handlers ((exn:fail:contract? (lambda (ex) .... something with input)))
;     (id x)))

; "grace.ss":
;   making #<path:/Users/ben/code/racket/gtp/shallow/gf-icfp-2018/talk/grace.ss>
;  [output to "compiled/grace_ss.zo"]
; result arity mismatch;
;  expected number of values not received
;   expected: 2
;   received: 1
;   in: local-binding form
;   values...:
;    24/25
;   context...:
;    /Users/ben/code/racket/fork/extra-pkgs/slideshow/slideshow-lib/slideshow/viewer.rkt:263:10: display-changed method in auto-resize-frame%
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:428:6
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:479:32
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:627:3
;    "/Users/ben/code/racket/fork/racket/collects/raco/raco.rkt": [running body]
;    temp37_0
;    for-loop
;    run-module-instance!125
;    "/Users/ben/code/racket/fork/racket/collects/raco/main.rkt": [running body]
;    temp37_0
;    for-loop
;    run-module-instance!125
;    perform-require!78
; result arity mismatch;
;  expected number of values not received
;   expected: 2
;   received: 1
;   in: local-binding form
;   values...:
;    24/25
;   context...:
;    /Users/ben/code/racket/fork/extra-pkgs/slideshow/slideshow-lib/slideshow/viewer.rkt:263:10: display-changed method in auto-resize-frame%
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:428:6
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:479:32
;    /Users/ben/code/racket/fork/extra-pkgs/gui/gui-lib/mred/private/wx/common/queue.rkt:627:3
;    "/Users/ben/code/racket/fork/racket/collects/raco/raco.rkt": [running body]
;    temp37_0
;    for-loop
;    run-module-instance!125
;    "/Users/ben/code/racket/fork/racket/collects/raco/main.rkt": [running body]
;    temp37_0
;    for-loop
;    run-module-instance!125
;    perform-require!78

(require
  (only-in gtp-util natural->bitstring)
  gf-icfp-2018/talk/src/gt-system
  gf-icfp-2018/talk/src/grace-util
  pict pict/convert pict/balloon pict/shadow
  pict-abbrevs
  ppict/2
  scribble-abbrevs/pict
  plot/no-gui
  racket/draw
  racket/list
  gtp-plot/configuration-info
  gtp-plot/performance-info
  gtp-plot/plot
  gtp-plot/typed-racket-info
  (only-in racket/string string-split)
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style)

(module+ test (require rackunit))

;; -----------------------------------------------------------------------------

(define FSM-DATA (make-typed-racket-info "./src/fsm-6.4.rktd"))

(define ((add-bg-assembler default-assembler #:color color) s v-sep c)
  (define fg (default-assembler s v-sep c))
  (define bg
    (inset (filled-rectangle
             (+ (* 2 margin) client-w)
             (+ (* 2 margin) client-h)
             #:color color
             #:draw-border? #false) (- margin)))
  (cc-superimpose bg fg))

(module+ main
  (set-page-numbers-visible! #true)
  (set-spotlight-style! #:size 40 #:color (color%-update-alpha HIGHLIGHT-COLOR 0.6))
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size NORMAL-FONT-SIZE]
                 [current-slide-assembler (add-bg-assembler (current-slide-assembler)
                                                            #:color (color%-update-alpha (string->color% "Moccasin") 0.4))]
                 [current-titlet string->title])
    (void)
    (sec:title)
    (sec:background)
    (sec:three)
    ;(sec:boundary)
    (sec:soundness) ;; ends with bubble, folklore
    (sec:implementation)
    (sec:lattice)
    (sec:performance)
    (sec:people)
    (void)))

;; -----------------------------------------------------------------------------

(define (sec:title)
  (pslide
    #:go (coord SLIDE-LEFT 35/100 'lt)
    (parameterize ((current-main-font (list* 'bold 'italic TITLE-FONT))
                   (current-font-size TITLE-FONT-SIZE))
      @t{Three Approaches to Gradual Typing})
    #:go (coord SLIDE-RIGHT SLIDE-BOTTOM 'rb)
    (parameterize ((current-main-font ALL-CAPS-FONT)
                   (current-font-size SMALL-FONT-SIZE))
      @para{@bt{Ben Greenman},
            Justin Pombrio,
            Matthias Felleisen,
            Preston Tunnell Wilson,
            Shriram Krishnamurthi, and many others})
    #;#;#:go (coord 1/2 SLIDE-BOTTOM 'cc)
    #;(apply hb-append 40 all-logo*)
    )
  (void))

(define (sec:background)
  (parameterize ((current-para-width (w%->pixels 55/100)))
    (let ((dyn-desc
            (lines-append
              @subsubtitle-text{Dynamic Typing}
              @para{@bt{value}-level abstractions, enforced at run-time}))
          (sta-desc
            (lines-append
              @subsubtitle-text{Static Typing}
              @para{@bt{type}-level abstractions, checked before run-time}))
          (mixed-desc
            (lines-append
              @subsubtitle-text{Gradual Typing}
              @para{mix of static & dynamic typing ... somehow}))
          (h-width 4)
          (h-color HIGHLIGHT-COLOR))
    (pslide
     #:go CENTER-COORD
         (make-2table
         (list
           (list dyn-desc
                 (make-program-pict/dyn))
           (list sta-desc
                 (make-program-pict/sta))
           (list mixed-desc
                 (make-program-pict/mixed #:show-boundary? #true))))
     #:next
     #:alt [
     #:go (at-leftline dyn-desc)
     (make-leftline dyn-desc h-width #:color h-color) ]
     #:alt [
     #:go (at-leftline sta-desc)
     (make-leftline sta-desc h-width #:color h-color) ]
     #:go (at-leftline mixed-desc)
     (make-leftline mixed-desc h-width #:color h-color))))
  (pslide
    #:go HEADING-COORD
    (subsubtitle-text "Gradual Typing is growing ...")
    #:go (coord 1/10 20/100 'lt)
    (vl-append (h%->pixels 1/15)
               @para{Over 80 publications}
               @para{Over 20 implementations})
    #:next
    #:go (coord 1/2 1/2 'ct)
    (parameterize ((current-para-width (w%->pixels 60/100)))
      (alert-frame @para[#:align 'center]{But NO common definition of gradual typing --- due to@bt{different} goals and priorities}))
    #:next
    #:go (coord 1/2 SLIDE-BOTTOM 'cc)
    @para[#:align 'center]{Little acknowledgment (or analysis!) of the differences})
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "One kind of gradual typing:")
   #:go (coord 1/10 SLIDE-TOP 'lt)
   (hc-append (subtitle-text "Migratory Typing") @t{ (SNAPL'17)})
   #:go (coord 1/5 25/100 'lt)
   (parameterize ((current-para-width (w%->pixels 55/100)))
     (make-2table
       #:row-sep (h%->pixels 1/15)
       #:col-sep 10
       #:row-align lt-superimpose
       (list
         (list @t{1.} @para{Begin with an existing, dynamically-typed language})
         (list @t{2.} @para{Design an idiomatic type system})
         (list @t{3.} @para{Allow interaction between the two languages})))))
  (void))

(define (sec:three)
  (define-values [deep-system-pict shallow-system-pict erasure-system-pict] (make-DSE-system-pict*))
  (define-values [d-pict s-pict e-pict] (apply values (make-DSE-halo-pict*)))
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "a few Migratory Typing systems")
   #:go (coord SLIDE-LEFT 1/5 'lt)
   #:alt [(make-2table
     #:row-align lt-superimpose
            (list
              (list (pict->blank d-pict) deep-system-pict)
              (list (pict->blank s-pict) shallow-system-pict)
              (list (pict->blank e-pict) erasure-system-pict)))]
   (make-2table
     #:row-align lt-superimpose
     (list
       (list d-pict deep-system-pict)
       (list s-pict shallow-system-pict)
       (list e-pict erasure-system-pict))))
  (pslide
   #:go HEADING-COORD
   (subsubtitle-text "three approaches to Migratory Typing")
   #:go (coord SLIDE-LEFT 1/5 'lt)
   #:alt [(make-2table
     #:row-align lt-superimpose
            (list
              (list d-pict (pict->blank deep-system-pict))
              (list s-pict (pict->blank shallow-system-pict))
              (list e-pict (pict->blank erasure-system-pict))))]
   (make-2table
     #:col-sep 20
     #:row-align lt-superimpose
     (list
       (list d-pict (lc-superimpose (blank (pict-height d-pict) 0) (gt-strategy->kafka-text DEEP-TAG)))
       (list s-pict (lc-superimpose (blank (pict-height s-pict) 0) (gt-strategy->kafka-text SHALLOW-TAG)))
       (list e-pict (lc-superimpose (blank (pict-height e-pict) 0) (gt-strategy->kafka-text ERASURE-TAG)))))
   #:next
   #:go (coord 50/100 20/100 'lt)
   (parameterize ((current-para-width (w%->pixels 1/2))
                  (current-main-font SS-FONT))
     (vl-append 20
       (let-values (((a b c) (make-boundary-pict*)))
                   (scale a 0.8))
       @para{Three strategies for enforcing types at a boundary})))
  (let ((deep-txt @t{types are sound/enforced})
        (shallow-txt @t{typed code cannot get stuck})
        (erasure-txt @t{types do not affect behavior}))
    (pslide
     #:go HEADING-COORD
     (subsubtitle-text "three approaches to Migratory Typing")
     #:go (coord SLIDE-LEFT 1/5 'lt)
     #:alt [(make-2table
              #:row-align lt-superimpose
              (list
                (list d-pict (pict->blank deep-system-pict))
                (list s-pict (pict->blank shallow-system-pict))
                (list e-pict (pict->blank erasure-system-pict))))]
     #:alt [(make-2table
              #:row-align lt-superimpose
              (list
                (list d-pict (lt-superimpose (pict->blank deep-system-pict) deep-txt))
                (list s-pict (pict->blank shallow-system-pict))
                (list e-pict (pict->blank erasure-system-pict))))]
     #:alt [(make-2table
              #:row-align lt-superimpose
              (list
                (list d-pict (lt-superimpose (pict->blank deep-system-pict) deep-txt))
                (list s-pict (lt-superimpose (pict->blank shallow-system-pict) shallow-txt))
                (list e-pict (pict->blank erasure-system-pict))))]
     (make-2table
       #:row-align lt-superimpose
       (list
         (list d-pict (lt-superimpose (pict->blank deep-system-pict) deep-txt))
         (list s-pict (lt-superimpose (pict->blank shallow-system-pict) shallow-txt))
         (list e-pict (lt-superimpose (pict->blank erasure-system-pict) erasure-txt))))))
  (void))

(define (sec:boundary)
  (define-values [sd sta-pict dyn-pict] (make-boundary-pict*))
  (let* ((validate-coord (coord 1/2 1/3 'cc))
         (sd/int (add-thought/sta sd sta-pict (need-txt "Integer"))) 
         (sd/int-0 (add-thought/dyn sd/int dyn-pict @t{42}))
         (sd/int-1 (add-thought/dyn sd/int dyn-pict @t{'NaN}))
         (sd/los (add-thought/sta sd sta-pict (need-txt "Listof(Symbol)")))
         (sd/los-0 (add-thought/dyn sd/los dyn-pict @t{'(A B 3 D)}))
         (sd/ii (add-thought/sta sd sta-pict (need-txt "Bool->Bool")))
         (sd/ii-0 (add-thought/dyn sd/ii dyn-pict @t{#<procedure>})))
    (pslide
      #:go HEADING-COORD
      (subtitle-text "Typed-Untyped Interaction")
      #:go (coord 1/2 1/2 'cb)
      #:alt [sd]
      #:alt [sd/int]
      #:alt [sd/int-0 #:next #:go validate-coord (large-check-icon)]
      #:alt [sd]
      #:alt [sd/int]
      #:alt [sd/int-1 #:next #:go validate-coord (large-x-icon)]
      #:alt [sd]
      #:alt [sd/los]
      #:alt [sd/los-0 #:next #:go validate-coord (large-x-icon)]
      #:alt [sd]
      #:alt [sd/ii]
      #:alt [sd/ii-0 #:next #:go validate-coord (make-monitor-icon "Bool?")]
      sd
      #:go (coord 1/2 3/5 'ct)
      @t{Type boundaries impose a run-time cost!}
      #:go (coord 1/2 SLIDE-BOTTOM 'ct)
      (vl-append 4
        @smallt{(Some mixed-typed languages do not enforce}
        @smallt{ types. For these languages, the performance}
        @smallt{ of type boundaries is not an issue.)})))
  (void))

(define (sec:soundness)
  (define-values [H-box 1-box E-box]
    (let ((pp* (make-DSE-halo-pict*)))
      (values (tag-pict (car pp*) 'H-box)
              (tag-pict (cadr pp*) '1-box)
              (tag-pict (caddr pp*) 'E-box))))
  (define y-sep 20)
  (define y-spectrum 26/100)
  (define sound-0 (tag-pict (hb-append 0 (t "e ->* v and ") (well-t "v" "t")) 'sound-0))
  (define sound-1 (tag-pict (t "e diverges") 'sound-1))
  (define sound-2 (tag-pict (t "e ->* Error") 'sound-2))
  (define H-sound-0 (tag-pict (well-t "v" "t") 'H-sound-0))
  (define 1-sound-0 (tag-pict (well-t "v" "C(t)") '1-sound-0))
  (define E-sound-0 (tag-pict (well-t "v" #f) 'E-sound-0))
  (define sound-pict
    (vl-append 20
               (t "Type Soundness (simplified):")
               (vl-append 20
                          (hb-append 0 (t " if ") (well-t "e" "t") (t " then either:"))
                          (hb-append 0 (t " - ") sound-0)
                          (hb-append 0 (t " - ") sound-1)
                          (hb-append 0 (t " - ") sound-2))))
  (pslide
    #:go (coord 50/100 1/2 'cc)
    (let ((pp (rule (w%->pixels 34/100)
                    (+ (* 3 margin) client-h)
                    #:color (color%-update-alpha (string->color% "black") 0.1))))
      (cc-superimpose (rule (pict-width pp) (pict-height pp) #:color WHITE) pp))
    #:go (coord 18/100 SLIDE-TOP 'ct) H-box
    #:go (coord 50/100 SLIDE-TOP 'ct) 1-box
    #:go (coord 82/100 SLIDE-TOP 'ct) E-box
    #:next
    #:alt [#:go (coord 1/2 1/3 'ct)
           (cc-superimpose
             (filled-rounded-rectangle (+ 60 (pict-width sound-pict)) (+ 40 (pict-height sound-pict)) -0.05
                                       #:color "white" #:border-width 8)
             sound-pict)
           #:next
           #:alt [#:go (at-underline 'sound-0) (make-underline sound-0)]
           #:alt [#:go (at-underline 'sound-1) (make-underline sound-1)]
           #:go (at-underline 'sound-2) (make-underline sound-2)]
    #:go (at-find-pict 'H-box cb-find 'ct #:abs-y (* 4 y-sep))
    (scale-soundness
      (vl-append 20
               (hc-append 0 (t "Deep"))
               (vl-append 20
                          (hb-append 0 (t " if ") (well-t "e" "t") (t " then either:"))
                          (hb-append 0 (t " - ") (hb-append 0 (t "e ->* v and ") H-sound-0))
                          (hb-append 0 (t " - ") (t "e diverges"))
                          (hb-append 0 (t " - ") (t "e ->* Error")))))
    #:go (at-underline 'H-sound-0) (make-underline H-sound-0 #:width 50)
    #:next
    #:go (at-find-pict '1-box cb-find 'ct #:abs-y (* 4 y-sep))
    (scale-soundness
      (vl-append 20
                 (t "Shallow")
                 (vl-append 20
                            (hb-append 0 (t " if ") (well-t "e" "t") (t " then either:"))
                            (hb-append 0 (t " - ") (hb-append 0 (t "e ->* v and ") 1-sound-0))
                            (hb-append 0 (t " - ") (t "e diverges"))
                            (hb-append 0 (t " - ") (t "e ->* Error")))))
    #:go (at-underline '1-sound-0) (make-underline 1-sound-0 #:width 70)
    #:next
    #:go (at-find-pict 'E-box cb-find 'ct #:abs-y (* 4 y-sep))
    (scale-soundness
      (vl-append 20
                 (t "Erasure")
                 (vl-append 20
                            (hb-append 0 (t " if ") (well-t "e" "t") (t " then either:"))
                            (hb-append 0 (t " - ") (hb-append 0 (t "e ->* v and ") E-sound-0))
                            (hb-append 0 (t " - ") (t "e diverges"))
                            (hb-append 0 (t " - ") (t "e ->* Error")))))
    #:go (at-underline 'E-sound-0) (make-underline E-sound-0))
  (make-folklore-slide #:q2? #false #:answers? #false)
  (make-folklore-slide #:q2? #false #:answers? #true
                      ;; #:extra (cons (coord 1/2 8/10) (scale (make-spectrum-pict) 0.65))
                       )
  (void))

(define (sec:implementation)
   (pslide
    #:go HEADING-COORD
    (subsubtitle-text "Implementation")
    #:go (coord SLIDE-LEFT 1/5 'lt)
    (make-impl-pict)
    #:go (coord 1/2 1/5 'lt)
    (parameterize ((current-para-width (w%->pixels 50/100)))
      (vl-append (h%->pixels 15/100)
        @para{Three compilers for the Typed Racket surface language}
        @para{i.e. three ways of running@bt{the same code}})))
  (void))

(define (sec:lattice)
  (let* ((p0 (bigger-program (list->program '(#f #t #t #f))))
         (the-lattice-coord (coord 1/2 SLIDE-TOP 'ct))
         (the-step-coord (coord SLIDE-LEFT SLIDE-TOP 'lb #:abs-y -4))
         (-the-step-coord (coord SLIDE-RIGHT SLIDE-TOP 'rb #:abs-y -4))
         (p-typed (make-node '(#t #t #t #t)))
         (time-y-sep -2)
         (total-bits 4)
         (make-overhead (lambda (cfg) (overhead FSM-DATA (configuration-info->mean-runtime cfg))))
         (cfg->o-coord (lambda (tag) (at-find-pict tag rt-find 'rb #:abs-y time-y-sep)))
        )
    (pslide
      #:go the-lattice-coord
      #:alt [p-typed #:go CENTER-COORD (subsubtitle-text "How to measure performance?")]
      (make-lattice 4 make-node
                    #:x-margin (w%->pixels 1/70)
                    #:y-margin (h%->pixels 1/9))
      #:next
      #:alt [#:set (for/fold ((acc ppict-do-state))
                             ((cfg (in-configurations FSM-DATA))
                              (i (in-naturals)))
                     (define tag (bitstring->tag (natural->bitstring i #:bits total-bits)))
                     (ppict-do
                       acc
                       #:go (at-find-pict tag lt-find 'lb #:abs-y time-y-sep)
                       (runtime->pict (configuration-info->mean-runtime cfg))))]
      #:alt [#:set (ppict-do
                     ppict-do-state
                     #:go (cfg->o-coord 'cfg-0000)
                     (tag-pict (overhead->pict 1) 'the-tgt)
                     #:go (at-find-pict 'the-tgt rc-find 'lc #:abs-x 10)
                     (left-arrow #:color HIGHLIGHT-COLOR))]
      #:set (for/fold ((acc ppict-do-state))
                      ((cfg (in-configurations FSM-DATA))
                       (i (in-naturals)))
              (define tag (bitstring->tag (natural->bitstring i #:bits total-bits)))
              (ppict-do
                acc
                #:go (cfg->o-coord tag)
                (overhead->pict (make-overhead cfg))))
      ;#:next
      ;#:set (for/fold ((acc (cellophane ppict-do-state 0.4)))
      ;                ((cfg (in-configurations FSM-DATA))
      ;                 (i (in-naturals)))
      ;        (define tag (bitstring->tag (natural->bitstring i #:bits total-bits)))
      ;        (ppict-do
      ;          acc
      ;          #:go (at-find-pict tag cc-find 'cc)
      ;          (if (< (make-overhead cfg) 2)
      ;            (large-check-icon)
      ;            (large-x-icon))))
  ))
  ;(let* ((x-sep 50)
  ;       (ra (right-arrow #:color HIGHLIGHT-COLOR))
  ;       (lhs-pict
  ;         (hc-append 12 (make-lattice-icon) @subtitle-text{+} @bt{D}))
  ;       (rhs-pict
  ;         (make-check-x-fraction)))
  ;  (pslide
  ;    #:go HEADING-COORD
  ;    (subtitle-text "D-deliverable")
  ;    #:go (coord 1/10 20/100 'lt)
  ;    (lines-append
  ;      (hb-append @t{A configuration is } @bt{D}@it{-deliverable} @t{ if its})
  ;      (hb-append @t{performance is no worse than a factor })
  ;      (hb-append @t{of } @bt{D} @t{ slowdown compared to the baseline}))
  ;    #:go (coord 1/10 50/100 'lt)
  ;    (hc-append x-sep lhs-pict ra rhs-pict)))
  (void))

(define (sec:performance)
   (pslide
    #:go HEADING-COORD
    (subsubtitle-text "Experiment")
    #:go (coord SLIDE-LEFT 1/5 'lt)
    (make-impl-pict)
    #:go (coord 1/2 1/5 'lt)
    (parameterize ((current-para-width (w%->pixels 50/100)))
      (vl-append (h%->pixels 10/100)
        @para{10 benchmark programs}
        @para{2 to 10 modules each}
        @para{4 to 1024 configurations each}))
    #:go (coord 1/2 SLIDE-BOTTOM 'cc)
    @make-url{docs.racket-lang.org/gtp-benchmarks})
  (make-overhead-plot-slide '())
  (pslide (make-scatterplots-pict))
  (define perf-plot-pict (small-overhead-plot))
  (define (make-perf-text sym pp)
    (define-values (_n _d bx) (symbol->name+box sym))
    (ht-append (lb-superimpose (blank 55 26) (scale-to-fit bx 40 40))
               pp))
  (define-values [H-perf-txt 1-perf-text E-perf-text]
                 (parameterize ((current-para-width (w%->pixels 45/100)))
    (let ((p* (list (make-perf-text 'H @para{add types to remove all critical boundaries})
                    (make-perf-text '1 @para{add types sparingly})
                    (make-perf-text 'E @para{add types anywhere, doesn't matter}))))
      (apply values (pict-bbox-sup* p*)))))
  (pslide
    #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
    @subsubtitle-text{Performance Implications}
    #:go (coord SLIDE-LEFT 1/5 'lt)
    perf-plot-pict
    #:next
    #:go (coord 1/2 1/5 'lt)
    (vl-append (h%->pixels 1/9)
    H-perf-txt
    1-perf-text
    E-perf-text))
  (void))

(define (sec:people)
  (define-values [d-pict s-pict e-pict] (apply values (make-DSE-halo-pict*)))
  (define-values [deep-system-pict shallow-system-pict erasure-system-pict] (make-DSE-system-pict*))
  (let ((deep-txt @t{types are sound/enforced})
        (shallow-txt @t{typed code cannot get stuck})
        (erasure-txt @t{types do not affect behavior}))
    (pslide
     #:go HEADING-COORD
     (subsubtitle-text "three approaches to Migratory Typing")
     #:go (coord SLIDE-LEFT 1/5 'lt)
     (make-2table
       #:row-align lt-superimpose
       (list
         (list d-pict (pict->blank deep-system-pict))
         (list s-pict (pict->blank shallow-system-pict))
         (list e-pict (pict->blank erasure-system-pict))))
     #:go (coord 1/2 30/100 'lt)
     (comment-frame
       (vl-append (h%->pixels 5/100)
                  @t{Soundness}
                  @t{Performance}
                  @t{... Users?}))))
  (define q-w (w%->pixels 60/100))
  (define r-w (w%->pixels 66/100))
  (define (str->pict str w)
    (scale-to-fit (bitmap (make-png-path str)) w w))
  (for ((qq (in-list `(("q1" "q1-data")))))
    (make-data-slide (question-frame (str->pict (car qq) q-w))
                     (answer-frame (str->pict (cadr qq) r-w))))
  (pslide
    #:go HEADING-COORD
    (subsubtitle-text "Developer Survey")
    #:go (coord 1/10 1/5 'lt)
    (parameterize ((current-para-width (w%->pixels 75/100)))
      (vl-append (h%->pixels 5/100)
                 @para{Asked software engineers, students, and MTurk workers to rate potential@bt{different behaviors} for programs}
                 (hc-append @t{Results show a preference for } deep-pict)
                 @t{More at DLS Tuesday 10:30am The Loft}))
    #:go (coord 1/2 SLIDE-BOTTOM 'cc)
    @make-url{cs.brown.edu/research/plt/dl/dls2018})
  (void))

;; -----------------------------------------------------------------------------

(define (make-DSE-system-pict*)
  (parameterize ((current-para-width (w%->pixels 65/100))
                 #;(current-line-sep 8))
    (values
      (gt*->pict #:direction 'H (filter/embedding 'H MT-system*))
      (gt*->pict #:direction 'H (filter/embedding '1 MT-system*))
      (gt*->pict #:direction 'H (filter/embedding 'E MT-system*)))))

(define (make-racket-logo)
  (comment-frame (scale-to-fit (bitmap racket-logo.png) 150 150)))

(define (make-impl-pict)
  (define bb (make-racket-logo))
  (define dse* (map (lambda (p) (vc-append 4 (blank) p)) (make-DSE-halo-pict*)))
  (define dse-base
    (vc-append -10 (hc-append 70 (car dse*) (caddr dse*)) (cadr dse*)))
  (define no-arrows (vc-append 40 bb dse-base))
  (for/fold ((acc no-arrows))
            ((pp (in-list dse*))
             (t-find (in-list (list lb-find cb-find rb-find))))
    (pin-arrow-line 16 acc bb t-find pp ct-find #:line-width 4 #:color BLACK #:alpha 0.8)))

(define (make-overhead-plot-slide e*)
  (parameterize ([current-font-size 26])
    (pslide
      #:go (coord SLIDE-LEFT SLIDE-TOP 'lt)
      (subsubtitle-text "Performance")
      #:go (coord SLIDE-LEFT 1/5 'lt)
      (make-overhead-plot e*))))

(define (make-scatterplots-pict)
  (cc-superimpose
    (rule client-w client-h #:color WHITE)
    (scale-to-fit (bitmap cache-scatterplots.png) client-w client-h)))

;; -----------------------------------------------------------------------------

(module+ raco-pict
  (provide raco-pict)
  (define p
  (parameterize ([current-main-font MONO-FONT]
                 [current-font-size NORMAL-FONT-SIZE])
    (let ((bb (blank client-w client-h)))
      (blank)

   (;pslide
    ppict-do bb
    #:go CENTER-COORD
    (make-overhead-plot '(H 1 E)))

  )))
  (define (add-bg p)
    (cc-superimpose (blank (+ 100 (pict-width p)) (+ 100 (pict-height p))) (frame p)))
  (define raco-pict (add-bg p))
  (void))
