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
    (sec:embeddings)
#;    (sec:implementation)
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
    (make-embeddings-pict))
  (pslide
    #:go (coord 2/4 1/4)
    (tag-pict @t{e} 'e)
    #:go (coord 1/4 1/2)
    ->H
    #:go (coord 2/4 1/2)
    ->E
    #:go (coord 3/4 1/2)
    ->1
    #:set (for/fold ([p ppict-do-state])
                    ([tag (in-list '(->H ->E ->1))]
                     [?-find (in-list (list lb-find cb-find rb-find))])
            (pin-arrow-line 8 p
                            (find-tag p 'e) ?-find
                            (find-tag p tag) ct-find))
    )
  (main-results-slide)
  (void))

(define (sec:embeddings)
  (embedding:warmup)
  (embedding:H)
  (embedding:E)
  (embedding:1)
  (embedding:end)
  (void))

(define (embedding:warmup)
  (pslide
    (make-embeddings-pict)
    ;; goto center, add boundary pict
    #:go (coord 1/2 1/2)
    (disk 40) ;; typed world , untyped world, boundary, value crossing over
    )
  (pslide
    @t{t ::= Nat  Int  t x t  t - t}
    @t{Nat <: Int}
    @t{v ::= n  i  <v,v>  lam x e  lam x:t e}
    @t{n subset i}
    @t{e ::= ....  dyn t e  stat t e}
    @comment{
    })
  (pslide
    @t{- e      - e : t}
    @t{ blah }
    @t{ - e / - dyn t e : t}
    @t{ - e : t / - stat t e}
    @comment{
    })
  (pslide
    @t{(f (dyn NatxNat <-1,-2>))}
    @comment{
    })
  (pslide
    @t{typed world .. f    untyped world pair    boundary}
    @comment{
    })
  (void))

(define (embedding:H)
  (pslide
    ;; TODO highlight H
    (make-embeddings-pict))
  (pslide
    @t{f x <-- NxN -- <-1,-2>}
    @t{rejected}
    @comment{
    })
  (pslide
    @t{sig :: dyn t v = v}
    @t{dyn Nat n = n}
    @t{dyn Int i = i}
    @t{dyn t0xt1 <v0v1> = <dyn,dyn>}
    @t{dyn td->tc \x:t.e = \x (stat tc ((\x:t.e) (dyn td x)))}
    @t{dyn t v = BE otherwise}
    @comment{
    })
  (void))

(define (embedding:E)
  (pslide
    (make-embeddings-pict H-system*)
    ;; TODO highlight E
    @comment{
    })
  (pslide
    @t{f x <-- NxN -- <-1,-2>}
    @t{OK}
    @comment{
    })
  (pslide
    @t{sig :: dyn t v = v}
    @t{dyn Nat v = v}
    @t{dyn Int v = v}
    @t{dyn t0xt1 v = v}
    @t{dyn td->tc v = v}
    @comment{
    })
  (pslide
    @t{sig :: dyn t v = v}
    @t{dyn t v = v}
    @comment{
      simple!!!
    })
  (void))

(define (embedding:1)
  (pslide
    (make-embeddings-pict H-system* E-system*)
    ;; TODO highlight 1
    @comment{
    })
  (pslide
    @t{f x <-- NxN -- <-1,-2>}
    @t{OK (transient)}
    @comment{
    })
  (pslide
    @t{sig :: dyn t v = v}
    @t{dyn Nat n = n}
    @t{dyn Int i = i}
    @t{dyn t0xt1 <v0v1> = <v0v1>}
    @t{dyn td->tc \x e = \x e}
    @comment{
    })
  (pslide
    @t{Tworld <-- Uworld}
    @t{move delta to Uworld}
    @comment{
    })
  (pslide
    (make-embeddings-pict H-system* E-system*)
    ;; TODO highlight 1
    @comment{
    })
  (void))

(define (embedding:end)
  (pslide
    (make-embeddings-pict H-system* E-system* 1-system* HE-system* 1E-system*)
    @comment{
    })
  (void))

(define (sec:implementation)
  ;; two new points
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
    @t{One surface language}
    @t{Two typing systems}
    @t{Three semantics}
    @t{Three pairs of soundness theorems}
    @t{Three implementations}
    @comment{
      in particular start with one surface language that admits
      typed code and untyped code, then define three ways of running a surface expression
      we call these strategies [higher-order erasure first-order] together they provide
      a nice foundation for understanding the literature
    })
  (void))

(define (make-gtspace-bg)
  (cellophane (filled-rectangle client-w client-h #:color "darkcyan") 0.2))

(define (make-base-embeddings-pict)
  (ppict-do
    (make-gtspace-bg)
    #:go (coord 1/4 1/4)
    (filled-rectangle 100 100 #:color RED)
    #:go (coord 3/4 1/2)
    (filled-rectangle 100 100 #:color BLUE)
    #:go (coord 1/4 3/4)
    (filled-rectangle 100 100 #:color GREEN)))

(define (make-embeddings-pict . gt-system-tree)
  ;(define gt* (flatten gt-system-tree))
  ;(define H* (filter/embedding 'H gt*))
  ;(define E* (filter/embedding 'E gt*))
  ;(define 1* (filter/embedding '1 gt*))
  ;(define HE-system* (filter/embedding '(H E) gt*))
  ;(define 1E-system* (filter/embedding '(E 1) gt*))
  (make-base-embeddings-pict))

(define (comment . stuff*)
  (blank 0 0))

;; =============================================================================

(module+ main
  (do-show))

(module+ test
  (require rackunit)

  (test-case "yolo"
    (check-true #true)))
