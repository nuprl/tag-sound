#lang at-exp racket/base

;; Utilities / setup for acmart-style Scribble papers

;; TODO cleanup

(provide
  ;; --- new stuff
  bm-desc
  blockquote
  MT
  TR
  good
  language
  MMT
  well_D
  well_S
  step_D
  step_S
  embed-sta
  embed-dyn
  well-dyn
  well-sta
  sta*
  dynstep
  dyn*
  step*
  definition
  counterexample
  lemma
  convention
  theorem
  fake-theorem
  type-error
  value-error
  include-figure
  include-figure*
  NUM-EMBEDDINGS
  EGOOD
  deliverable
  LD-Racket
  x-axis
  y-axis
  IF-TECHREPORT

  bm

  ~a

  note-to-self
  mytech
  $$
  twocolumn
  inline-pict

  proof-sketch

  appendix

  ;; ---------------------------------------------------------------------------
  ;; --- old stuff
  (all-from-out
    "bib.rkt"
    "plot.rkt"
    scribble-abbrevs
    scribble/acmart
    scribble/doclang
    scriblib/figure
    scribble/example
    scriblib/autobib)
  note ;; reprovide from scriblib/footnote
  (except-out (all-from-out scribble/manual) url)

  (rename-out
   [acmart:#%module-begin #%module-begin]

   [format-url url]
   ;; Usage: @url{URL}
   ;;  format a URL, removes the `http://` prefix if given
  )

  generate-bibliography

  ~cite
  ;; Usage: `@~cite[bib-name]`
  ;;  where `bib-name` is an identifier from `bib.rkt`
  ;; Renders a short-style citation to `bib-name`.
  ;; Example:
  ;;   @elem{We love@~cite[matthias]}
  ;; May render to:
  ;;   "We love [409]."
  ;; Where 409 is the number assigned to the bib entry that `matthias` refers to

  citet
  ;; Usage: `@citet[bib-name]`
  ;;  where `bib-name` is an identifier from `bib.rkt`
  ;; Renders a long-style citation to `bib-name`
  ;; Example:
  ;;  @elem{See work by @citet[matthias]}
  ;; May render to:
  ;;  "See work by Felleisen 1901"
  ;; If `matthias` refers to a 1901 article by Felleisen.

  python
  ;; Usage: `@python{ code }`
  ;;  where `code` is one-or-more-lines of Python code
  ;; Renders a codeblock containing Python code.

  pythonexternal
  ;; Usage: `@pythonexternal{path-string}`
  ;;  where `path-string` refers to a file containing Python code
  ;; Renders the contents of `path-string` in a Python code block

  pythoninline
  ;; Usage: `@pythoninline{code}`
  ;;  where `code` is less than 1 line of Python code
  ;; Renders some Python code in the current line of text.
  ;; Useful for formatting identifiers

  parag
)

(require
  "bib.rkt"
  "plot.rkt"
  (only-in racket/list
    add-between
    partition)
  (only-in gtp-plot/util
    log-gtp-plot-warning)
  racket/format
  racket/set
  racket/string
  scribble/acmart
  scribble/core
  scribble/example
  scribble-abbrevs
  (except-in scriblib/autobib authors)
  scriblib/figure
  setup/main-collects
  (except-in scribble/doclang
    #%module-begin)
  (only-in scribble/acmart/lang
    [#%module-begin acmart:#%module-begin])
  (except-in scribble/manual
    title author)
  (only-in scriblib/footnote
    note)
  (for-syntax racket/base syntax/parse))

;; =============================================================================

(define-cite ~cite citet pre-generate-bibliography
  #:style number-style)

(define (generate-bibliography)
  (pre-generate-bibliography #:sec-title (exact "\\refname")))

(define (python . x)
  (apply exact (append (list "\n\\begin{python}\n") x (list "\n\\end{python}\n"))))

(define (pythoninline . x)
  (apply exact (append (list "\\pythoninline{") x (list "}"))))

(define (pythonexternal a)
  (exact (format "\\pythonexternal{~a}" a)))

;; -----------------------------------------------------------------------------
;; --- new stuff (not among the GTP-paper things)

(define MMT
  (sc "mmt"))

(define (include-figure ps caption)
  (include-?figure figure ps caption))

(define (include-figure* ps caption)
  (include-?figure figure* ps caption))

(define (include-?figure make-fig ps caption)
  (define error-name (object-name make-fig))
  (define (assert-file-exists! filename)
    (unless (file-exists? filename)
      (raise-argument-error error-name "(and/c string? file-exists?)" filename)))
  (define-values [tag tex]
    (cond
     [(string? ps)
      (assert-file-exists! ps)
      (define tag (path-string->tag ps))
      (define tex (path-string->input ps))
      (values tag tex)]
     [(list? ps)
      (for-each assert-file-exists! ps)
      (define tag (apply string-append (map path-string->tag ps)))
      (define tex (path-string*->input ps))
      (values tag tex)]
     [else
      (raise-argument-error 'include-?figure "unidentified input value" 1 make-fig ps caption)]))
   (make-fig tag caption tex))

(define (path-string->tag ps)
  (path->string (path-replace-extension ps #"")))

(define (path-string*->input ps*)
  (exact (apply string-append (map format-input ps*))))

(define (path-string->input ps)
  (exact (format-input ps)))

(define (format-input ps)
  (format "\\input{~a}" ps))

(define (definition term #:key [key #f] . defn*)
  (make-thing "Definition" term defn* key))

(define (counterexample term #:key [key #f] . defn*)
  (make-thing "Counterexample" term defn* key))

(define (convention term #:key [key #f] . defn*)
  (make-thing "Convention" term defn* key))

(define (theorem term #:key [key #f] . defn*)
  (make-thing "Theorem" term defn* key))

(define (lemma term #:key [key #f] . defn*)
  (make-thing "Lemma" term defn* key))

(define (fake-theorem term #:key [key #f] . defn*)
  (make-thing "Theorem Sketch" term defn* key))

(define (good str)
  ($ (format "\\emph{good}(~a)" str)))

;; TODO add a deftech?
(define (make-thing title term defn* [key #f])
  (nested
    (list
      (exact "\\vspace{1ex}\n")
      (bold title)
      (cons (element #f (list " (" (emph term) ") ")) defn*))))

;; TODO just use Scribble's tech?
(define TECH-TERMS (mutable-set))
(define (mytech #:key [key #f] . pc*)
  (set-add! TECH-TERMS (content->string pc*))
  pc*)

(define (lemmaref what)
  (emph what))

(define (proof-sketch . elem*)
  (make-proof "Proof Sketch: " elem*))

(define (proof . elem*)
  (make-proof "Proof: " elem*))

(define (make-proof descr elem*)
  (list (emph descr) elem* @${\hfill \qedsymbol}))

(define well_D
  ($ "\\welldyn"))

(define well_S
  ($ "\\wellsta"))

(define step_D
  ($ "\\dynstep"))

(define step_S
  ($ "\\stastep"))

(define (well-dyn x)
  ($ (format "\\welldyn~~~a" x)))

(define (well-sta x t)
  ($ (format "\\wellsta~~~a : ~a" x t)))

(define (dynstep src tgt)
  (step "\\dynstep" src tgt))

(define (dyn* src tgt)
  (format-step* "\\dynstep" src tgt))

(define (sta* src tgt)
  (format-step* "\\stastep" src tgt))

(define (step* src tgt)
  (format-step* "\\rightarrow" src tgt))

(define (step arr src tgt)
  ($ (format "~a~~~a~~~a" src arr tgt)))

(define (format-step* arr src tgt)
  ($ (format "~a~~~a^*~~~a" src arr tgt)))

(define ($$ . elem*)
  (apply exact (list "\\[" elem* "\\]")))

(define two-column-style
  (style "TwoColumn" '()))

(define (twocolumn a b)
  (nested #:style 'no-break
          (nested #:style two-column-style (list a (exact "\n\\multicolsbreak\n") b))))

(define type-error
  "\\tagerror")

(define value-error
  "\\boundaryerror")

(define (embed-sta t e)
  ($ (format "\\esta{~a}{~a}" t e)))

(define (embed-dyn t e)
  ($ (format "\\edyn{~a}{~a}" t e)))

(define (do-defend t e)
  ($ (format "\\edefend{~a}{~a}" t e)))

(define (do-check t e)
  ($ (format "\\echeck{~a}{~a}" t e)))

(define (note-to-self . elem*)
  (nested #:style 'inset (emph elem*)))

(define (language x)
  (bold x))

(define (MT x)
  (bold (format "MT(~a)" x)))

(define EMBEDDINGS
  '("erased" "natural" "co-natural" "forgetful" "tagged"))

(define NUM-EMBEDDINGS
  (length EMBEDDINGS))

(define EGOOD
  (emph "good"))

(define (deliverable [D "D"])
  (define d-str
    (cond
     [(string? D)
      D]
     [(and (real? D) (positive? D))
      (number->string D)]
     [else
      (raise-argument-error 'deliverable "(or/c positive-real? string?)" D)]))
  (elem ($ d-str) "-deliverable"))

(define LD-Racket
  "Locally-Defensive Racket")

(define TR
  "Typed Racket")

(define x-axis
  (exact "\\emph{x}-axis"))

(define y-axis
  (exact "\\emph{y}-axis"))

(define (bm str)
  (define sym (string->symbol str))
  (unless (memq sym BM-NAME*)
    (log-gtp-plot-warning "unrecognized benchmark name '~a'" str))
  (tt str))

(define-for-syntax TECH-REPORT? #false)
(define-syntax (IF-TECHREPORT stx)
  (if TECH-REPORT?
    (cdr (syntax-e stx))
    #'(void)))

(define (blockquote . elem*)
  (nested #:style 'inset (emph elem*)))

(define (bm-desc title author lib . descr)
  ;(void (->benchmark title)) ;; assert that 'title' is the name of a benchmark
  (elem
    (parag title)  (smaller "from " author)
    (linebreak)
    descr))

(define appendix
  (make-paragraph (make-style 'pretitle '())
    (make-element (make-style "appendix" '(exact-chars)) '())))

(define (inline-pict p)
  (centered (list p)))
