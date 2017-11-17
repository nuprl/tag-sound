#lang at-exp racket/base

;; Utilities / setup for acmart-style Scribble papers

(provide
  ;; --- new stuff
  bm-desc
  lib
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
  theorem
  fake-theorem
  type-error
  value-error
  proof
  proof-sketch
  include-figure
  include-figure*
  NUM-EMBEDDINGS
  EGOOD
  deliverable
  LD-Racket
  x-axis
  y-axis
  IF-TECHREPORT

  D-SAFETY
  S-SAFETY
  E-SAFETY
  N-SAFETY
  C-SAFETY
  F-SAFETY
  K-SAFETY
  bm

  ~a

  note-to-self

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
  (only-in racket/class
    class new super-new object% define/public)
  (only-in racket/list
    add-between
    partition)
  (only-in gtp-plot/util
    log-gtp-plot-warning)
  racket/format
  racket/string
  scribble/acmart
  scribble/core
  scribble/example
  scribble/html-properties
  scribble/latex-properties
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

(define small-number-style
  (let ([autobib-style-extras
        (let ([abs (lambda (s)
                     (path->main-collects-relative
                      (collection-file-path s "scriblib")))])
          (list
           (make-css-addition (abs "autobib.css"))
           (make-tex-addition (abs "autobib.tex"))))])
    (new
     (class object%
       (define/public (bibliography-table-style)
         (make-style "AutoBibliography" autobib-style-extras))
       (define/public (entry-style)
         (make-style "Autocolbibentry" autobib-style-extras))
       (define/public (disambiguate-date?) #f)
       (define/public (collapse-for-date?) #f)
       (define/public (get-cite-open) "[")
       (define/public (get-cite-close) "]")
       (define/public (get-group-sep) ", ")
       (define/public (get-item-sep) ", ")
       (define/public (render-citation date-cite i)
         (make-element
          (make-style "Thyperref" (list (command-extras (list (make-label i)))))
          (list (number->string i))))
       (define/public (render-author+dates author dates) dates)
       (define (make-label i)
         (string-append "autobiblab:" (number->string i)))
       (define/public (bibliography-line i e)
         (list (make-paragraph plain
                               (make-element (make-style "Autocolbibnumber"
                                                         autobib-style-extras)
                                             (list
                                              (make-element (make-style "label" null)
                                                            (make-label i))
                                              "[" (number->string i) "]")))
               e))
       (super-new)))))

(define-cite ~cite citet generate-bibliography
  #:style small-number-style)

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
  (unless (and (string? ps) (file-exists? ps))
    (raise-argument-error 'include-figure "(and/c string? file-exists?)" ps))
  (define tag (path-string->tag ps))
  (define tex (path-string->input ps))
  (figure tag caption tex))

(define (include-figure* ps caption)
  (unless (and (string? ps) (file-exists? ps))
    (raise-argument-error 'include-figure* "(and/c string? file-exists?)" ps))
  (define tag (path-string->tag ps))
  (define tex (path-string->input ps))
  (figure* tag caption tex))

(define (path-string->tag ps)
  (path->string (path-replace-extension ps #"")))

(define (path-string->input ps)
  (exact (format "\\input{~a}" ps)))

(define (definition term . defn*)
  (make-thing "Definition" term defn*))

(define (theorem term . defn*)
  (make-thing "Theorem" term defn*))

(define (fake-theorem term . defn*)
  (make-thing "Theorem Sketch" term defn*))

(define (good str)
  ($ (format "\\emph{good}(~a)" str)))

(define (make-thing title term defn*)
  (para #:style plain
    (list
      (exact "\\vspace{1ex}\n")
      (bold title)
      (cons (element #f (list " (" (emph term) ") ")) defn*))))

;; TODO say "proof sketch" instead of "proof"
(define (proof-sketch . elem*)
  (make-proof "Proof Sketch: " elem*))

(define (proof . elem*)
  (make-proof "Proof: " elem*))

(define (make-proof descr elem*)
  (para (list (emph descr) elem* @${\hfill \qedsymbol})))

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

(define type-error
  "\\typeerror")

(define value-error
  "\\valueerror")

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

(define D-SAFETY
  (list
    @theorem[@elem{@${\langD} soundness}]{
      If @${\welldyn e} then either:
    }
    @itemlist[
    @item{ @${e~\rrDstar~v} }
    @item{ @${e~\rrDstar~\typeerror} }
    @item{ @${e~\rrDstar~\valueerror} }
    @item{ @${e} diverges } ]))

(define S-SAFETY
  (list
    @theorem[@elem{@${\langS} type soundness}]{
      If @${\wellsta e : \tau} then either:
    }
    @itemlist[
      @item{ @${e~\rrSstar~v} and @${\wellsta v} }
      @item{ @${e~\rrSstar~\valueerror} }
      @item{ @${e} diverges } ]))

(define E-SAFETY
  (list
    @theorem[@elem{@${\langE} term safety}]{
      If @${\wellM e : \tau} then @${\wellEE e} and either:
    }
    @itemlist[
    @item{ @${e~\rrEEstar~v} and @${\wellEE v} }
    @item{ @${e~\rrEEstar~\typeerror} }
    @item{ @${e~\rrEEstar~\valueerror} }
    @item{ @${e} diverges } ]))

(define N-SAFETY
  (list
    @theorem[@elem{@${\langN} type soundness}]{
      If @${\wellM e : \tau} then @${\wellNE e : \tau} and either:
    }
    @itemlist[
    @item{ @${e \rrNEstar v} and @${\wellNE v : \tau} }
    @item{ @${e \rrNEstar E[e'] \ccND \typeerror} }
    @item{ @${e \rrNEstar \valueerror} }
    @item{ @${e} diverges } ]))

(define C-SAFETY
  (list
    @theorem[@elem{@${\langL} type safety}]{
      If @${\wellM e : \tau} then @${\wellLE e : \tau} and either:
    }
    @itemlist[
    @item{ @${e \rrLEstar v} and @${\wellLE v : \tau} }
    @item{ @${e \rrLEstar E[e'] \ccLD \typeerror} }
    @item{ @${e \rrLEstar \valueerror} }
    @item{ @${e} diverges }]))

(define F-SAFETY
  (list
    @theorem[@elem{@${\langF} type soundness}]{
      If @${\wellM e : \tau} then @${\wellFE e : \tau} and either:
    }
    @itemlist[
    @item{ @${e \rrFEstar v} and @${\wellFE v : \tau} }
    @item{ @${e \rrFEstar E[e'] \ccFD \typeerror} }
    @item{ @${e \rrFEstar \valueerror} }
    @item{ @${e} diverges } ]))

(define K-SAFETY
  (list
    @theorem[@elem{@${\langK} type-tag soundness}]{
      If @${\wellM e : \tau}
       and @${\tagof{\tau} = K}, then
       @${\wellM e : \tau \carrow e^+}
       and
       @${\wellKE e^+ : K}
       and either:
    }
    @itemlist[
    @item{ @${e^+ \rrKEstar v} and @${\wellKE v : K} }
    @item{ @${e^+ \rrKEstar E[e'] \ccKD \typeerror} }
    @item{ @${e^+ \rrKEstar \valueerror} }
    @item{ @${e^+} diverges } ]))

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
  "Tagged Racket")

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
    ;ignore `url`
    (format-deps lib)
    (linebreak)
    descr))

(define (format-deps dep*)
  (if (null? dep*)
    "No dependencies."
    (let-values ([(lib* other*) (partition lib? dep*)])
      (list "Depends on "
            (cond
             [(null? lib*)
              other*]
             [(null? other*)
              (format-lib lib*)]
             [else
              (list (format-lib lib*) ", and " other*)])
            "."))))

(define (format-lib lib*)
  (define n*
    (for/list ([l (in-list lib*)])
      (hyperlink (lib-url l) (tt (lib-name l)))))
  (define l-str (if (null? (cdr lib*)) "library" "libraries"))
  (list "the " (authors* n*) " " l-str))

(struct lib [name url] #:transparent)
