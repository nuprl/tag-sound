#lang racket/base

;; Utilities / setup for acmart-style Scribble papers

(provide
  (all-from-out
    "bib.rkt"
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
)

(require
  "bib.rkt"
  (only-in racket/class
    class new super-new object% define/public)
  (only-in racket/list
    add-between
    partition)
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
