#lang at-exp racket/base

;; Definitions for writing 21st-century proofs.
;;    https://lamport.azurewebsites.net/pubs/proof.pdf

;; TODO
;; - structured theorems, instead of this free-form English
;; - names for steps,
;;   names for assumptions
;; - clearer "by" ... this is a mini proof
;; - comments, between steps
;; - HTML backend
;;   - configure math renderer
;;   - click to show/hide proof/cases

(provide
  UID++

  clearpage
  smallskip
  newpage

  appendix-title
  appendix-title++

  tr-ref
  tr-definition
  tr-lemma
  tr-counterexample
  tr-convention
  tr-theorem
  tr-corollary
  tr-if
  tr-else
  tr-step
  tr-IH
  tr-proof
  tr-case
  tr-and
  tr-or

  tr-qed
  tr-contradiction
)

(require
  scribble/core
  scribble/base
  (only-in scribble/manual
    defidform
    deftech
    tech)
  (only-in scribble/decode
    make-splice)
  ;scribble/struct
  (only-in racket/format
    ~a)
)

;; =============================================================================

(define UID
  (mcons 0 0))

(define (UID+)
  (define old (mcdr UID))
  (set-mcdr! UID (+ old 1))
  (void))

(define (UID++)
  (define old (mcar UID))
  (set-mcar! UID (+ old 1))
  (set-mcdr! UID 0)
  (void))

(define (next-UID)
  (begin0
    (format "~a.~a" (mcar UID) (mcdr UID))
    (UID+)))

(define NAME+UID
  (make-hash))

(define kind?
  symbol?)

(define (register-key! user-key kind uid)
  (when (hash-has-key? NAME+UID user-key)
    (log-techreport-error "duplicate key ~a" user-key))
  (hash-set! NAME+UID user-key (cons kind uid)))

(define (key->string user-key)
  ;;(define kind+uid
  ;;  (hash-ref NAME+UID user-key (λ () (log-techreport-warning "undefined key ~a" user-key) '(??? . "???"))))
  ;;(format "~a ~a: ~a" (kind->abbrev (car kind+uid)) (cdr kind+uid) user-key)
  user-key)

(define (kind->abbrev k)
  (case k
   [(definition)
    "defn."]
   [(lemma)
    "lemma"]
   [(corollary)
    "corollary"]
   [(theorem)
    "theorem"]
   [(counterexample)
    "counterexample"]
   [else
    (symbol->string k)]))

(define (kind->long-name k)
  (case k
   [(definition)
    "Definition"]
   [(lemma)
    "Lemma"]
   [(theorem)
    "Theorem"]
   [(corollary)
    "Corollary"]
   [(convention)
    "Convention"]
   [(counterexample)
    "Counterexample"]
   [(example)
    "Example"]
   [else
    (symbol->string k)]))

;; -----------------------------------------------------------------------------

(define-logger techreport)

;; -----------------------------------------------------------------------------

(define boxed-style
  (make-style 'boxed '()))

(define (exact str*)
  (make-element (make-style "relax" '(exact-chars)) str*))

(define ($ str*)
  (make-element (make-style "relax" '(exact-chars))
    (list "$" str* "$")))

(define (sc str)
  @exact{@~a{\textsc{@|str|}}})

(define smallskip
  @exact{\smallskip})

(define clearpage
  @exact{\clearpage})

(define newpage
  @exact{\newpage})

(define-syntax-rule (appendix-title stuff ...)
  (list
    (para #:style 'pretitle clearpage)
    (title stuff ...)))

(define-syntax-rule (appendix-title++ stuff ...)
  (begin
    (UID++)
    (appendix-title stuff ...)))

(define (fbox$ . elem*)
  @exact{\fbox{@$[elem*]}})

;; -----------------------------------------------------------------------------

(define missing-key 'missing-key)

(define (tr-ref #:key user-key . pc*)
  (define k (key->string user-key))
  (tech #:key k (emph pc*)))

(define (tr-definition name-elem #:key [user-key missing-key] . content*)
  (tr-def name-elem 'definition #:key user-key content*))

(define (tr-counterexample name-elem #:key [user-key missing-key] . content*)
  (tr-def name-elem 'counterexample #:key user-key content*))

(define (tr-convention name-elem #:key [key missing-key] . content*)
  (tr-def name-elem 'convention #:key key content*))

(define (tr-theorem name-elem #:key [key missing-key] . content*)
  (tr-def name-elem 'theorem #:key key content*))

(define (tr-corollary name-elem #:key [key missing-key] . content*)
  (tr-def name-elem 'corollary #:key key content*))

(define (tr-lemma name-elem #:key [key missing-key] . content*)
  (tr-def name-elem 'lemma #:key key content*))

(define (tr-def name-elem
                kind
                #:key [user-key missing-key]
                content*)
  (define pre-key
    (if (string? user-key)
      user-key
      (if (string? name-elem)
        name-elem
        #false)))
  (when (eq? pre-key missing-key)
    (log-techreport-warning "missing key for ~a ~a" kind name-elem))
  (define uid (next-UID))
  (define key-str
    (if pre-key
      (begin
        (register-key! pre-key kind uid)
        (key->string pre-key))
      #false))
  (nested #:style 'block
    (list
      @elem{@exact{\vspace{0.4ex}}
            @bold{@kind->long-name[kind] @|uid|} : @(if key-str @deftech[#:key key-str name-elem] @emph[name-elem])
            @exact{\vspace{0.2ex}}}
      (make-table
        boxed-style
        (list (list (nested content*)))))))

;; -----------------------------------------------------------------------------

(define (tr-proof . elem*)
  (nested
    (emph "Proof") ": "
    (nested #:style 'inset elem*)
    @exact{\raisebox{0.5ex}{$\qedsymbol$}}))

(define (tr-case #:itemize? [itemize? #true] #:box? [box? #false] title . content*)
  (tr-labeled "case" box? itemize? title content*))

(define (tr-if #:itemize? [itemize? #true] cond . content*)
  (tr-labeled "if" #false itemize? cond content*))

(define (tr-else #:itemize? [itemize? #true] cond . content*)
  (tr-labeled "else" #false itemize? cond content*))

(define (tr-labeled name box? itemize? title content*)
  (define width
    (make-hpad (string-length name)))
  (list
    @elem{@exact{@~a{\makebox[@|width|][l]{\textbf{\textsc{@|name|}}}}}
          @(if box?
             (let ((raise (cond
                           [(integer? box?)
                            (format "-~aex" box?)]
                           [(string? box?)
                            box?]
                           [else
                            "-3ex"])))
               @exact{@~a{\raisebox{@|raise|}{\fbox{@content->string[title]}}}})
             title)@(if #false #;box? "" " :")}
    (nested #:style 'inset
      (if itemize?
        (apply itemlist #:style 'ordered (content*->items content*))
        content*))))

(define (make-hpad n)
  (format "~aem" (* 0.6 n)))

(define (content*->items content*)
  (for/list ([c (in-list content*)]
             #:when (non-empty-content? c))
    (item c)))

(define (non-empty-content? c)
  (not (empty-content? c)))

(define (empty-content? c)
  (and (string? c) (whitespace? c)))

(define whitespace?
  (let ([WHITESPACE '(#\newline #\tab #\linefeed #\space)])
    (lambda (str)
      (= 0
         (for/sum ((c (in-string str)))
           (if (memq c WHITESPACE) 0 1))))))

(define (tr-step what . pre-why*)
  (define why* (filter non-empty-content? pre-why*))
  (if (null? why*)
    what
    (list* what (linebreak) "by " why*)))

(define tr-IH
  "the induction hypothesis")

(define (tr-and [n #f])
  (tr-conjunction "\\wedge" n))

(define (tr-or [n #f])
  (tr-conjunction "\\vee" n))

(define (tr-conjunction str n)
  (string-append
    "\\\\"
    (if n (format "\\hspace*{~a}" (make-hpad n)) "")
    str))

(define (tr-qed . content*)
  (elem (cons (sc "qed ") content*)))

(define (tr-contradiction . why*)
  (elem (cons "Contradiction by " why*)))
