#lang at-exp racket/base

;; Definitions for writing 21st-century proofs.
;;    https://lamport.azurewebsites.net/pubs/proof.pdf

(provide
  UID++

  clearpage
  smallskip
  newpage

  appendix-title

  tr-ref
  tr-definition
  tr-lemma
  tr-counterexample
  tr-convention
  tr-theorem
  tr-if
  tr-else

  tr-proof
  tr-case (rename-out [tr-case proofcase])

  tr-qed

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

(define (fbox$ . elem*)
  @exact{\fbox{@$[elem*]}})

;; -----------------------------------------------------------------------------

(define (tr-ref str #:key user-key)
  (define k (key->string user-key))
  (tech #:key k (emph str)))

(define (tr-definition name-elem #:key [user-key #f] . content*)
  (tr-def name-elem 'definition #:key user-key content*))

(define (tr-counterexample name-elem #:key [user-key #f] . content*)
  (tr-def name-elem 'counterexample #:key user-key content*))

(define (tr-convention name-elem #:key [key #f] . content*)
  (tr-def name-elem 'convention #:key key content*))

(define (tr-theorem name-elem #:key [key #f] . content*)
  (tr-def name-elem 'theorem #:key key content*))

(define (tr-lemma name-elem #:key [key #f] . content*)
  (tr-def name-elem 'lemma #:key key content*))

(define (tr-def name-elem
                kind
                #:key [user-key #f]
                content*)
  (define pre-key
    (or user-key (if (string? name-elem) name-elem #f)))
  (unless pre-key
    (log-techreport-warning "missing key for ~a ~a" kind name-elem))
  (define uid (next-UID))
  (define key-str
    (if pre-key
      (begin
        (register-key! pre-key kind uid)
        (key->string pre-key))
      ""))
  (nested #:style 'block
    (list
      @elem{@exact{\vspace{0.4ex}}
            @bold{@kind->long-name[kind] @|uid|} : @deftech[#:key key-str name-elem]
            @|smallskip|}
      (make-table
        boxed-style
        (list (list (nested content*)))))))

;; -----------------------------------------------------------------------------

(define (tr-proof . elem*)
  (nested
    (emph "Proof") ": "
    (nested #:style 'inset elem*)
    @${\qedsymbol}))

(define (tr-case #:itemize? [itemize? #true] #:box? [box? #false] title . content*)
  (tr-labeled "case" box? itemize? title content*))

(define (tr-if cond . content*)
  (tr-labeled "if" #false #true cond content*))

(define (tr-else cond . content*)
  (tr-labeled "else" #false #true cond content*))

(define (tr-labeled name box? itemize? title content*)
  (define width "2.4em")
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

(define (content*->items content*)
  (for/list ([c (in-list content*)]
             #:when (not (empty-content? c)))
    (item c)))

(define (empty-content? c)
  (and (string? c) (whitespace? c)))

(define whitespace?
  (let ([WHITESPACE '(#\newline #\tab #\linefeed #\space)])
    (lambda (str)
      (= 0
         (for/sum ((c (in-string str)))
           (if (memq c WHITESPACE) 0 1))))))

(define tr-and
  (list "and "))

(define (tr-by tag [thing #f])
  (list* (linebreak) "by " (tech tag)
    (if thing
      (list " applied to " thing)
      (list))))

(define (proofbyIH [why #f])
  (list* (linebreak) "by the induction hypothesis"
    (if why (list " applied to " why) '())))

(define (tr-qed . content*)
  (make-element 'no-break (cons (sc "qed ") content*)))

(define proofthen
  "then ")

(define proofbecause
  (list (linebreak) "because "))

(define proofwhere
  (list (linebreak) "where "))

(define (proofcontradiction why)
  @elem{Impossible, contradiction with @|why|})

