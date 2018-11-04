#lang racket/base

;; TODO
;; - host-lang as struct?

(require racket/contract)
(provide
  (contract-out
    [struct gt-system
            ([name string?]
             [year fixnum?]
             [host-lang string?]
             [source gt-system-source?]
             [embedding embedding?]
             [perf (>=/c 1)]
             [url string?]
             [mt? boolean?])
            #:omit-constructor]
    [all-system*
      (listof gt-system?)]
    [MT-system*
      (listof gt-system?)]
    [new-system*
      (listof gt-system?)]
    [H-system*
      (listof gt-system?)]
    [E-system*
      (listof gt-system?)]
    [1-system*
      (listof gt-system?)]
    [HE-system*
      (listof gt-system?)]
    [1E-system*
      (listof gt-system?)]
    [typed-racket
      gt-system?]
    [reticulated
      gt-system?]

    [embedding?
      (-> any/c boolean?)]
    [filter/mt
      (-> boolean? (listof gt-system?) (listof gt-system?))]
    [filter/embedding
      (-> embedding? (listof gt-system?) (listof gt-system?))]
    [filter/source
      (-> gt-system-source? (listof gt-system?) (listof gt-system?))]
    [filter/perf
      (-> (>=/c 0) (listof gt-system?) (listof gt-system?))]
    [filter-not/perf
      (-> (>=/c 0) (listof gt-system?) (listof gt-system?))]
    [filter-not/name
      (-> string? (listof gt-system?) (listof gt-system?))]
    [gt-system-source<
      (-> gt-system-source? gt-system-source? boolean?)]
    )
)

(require
  (only-in racket/set set=?)
  (only-in racket/list filter-not))

;; -----------------------------------------------------------------------------

(define the-embedding* '(H E 1))

(define embedding?
  (let ([e? (lambda (x) (memv x the-embedding*))])
    (lambda (y)
      (if (list? y)
        (andmap e? y)
        (e? y)))))

(define (embedding->string e #:short? [short? #false])
  (if short?
    (embedding->short-name e)
    (embedding->long-name e)))

(define (embedding->long-name e)
  (case e
    ((H)
     "higher-order")
    ((E)
     "erasure")
    ((1)
     "first-order")))

(define (embedding->short-name e)
  (format "~a" e))

(define the-source* '(A I))

(define gt-system-source?
  (let ([src? (lambda (x) (and (memq x the-source*) #true))])
    (lambda (y)
      (if (list? y)
        (andmap src? y)
        (src? y)))))

(struct gt-system [name year host-lang source embedding perf url mt?]
        #:transparent)

(define (make-gt-system #:name name
                        #:year year
                        #:host host
                        #:from from
                        #:embedding embedding
                        #:perf worst-case-perf
                        #:url url
                        #:mt? mt?)
  (gt-system name year host from embedding worst-case-perf url mt?))

(define (make-filter selector [eq? eq?] [not? #false])
  (lambda (e gt*)
    (let ([same? 
           (if (list? e)
             (lambda (gt)
               (let ([gt-e (selector gt)])
                 (and (list? gt-e) (set=? e gt-e))))
             (lambda (gt)
               (eq? e (selector gt))))]
          [f (if not? filter-not filter)])
      (f same? gt*))))

(define filter/embedding (make-filter gt-system-embedding))
(define filter/source (make-filter gt-system-source))
(define filter/perf (make-filter gt-system-perf >=))
(define filter-not/perf (make-filter gt-system-perf >= #true))
(define filter-not/name (make-filter gt-system-name string=? #true))
(define filter/mt (make-filter gt-system-mt? eq?))

;; -----------------------------------------------------------------------------

(define gradualtalk
  (make-gt-system #:name "Gradualtalk"
                  #:year 2014 ;; TODO support this
                  #:host "Smalltalk"
                  #:from 'A
                  #:embedding 'H
                  #:perf 10 ;; TODO support this
                  #:url "https://pleiad.cl/research/software/gradualtalk"
                  #:mt? #true))

(define typed-racket
  (make-gt-system #:name "Typed Racket"
                  #:year 2008
                  #:host "Racket"
                  #:from 'A
                  #:embedding 'H
                  #:perf 100
                  #:url "https://github.com/racket/typed-racket"
                  #:mt? #true))

(define tpd
  (make-gt-system #:name "TPD"
                  #:year 2017
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding 'H
                  #:perf 1.4
                  #:url "https://github.com/jack-williams/tpd"
                  #:mt? #true))

(define strongscript
  (make-gt-system #:name "StrongScript"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding '(H E)
                  #:perf 10
                  #:url "https://plg.uwaterloo.ca/~dynjs/strongscript"
                  #:mt? #false))

(define actionscript
  (make-gt-system #:name "ActionScript"
                  #:year 2006
                  #:host "ActionScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://www.adobe.com/devnet/actionscript.html"
                  #:mt? #true))

(define mypy
  (make-gt-system #:name "mypy"
                  #:year 2012
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "http://mypy-lang.org"
                  #:mt? #true))

(define flow
  (make-gt-system #:name "Flow"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://flow.org"
                  #:mt? #true))

(define hack
  (make-gt-system #:name "Hack"
                  #:year 2011
                  #:host "PHP"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "http://hacklang.org"
                  #:mt? #true))

(define pyre
  (make-gt-system #:name "Pyre"
                  #:year 2018
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://pyre-check.org"
                  #:mt? #true))

(define pytype
  (make-gt-system #:name "Pytype"
                  #:year 2015
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://opensource.google.com/projects/pytype"
                  #:mt? #true))

(define rtc
  (make-gt-system #:name "rtc"
                  #:year 2013
                  #:host "Ruby"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "https://github.com/plum-umd/rtc"
                  #:mt? #true))

(define maclisp
  (make-gt-system #:name "MACLISP"
                  #:year 1990
                  #:host "MACLISP"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "http://maclisp.info"
                  #:mt? #true))

(define common-lisp
  (make-gt-system #:name "Common Lisp"
                  #:year 1990
                  #:host "Common Lisp"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://common-lisp.net"
                  #:mt? #true))

(define strongtalk
  (make-gt-system #:name "Strongtalk"
                  #:year 1993
                  #:host "Smalltalk"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "http://strongtalk.org"
                  #:mt? #true))

(define typescript
  (make-gt-system #:name "TypeScript"
                  #:year 2012
                  #:host "JavaScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://www.typescriptlang.org"
                  #:mt? #true))

(define typed-clojure
  (make-gt-system #:name "Typed Clojure"
                  #:year 2012
                  #:host "Clojure"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "http://typedclojure.org"
                  #:mt? #true))

(define typed-lua
  (make-gt-system #:name "Typed Lua"
                  #:year 2014
                  #:host "Lua"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "https://github.com/andremm/typedlua"
                  #:mt? #true))

(define pyret
  (make-gt-system #:name "Pyret"
                  #:year 2013
                  #:host "Pyret"
                  #:from 'A
                  #:embedding '(E 1)
                  #:perf 1.2
                  #:url "https://www.pyret.org"
                  #:mt? #true))

(define thorn
  (make-gt-system #:name "Thorn"
                  #:year 2010
                  #:host "Thorn"
                  #:from 'A
                  #:embedding '(E 1)
                  #:perf 1.1
                  #:url "http://janvitek.org/yearly.htm"
                  #:mt? #false))

(define dart2
  (make-gt-system #:name "Dart 2"
                  #:year 2018
                  #:host "Dart 2"
                  #:from 'I
                  #:embedding '1
                  #:perf 1.1
                  #:url "https://www.dartlang.org/dart-2"
                  #:mt? #false))

(define dart1
  (make-gt-system #:name "Dart 1"
                  #:year 2012
                  #:host "Dart 1"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1.1
                  #:url "https://v1-dartlang-org.firebaseapp.com"
                  #:mt? #true))

(define nom
  (make-gt-system #:name "Nom"
                  #:year 2017
                  #:host "Nom"
                  #:from 'A
                  #:embedding '1
                  #:perf 1.2 ;; TODO
                  #:url "https://www.cs.cornell.edu/~ross/publications/nomalive"
                  #:mt? #false))

(define pycket
  (make-gt-system #:name "Pycket"
                  #:year 2017
                  #:host "Racket"
                  #:from 'A
                  #:embedding 'H
                  #:perf 3 ;; TODO
                  #:url "https://github.com/pycket/pycket"
                  #:mt? #true))

(define reticulated
  (make-gt-system #:name "Reticulated"
                  #:year 2014
                  #:host "Python"
                  #:from 'A
                  #:embedding '1
                  #:perf 3 ;; TODO
                  #:url "https://github.com/mvitousek/reticulated"
                  #:mt? #true))

(define safets
  (make-gt-system #:name "SafeTS"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url "https://www.microsoft.com/en-us/research/publication/safe-efficient-gradual-typing-for-typescript-3"
                  #:mt? #false))

(define grace
  (make-gt-system #:name "Grace"
                  #:year 2017
                  #:host "Grace"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url "http://gracelang.org/applications/home"
                  #:mt? #true))

(define pallene
  (make-gt-system #:name "Pallene"
                  #:year 2018
                  #:host "Lua"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url "https://github.com/pallene-lang"
                  #:mt? #true))

(define titan
  (make-gt-system #:name "Titan"
                  #:year 2018
                  #:host "Lua"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url "https://github.com/titan-lang"
                  #:mt? #true))

(define all-system*
  (list gradualtalk typed-racket tpd strongscript #;actionscript mypy pallene
        grace flow hack pyre pytype rtc safets maclisp common-lisp strongtalk
        typescript typed-clojure typed-lua pyret thorn dart1 dart2 nom pycket
        reticulated))

(define MT-system*
  (list gradualtalk typed-racket tpd strongscript mypy pallene
        grace flow hack pyre pytype rtc safets maclisp common-lisp strongtalk
        typescript typed-clojure typed-lua pyret pycket reticulated))

(define tr-e
  (make-gt-system #:name "TR-E"
                  #:year 2018
                  #:host "Racket"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url ""
                  #:mt? #true))

(define tr-1
  (make-gt-system #:name "TR-1"
                  #:year 2018
                  #:host "Racket"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url ""
                  #:mt? #true))

(define new-system*
  (list tr-e tr-1))

(define H-system*
  (filter/embedding 'H all-system*))

(define E-system*
  (filter/embedding 'E all-system*))

(define 1-system*
  (filter/embedding '1 all-system*))

(define HE-system*
  (filter/embedding '(H E) all-system*))

(define 1E-system*
  (filter/embedding '(E 1) all-system*))

(define (make-derived< x->nat)
  (lambda (a b)
    (<= (x->nat a)
        (x->nat b))))

(define (source->nat src)
  (cond
    [(eq? src 'A)
     0]
    [(pair? src)
     1]
    [(eq? src 'I)
     2]
    [else
      (raise-argument-error 'source->nat "source?" src)]))

(define gt-system-source< (make-derived< source->nat))

;; -----------------------------------------------------------------------------

(module+ test
  (require rackunit)

  (test-case "filter/embedding"
    (check-true (and (member thorn 1E-system*) #true))
    (check-false (and (member thorn H-system*) #true)))

  (test-case "filter/source"
    (let ((E/I-system* (filter/source 'I E-system*)))
      (check-true (and (member mypy E/I-system*) #true))
      (check-false (and (member typed-racket E/I-system*) #true))))

  (test-case "filter/perf"
    (let ((slow (filter-not/perf 90 all-system*)))
      (check-equal? 1 (length slow))
      (check-equal? (list typed-racket) slow))
    (let ((fast (filter/perf 90 all-system*)))
      (check-true (not (member typed-racket fast)))))

  (test-case "gt-system-source"
    (check-true (gt-system-source? 'A))
    (check-true (gt-system-source? 'I))
    (check-true (gt-system-source? '(A I)))
    (check-true (gt-system-source? '(I A))))
)
