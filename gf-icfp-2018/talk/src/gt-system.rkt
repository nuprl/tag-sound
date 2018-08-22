#lang racket/base

;; TODO
;; - host-lang as struct?

(require racket/contract)
(provide
  (contract-out
    [all-system*
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

    [gt-system->pict
      (-> gt-system? pict?)]
    [embedding?
      (-> any/c boolean?)]
    [filter/embedding
      (-> embedding? (listof gt-system?) (listof gt-system?))]
    )
  )

(require
  pict
  racket/set)

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
  (let ([src? (lambda (x) (memq x the-source*))])
    (lambda (y)
      (if (list? y)
        (andmap src? y)
        (src? y)))))

(struct gt-system [name year host-lang source embedding perf url]
        #:transparent)

(define (gt-system->pict gt)
  (void))

(define (make-gt-system #:name name
                        #:year year
                        #:host host
                        #:from from
                        #:embedding embedding
                        #:perf worst-case-perf
                        #:url url)
  (gt-system name year host from embedding worst-case-perf url))

(define (filter/embedding e gt*)
  (define same-embedding?
    (if (list? e)
      (lambda (gt)
        (let ([gt-e (gt-system-embedding gt)])
          (and (list? gt-e) (set=? e gt-e))))
      (lambda (gt)
        (eq? e (gt-system-embedding gt)))))
  (filter same-embedding? gt*))

;; -----------------------------------------------------------------------------

(define gradualtalk
  (make-gt-system #:name "Gradualtalk"
                  #:year 2014 ;; TODO support this
                  #:host "Smalltalk"
                  #:from 'A
                  #:embedding 'H
                  #:perf 10 ;; TODO support this
                  #:url "https://pleiad.cl/research/software/gradualtalk"))

(define typed-racket
  (make-gt-system #:name "Typed Racket"
                  #:year 2008
                  #:host "Racket"
                  #:from 'A
                  #:embedding 'H
                  #:perf 100
                  #:url "https://github.com/racket/typed-racket"))

(define tpd
  (make-gt-system #:name "TPD"
                  #:year 2017
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding 'H
                  #:perf 1.4
                  #:url "https://github.com/jack-williams/tpd"))

(define strongscript
  (make-gt-system #:name "StrongScript"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding '(H E)
                  #:perf 10
                  #:url "https://plg.uwaterloo.ca/~dynjs/strongscript"))

(define actionscript
  (make-gt-system #:name "ActionScript"
                  #:year 2006
                  #:host "ActionScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://www.adobe.com/devnet/actionscript.html"))

(define mypy
  (make-gt-system #:name "mypy"
                  #:year 2012
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "http://mypy-lang.org"))

(define flow
  (make-gt-system #:name "Flow"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://flow.org"))

(define hack
  (make-gt-system #:name "Hack"
                  #:year 2011
                  #:host "PHP"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "http://hacklang.org"))

(define pyre
  (make-gt-system #:name "Pyre"
                  #:year 2018
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://pyre-check.org"))

(define pytype
  (make-gt-system #:name "Pytype"
                  #:year 2015
                  #:host "Python"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://opensource.google.com/projects/pytype"))

(define rtc
  (make-gt-system #:name "rtc"
                  #:year 2013
                  #:host "Ruby"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "https://github.com/plum-umd/rtc"))

(define strongtalk
  (make-gt-system #:name "Strongtalk"
                  #:year 1993
                  #:host "Smalltalk"
                  #:from '(A I)
                  #:embedding 'E
                  #:perf 1
                  #:url "http://strongtalk.org"))

(define typescript
  (make-gt-system #:name "TypeScript"
                  #:year 2012
                  #:host "JavaScript"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1
                  #:url "https://www.typescriptlang.org"))

(define typed-clojure
  (make-gt-system #:name "Typed Clojure"
                  #:year 2012
                  #:host "Clojure"
                  #:from '(A I)
                  #:embedding 'E
                  #:perf 1
                  #:url "http://typedclojure.org"))

(define typed-lua
  (make-gt-system #:name "Typed Lua"
                  #:year 2014
                  #:host "Lua"
                  #:from 'A
                  #:embedding 'E
                  #:perf 1
                  #:url "https://github.com/andremm/typedlua"))

(define pyret
  (make-gt-system #:name "Pyret"
                  #:year 2013
                  #:host "Pyret"
                  #:from 'A
                  #:embedding '(E 1)
                  #:perf 1.2
                  #:url "https://www.pyret.org"))

(define thorn
  (make-gt-system #:name "Thorn"
                  #:year 2010
                  #:host "Thorn"
                  #:from 'A
                  #:embedding '(E 1)
                  #:perf 1.1
                  #:url "http://janvitek.org/yearly.htm"))

(define dart2
  (make-gt-system #:name "Dart 2"
                  #:year 2018
                  #:host "Dart 2"
                  #:from 'I
                  #:embedding '1
                  #:perf 1.1
                  #:url "https://www.dartlang.org/dart-2"))

(define dart1
  (make-gt-system #:name "Dart 1"
                  #:year 2012
                  #:host "Dart 1"
                  #:from 'I
                  #:embedding 'E
                  #:perf 1.1
                  #:url "https://v1-dartlang-org.firebaseapp.com"))

(define nom
  (make-gt-system #:name "Nom"
                  #:year 2017
                  #:host "Nom"
                  #:from 'A
                  #:embedding '1
                  #:perf 1.2 ;; TODO
                  #:url "https://www.cs.cornell.edu/~ross/publications/nomalive"))

(define pycket
  (make-gt-system #:name "Pycket"
                  #:year 2017
                  #:host "Racket"
                  #:from 'A
                  #:embedding 'H
                  #:perf 3 ;; TODO
                  #:url "https://github.com/pycket/pycket"))

(define reticulated
  (make-gt-system #:name "Reticulated"
                  #:year 2014
                  #:host "Python"
                  #:from 'A
                  #:embedding '1
                  #:perf 3 ;; TODO
                  #:url "https://github.com/mvitousek/reticulated"))

(define safets
  (make-gt-system #:name "SafeTS"
                  #:year 2015
                  #:host "JavaScript"
                  #:from 'A
                  #:embedding '1
                  #:perf 1
                  #:url "https://www.microsoft.com/en-us/research/publication/safe-efficient-gradual-typing-for-typescript-3"))


(define all-system*
  (list gradualtalk gradualtalk typed-racket tpd strongscript actionscript mypy
        flow hack pyre pytype rtc strongtalk typescript typed-clojure typed-lua
        pyret thorn dart2 dart1 nom pycket reticulated safets))

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

;; -----------------------------------------------------------------------------

(module+ test
  (require rackunit)
  (void)
)
