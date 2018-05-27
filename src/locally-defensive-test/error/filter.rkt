#lang typed/racket/base #:locally-defensive

(module u racket/base
  (provide nats)
  (define nats '(1 2 three four)))

(require/typed 'u
  (nats (Listof Natural)))

(: myadd (-> Natural Natural))
(define (myadd n)
  (add1 n))

(filter myadd nats)
