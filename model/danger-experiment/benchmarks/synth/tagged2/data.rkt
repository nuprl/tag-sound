#lang typed/racket/base

(provide
  (struct-out Array)
  (struct-out Settable-Array)
  (struct-out Mutable-Array))

  (struct Array ([shape : (Option (Vectorof (Option Integer)))]
                   [size : (Option Integer)]
                   [strict? : (Option (Boxof (Option Boolean)))]
                   [strict! : (Option (-> (Option Void)))]
                   [unsafe-proc : (Option (-> (Vectorof (Option Integer)) (Option Float)))]))
  (struct Settable-Array Array ([set-proc : (Option ((Vectorof (Option Integer)) Float -> (Option Void)))]))
  (struct Mutable-Array Settable-Array ([data : (Option (Vectorof (Option Float)))]))

