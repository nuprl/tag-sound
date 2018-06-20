#lang gf-icfp-2018
@require["techreport.rkt" (only-in gtp-plot/plot *OVERHEAD-LABEL?*)]
@appendix-title{Performance vs. Number of Typed Modules}

@(define data* (map list TR-DATA* TAG-DATA*))
@(define data** (let loop ((data* data*))
                  (cond
                    [(null? data*)
                     '()]
                    [(null? (cdr data*))
                     (raise-user-error 'exact-runtime "odd number of datasets (not implemented, need to resize the figure for this)")]
                    [else
                     (cons (list (car data*) (cadr data*)) (loop (cddr data*)))])))
@(define total-figs (length data**))
@(define figure-label*
   (for/list ((i (in-range total-figs)))
     (format "fig:locally-defensive-linear-~a" (+ i 1))))

@(apply Figure-ref figure-label*) plot every running time in the dataset.
Each point represents one measurement; specifically, a point at position
 @${(X,Y)} reports one running time of @${Y} milliseconds for one configuration
 with @${X} ``typed units'' --- in this paper, one typed unit is one typed module.
There are @integer->word[NUM-ITERS] such points for each configuration.
To make these points easier to see, the @integer->word[NUM-ITERS] points
 for one configuration are evenly spaced along the @|x-axis| within a bucket
 (delimited by solid vertical lines).
The left-most point plots the running time of the first trial,
 the second-from-left point corresponds to the second trial, and so on.

The figures support three broad conclusions.
First, the orange points for @|TR_LD| are often lower
 (i.e., show better performance) than the points for @|TR_N|.
Second, the performance of @|TR_LD| tends to degrade linearly as the number
 of typed modules increases.
This slowdown tapers off at the right-most end because the implementation
 skips the codomain-check for calls to statically-typed identifiers.
Third, the performance of @|TR_N| has a steep umbrella shape.
The worst performance is in the middle, but improves significantly as the
 number of typed modules approaches the maximum.

@(parameterize ([OVERHEADS-WIDTH 650]
                [OVERHEADS-HEIGHT 700]
                [*OVERHEAD-LABEL?* #true]
                [FONT-SIZE 12]
                [NUM-COLUMNS 1])
   (for/list ((plot-info (in-list data**))
              (lbl (in-list figure-label*))
              (i (in-naturals 1)))
     (figure*
       lbl
       @elem{Running time of @|TR_N| configurations (@|tr-color-text| @|tr-color-sample|)
             and @|TR_LD| configurations (@|tag-color-text| @|tag-color-sample|), part @~a[i]/@~a[total-figs]}
       (exact-plot* plot-info))))

