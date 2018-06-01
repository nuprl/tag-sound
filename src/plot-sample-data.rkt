#lang racket/base

;; Usage:
;;
;;   racket plot-sample-data.rkt <DIR>
;;
;; where <DIR> is a directory with benchmark results (.out files)
;;  made by the `gtp-measure` tool.
;;
;; Plots the data in `<DIR>` and saves the result to a .png file.

(provide
  )

(require
  "../gf-icfp-2018/plot.rkt"
  file/glob
  gtp-util
  with-cache
  )

;; =============================================================================

(define benchmark-name*
  '(sieve fsm morsecode zombie jpeg suffixtree kcfa snake tetris synth))

;; ensure-rktd* : (-> directory-exists? void?)
;; Convert any .out files in the given directory to the .rktd format that the
;;  `gtp-plot` library expects.
(define (ensure-rktd* sample-data-dir)
  (for ([out (in-glob (build-path sample-data-dir "*.out"))])
    (ensure-rktd out)))

;; ensure-rktd : (-> file-exists? void?)
;; Convert the given .out file to .rktd file, unless a matching .rktd file
;;  already exists.
(define (ensure-rktd out)
  (define rktd (out->rktd out))
  (unless (file-exists? rktd)
    (with-output-to-file rktd
      (lambda ()
        (displayln "#(")
        (with-input-from-file out
          (lambda ()
            (for ((ln (in-lines)))
              (define v (string->value ln))
              (writeln (map time-string->cpu-time (cadr v))))))
        (displayln ")")
        (void)))))

;; out->rktd : (-> path-string? path-string?)
(define (out->rktd out)
  (define-values [base name _] (split-path out))
  (define new-name
    (format "~a-v6.10.1.rktd"
      (remove-gtp-measure-prefix (path->string (path-replace-extension name #"")))))
  (build-path base new-name))

;; remove-gtp-measure-prefix : (-> string? string?)
(define (remove-gtp-measure-prefix str)
  (define m (regexp-match #rx"^([0-9]+-)(.*)$" str))
  (if m
    (caddr m)
    str))

;; collect-data : (-> directory-exists? (listof (list/c path-string? path-string?)))
;; Find and return all pairs of TR_N / TR_LD data in the given directory.
(define (collect-data data-dir)
  (filter values
    (for/list ([bm-name (in-list benchmark-name*)])
      (define N-data (glob-first (build-path data-dir (format "~a-v6.10.1.rktd" bm-name))))
      (define LD-data (glob-first (build-path data-dir (format "tag_~a-v6.10.1.rktd" bm-name))))
      (cond
        [(and N-data LD-data)
         (list N-data LD-data)]
        [N-data
         (printf "warning: found '~a' data for TR_N but not TR_LD, skipping~n" bm-name)
         (printf " to plot skipped data, run `raco gtp-plot --overhead '~a'`~n" N-data)
         #false]
        [LD-data
         (printf "warning: found '~a' data for TR_LD but not TR_N, skipping~n" bm-name)
         (printf " to plot skipped data, run `raco gtp-plot --overhead '~a'`~n" LD-data)
         #false]
        [else
         #false]))))

;; glob-first : (-> path-string? (or/c #f path-string?))
;; Call `glob` on the given path-string, deal with ambiguity.
(define (glob-first pat)
  (define r* (glob pat))
  (cond
    [(null? r*)
     #f]
    [(null? (cdr r*))
     (car r*)]
    [else
     (raise-arguments-error 'glob-first "multiple files match pattern, please delete or rename some files" "pattern" pat "files" r*)]))

;; plot-directory : (-> directory-exists? pict?)
(define (plot-directory sample-data-dir)
  (void
    (ensure-rktd* sample-data-dir))
  (define N/LD-data
    (collect-data sample-data-dir))
  (parameterize ((*use-cache?* #false))
    (overhead-plot* N/LD-data)))

;; =============================================================================

(module+ main
  (require racket/cmdline)
  (define out-file (box "sample-data.png"))
  (command-line
    #:program "plot-sample-data"
    #:once-each
    [("-o" "--output") filename "Save plot to given file" (set-box! out-file filename)]
    #:args (sample-data-dir)
    (let ([dest-file (unbox out-file)])
      (and
        (save-pict dest-file (plot-directory sample-data-dir))
        (printf "Saved plot to '~a'~n" dest-file)))))

