#lang at-exp slideshow

;; Slides for RacketCon mini-tutorial

(require
  pict
  slideshow/code
  racket/runtime-path)

;; =============================================================================

(define (do-show)
  (set-page-numbers-visible! #false)
  (parameterize ([current-main-font "Inconsolata" #;"Avenir" #;"Monaco" #;"Optima"]
                 [current-font-size 32]
                 [current-titlet string->title]
                 [*current-tech* #true])
    (sec:title)
    #;(sec:example)
    #;(sec:short-answer)
    #;(sec:contribution-outline)
    #;(sec:getting-started)
    #;(sec:install-source)
    #;(sec:edit-code) #;(sec:contribution-outline)
    #;(sec:render-documentation)
    #;(sec:run-tests)
    #;(sec:summary)
    #;(sec:extra)
    (void)))

;; -----------------------------------------------------------------------------

(define (tt str)
  (text str '(bold . modern) (- (current-font-size) 4)))

(define (url str)
  (hyperlinkize (tt str)))

(define (MD-URL)
  @url{https://tinyurl.com/racketeering101}
  @;@url{https://github.com/bennn/racket-lang-org/blob/pr-blog/blog/_src/posts/2017-09-27-tutorial-contributing-to-racket.md}
  )

(define (PR-URL)
  @url{https://github.com/racket/racket-lang-org/pull/58})

(define-runtime-path PWD ".")

;; *current-tech* : Parameterof Boolean
;; - #true => assume presenter has internet access
;; - #false => add slides / animations to simulate a live demo
(define *current-tech* (make-parameter #false))

(define (lo-tech?)
  (not (*current-tech*)))

;; Return "tech mode" for the presentation.
(define (get-current-tech)
  (for/or ([arg (in-vector (current-command-line-arguments))])
    (lo-tech-flag? arg)))

(define (lo-tech-flag? x)
  (and (member x '("lo-tech")) #true))

(define (bebas-bold str)
  (text str "Bebas Neue, Bold" 72))

(define-syntax-rule (mypara elem* ...)
  ;; TODO work on alignment
  (para #:align 'left elem* ...))

(define (string->title str)
  (text str (current-main-font) 44))

(define (question . elem*)
  (make-prompted "Q." elem*))

(define (answer . elem*)
  (make-prompted "A." elem*))

(define (make-prompted pre elem*)
  (parameterize ([current-font-size (+ 4 (current-font-size))])
    (apply para (para #:width 40 pre)
      elem*)))

;; -----------------------------------------------------------------------------
(define (sec:title)
  (slide
    @text["A Spectrum of Soundness and Performance" (current-main-font) (+ (current-font-size) 20)]
    @t{Ben Greenman, Northeastern University}
    @comment{
      ???
    })
  (void))

;(define (sec:short-answer)
;  (slide
;    @question{How to contribute to Racket?}
;    'next
;    @answer{Submit a pull request}
;    @comment{
;      Racket is on GitHub,
;      to suggest changes etc etc. just find the right repo and throw things at it
;    })
;  (when (lo-tech?)
;    (slide
;      #:title "Racket on Github"
;      @comment{})
;    (slide
;      #:title "Main Distribution Repos"
;      @comment{})
;    (slide
;      #:title "Edit on GitHub ..."
;      @comment{})
;    (slide
;      #:title "Fork ..."
;      @comment{})
;    (slide
;      #:title "Submit a Pull Request"
;      @comment{})
;    (slide
;      @question{How to contribute to Racket?}
;      @answer{Submit a pull request}
;      ; TODO check mark?
;      @comment{
;        Racket is on GitHub,
;        to suggest changes etc etc. just find the right repo and throw things at it
;      })
;    (void))
;  (void))
;
;;; TODO parameterize by number of times played, show checkmarks?
;;; TODO relly need check mark
;(define (sec:contribution-outline)
;  (slide
;    @question{How to .... ?}
;    @item{Install a package from source}
;    @item{Change the code}
;    @item{Render documentation}
;    @item{Run tests}
;    @comment{
;      kk for most contributions need more answers
;    })
;  (void))
;
;(define (sec:getting-started)
;  (slide
;    #:title "Step 0: Getting Started"
;    @item{Download Racket}
;    @subitem{@url{download.racket-lang.org}}
;    @item{Locate @tt{raco}}
;    @item{Choose a package to edit}
;    @subitem{Let @tt{<PKG> = pict}}
;    @comment{
;      yo lo
;      I have racket 6.10.1 installed, assuming you have the same thing too
;      need to find raco inside the package
;      ask if you have trouble today
;    })
;  (void))
;
;(define (sec:install-source)
;  (slide
;    #:title "Step 1: Install package from source"
;    @item{@tt{raco pkg update --catalog <URL> <PKG>}}
;    @item{@tt{raco pkg update --clone <PKG>}}
;    @subitem{@tt{<URL> =} @url{https://pkgs.racket-lang.org}}
;    @comment{
;      time to install = roughly 1 coffee break
;    })
;  (slide
;    #:title "Step 1.5: Connect source to GitHub"
;    @item{Fork @tt{<PKG>} on GitHub}
;    @item{@tt{git remote add fork <FORK-URL>}}
;    @item{@tt{git checkout -b <BRANCH-NAME>}}
;    @comment{
;      now you have the source, can start hacking,
;      but now is agood time to connect this clone to a fork of your own
;      on the github
;    })
;  (when (lo-tech?)
;    (parameterize ([current-font-size (- (current-font-size) 6)])
;      (slide
;        #:title "Update catalog"
;        @para{@tt{$ raco pkg update --catalog pkgs.racket-lang.org pict}}
;        @para{@tt{Inferred package scope: installation}}
;        @para{@tt{Resolving "pict" via https://pkgs.racket-lang.org}}
;        @para{@tt{Updating:}}
;        @para{@tt{....}}
;        @para{@tt{raco setup: --- parallel build using 4 jobs ---}}
;        @para{@tt{raco setup: 3 making: <collects>/racket}}
;        @para{@tt{C-c}}
;        @comment{})
;      (slide
;        #:title "Clone package"
;        @para{@tt{$ raco pkg update --clone pict}}
;        @para{@tt{Inferred package name from given `--clone' path}}
;        @para{@tt{....}}
;        @para{@tt{Convert the non-clone packages to clones, too?}}
;        @para{@tt{  [Y/n/a/c/?] y}}
;        @para{@tt{....}}
;        @para{@tt{raco setup: --- parallel build using 4 jobs ---}}
;        @para{@tt{....}}
;        @comment{}))
;    (slide
;      #:title "Go to GitHub"
;      @comment{})
;    (slide
;      #:title "Fork"
;      @comment{})
;    (slide
;      #:title "Connect fork and clone"
;      @comment{})
;    (void))
;  (void))
;
;(define (sec:edit-code)
;  (slide
;    #:title "Step 2: Find & edit the code"
;    @item{Search under @tt{<PKG>-lib}}
;    @item{In DrRacket: "Open Defining File"}
;    @item{@tt{raco fc <PKG>}}
;    @subitem{@tt{raco pkg install raco-find-collection}}
;    @comment{
;      time to edit the code,
;      general advice, what you want is probably under pict-lib
;      DrRacket and racket-mode can help with this
;      also raco fc
;    })
;  (when (lo-tech?)
;    (slide
;      #:title "Edit the code"
;      @comment{})
;    (slide
;      #:title "Commit changes"
;      @comment{})
;    (slide
;      #:title "Push to branch"
;      @comment{})
;    (slide
;      #:title "Submit PR"
;      @comment{})
;    (void))
;  (void))
;
;(define (sec:render-documentation)
;  (slide
;    #:title "Step 3: Edit the Documentation"
;    @item{To view: @tt{raco docs <PKG>}}
;    @item{To edit: @tt{<PKG>-doc/**/scribblings}}
;    @item{To build: @tt{raco setup <PKG>}}
;    @comment{
;      docs time,
;      fun fact you have a copy of the racket documentation
;
;      as motivating example I'm going to suggest an edit to the pict library,
;      see there's all these dingbas, but its missing something,
;      see I have this beautiful picture of my cat that I think would make a
;      great addition
;
;      I want `#lang racket (require pict/littlebear) meow` to give the picture
;    })
;  (when (lo-tech?)
;    (slide
;      #:title "Create the module"
;      @comment{})
;    (slide
;      #:title "Test usage"
;      @comment{})
;    (slide
;      #:title "Find the docs"
;      @comment{
;        now lets update the docs so everyone knows about this new power
;      })
;    (slide
;      #:title "Edit the docs"
;      @comment{
;      })
;    (slide
;      #:title "Render the docs"
;      @item{@tt{raco setup pict}}
;      @comment{
;      })
;    (void))
;  (void))
;
;(define (sec:run-tests)
;  (slide
;    #:title "Step 4: Run tests"
;    @item{@tt{raco test -c <PKG>}}
;    @comment{
;      exactly how to test depends on the package,
;      but usually raco test -c says if you broke something
;
;      many projects have a .travis.yml file you can check
;      --- but not all! --- thats something worth fixing
;    })
;  (when (lo-tech?)
;    (slide
;      #:title "Output of raco test"
;      @comment{})
;    (void))
;  (void))
;
;(define (sec:summary)
;  (slide
;    #:title "Reference"
;    @item{@tt{raco pkg update --catalog <URL> <PKG>}}
;    @subitem{@tt{<URL> =} @url{https://pkgs.racket-lang.org}}
;    @item{@tt{raco pkg update --clone <PKG>}}
;    @item{@tt{raco setup <PKG>}}
;    @item{@tt{raco test -c <PKG>}}
;    @para{See @MD-URL[]}
;    @comment{
;    })
;  (void))
;
;(define (sec:extra)
;  (slide
;    #:title "Install a new package"
;    @tt{raco pkg install --clone <PKG>}
;    @comment{
;    })
;  (slide
;    #:title "Test with \"standard\" settings"
;    @tt{raco test --drdr -c <PKG>}
;    @comment{
;    })
;  (slide
;    #:title "Build docs and index"
;    @tt{raco setup --doc-index <PKG>}
;    @comment{
;    })
;  (slide
;    #:title "Update a pull request"
;    @tt{git commit -m "new stuff"}
;    @tt{git push fork <MY-BRANCH>}
;    @comment{
;    })
;  (slide
;    #:title "Build Racket from source"
;    @item{@tt{git clone https://github.com/racket/racket}}
;    @item{@tt{cd racket}}
;    @item{@tt{make}}
;    @item{@tt{mkdir extra-pkgs}}
;    @comment{
;    })
;  (slide
;    #:title "What's in racket/racket ?"
;    @item{@tt{racket/class}}
;    @item{@tt{racket/contract}}
;    @item{@tt{racket/list}}
;    @item{@tt{racket/logging}}
;    @item{@tt{racket/match}}
;    @item{@tt{racket/system}}
;    @item{....}
;    @comment{
;    })
;  (slide
;    #:title "What's in the racket GitHub org.?"
;    @item{@tt{htdp}}
;    @item{@tt{math}}
;    @item{@tt{plot}}
;    @item{@tt{redex}}
;    @item{@tt{slideshow}}
;    @item{@tt{typed-racket}}
;    @item{....}
;    @comment{
;    })
;  (slide
;    #:title "What's on the package server?"
;    @item{@tt{adjutor}}
;    @item{@tt{dan-scheme}}
;    @item{@tt{debug-repl}}
;    @item{@tt{html-parsing}}
;    @item{@tt{frog}}
;    @item{@tt{pollen}}
;    @item{@tt{syntax-sloc}}
;    @item{....}
;    @comment{
;    })
;  (slide
;    #:title "Where's the source for the package server?"
;    @url{https://github.com/tonyg/racket-pkg-server}
;    @comment{
;    })
;  (slide
;    #:title "Where's the source for the Racket website?"
;    @url{https://github.com/racket/racket-lang-org}
;    @comment{
;    })
;  (void))

;; =============================================================================

(module+ main
  (do-show))
