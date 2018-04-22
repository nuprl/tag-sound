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
      As you all know, there are many choices in mixed-typed language design.
      In the beginning, need to decide the expressions and types in the language,
       and the granularity where types can be mixed.
      Second, need to decide whether to add a dynamic type, and if so need to a type
       precision relation.
      Third, need to define a core language --- possibly the same as the
       surface language --- and a translation from surface to core.
      Finally, need a semantics for the core language.

      None of these steps are entirely straightforward, though there is
       significant progress on ``gradualizing'' the typing system and generating
       a semantics .... I would say, AGT gives a specification and the gradualizer
       is closer to an efficient implementation.
      But that's part of why this is an exciting area.
      There's no standard textbook for mixed-typed languages, no G-TAPL; in
       some way we're all trying to figure out what chapters belong in a
       textbook called ``gradual types and programming languages''.

      Lately I have been interested in the relation between the static type
       system and the semantics in different languages; in particular, looking
       at "if a program is well typed, what soundness guarantee does the
       semantics preserve?"
      What are the implications for reasoning about programs and for performance.

      (Need to say 'migratory typing')

      To focus on these questions of soundness and performance, useful to step
       outside the strictly-speaking world of gradual typing and drop the
       dynamic type.
      So we just have to worry about what are the types in the language and
       what happens at runtime when an untyped value flows into a typed context.
      With this in mind, I'm going to present one language, one static type
       system, and three semantics.
      Each semantics will ? its own soundness and performance.

      Alright. A useful way to model this situation is by splitting the
       surface language into two parts:
       a dynamically-typed surface language e_D ::= x | e_D e_D | lam x e_D | ....
       and a statically-typed surface language e_S ::= ... lam x t e_S | ....
      The e_S language allows type annotations, so here is a bare-minimum
       grammar for types.
      Int is a base type, just to get things off the ground.
      Nat is another base type, interesting because of its relation to Int:
      - they're in a subtyping relation
      - adds a logical distinction to the types that isn't part of the "host language"
      - reflects the set-based reasoning that happens in e_D programs
      That gives us two parallel languages.
      To combine the languages, add so-called _boundary terms_ dyn and stat,
       to go from e_D to e_S and vice-versa.

      I've been calling "e_S" typed; we can make that precise by adding a
       static typing system.
      For the most part, a standard TAPL type system.
      The important non-standard part is the rule for a boundary term.
      To finish this rule, need a ``typing system'' for e_D terms to at least
       make sure that embedded e_S terms are well-typed; the judgment
       I've been using is one that also checks for free variables.
      Pretty sure that is optional, for what I want to study that is to follow,

      NAMELY, what is soundness for this pair of language?
      If e_S has type T and we have a semantics (and translation) what parts
       of T preserved?

      Today I'm going to present three approaches.
      All motivated by things that have proven useful in implementations
      --- thats just to say these soundnesses are not my idea; I'm bringing
          those ideas into a new common framework --- (needs work)

      Right, three approaches.
      These are based on three perspectives on the role of types.
      If you ask, "what is the meaning of types?"



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
