#lang at-exp slideshow

;; Slides for RacketCon mini-tutorial

(require
  pict
  ppict/2
  slideshow/code
  racket/runtime-path
  racket/draw)

;; =============================================================================

(define (do-show)
  (set-page-numbers-visible! #false)
  (set-margin! 0)
  (parameterize ([current-main-font "Inconsolata" #;"Avenir" #;"Monaco" #;"Optima"]
                 [current-font-size 32])
    (sec:title)
    (sec:intro)
    #;(sec:short-answer)
    #;(sec:contribution-outline)
    #;(sec:getting-started)
    #;(sec:install-source)
    #;(sec:edit-code) #;(sec:contribution-outline)
    #;(sec:render-documentation)
    #;(sec:run-tests)
    (sec:summary)
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

(define (title str)
  (text str (cons 'bold (current-main-font)) (+ 10 (current-font-size))))

(define (mytext str)
  (text str (current-main-font) (current-font-size)))

(define (question . elem*)
  (make-prompted "Q." elem*))

(define (answer . elem*)
  (make-prompted "A." elem*))

(define (make-prompted pre elem*)
  (parameterize ([current-font-size (+ 4 (current-font-size))])
    (apply para (para #:width 40 pre)
      elem*)))

(define (rectangle/gradient
                width height
                #:border-width [border-width 1]
                #:border-color [border-color "black"]
                #:color-1 [color-1 "white"]
                #:color-2 [color-2 "black"])
         (dc (λ (dc dx dy)
               (define old-brush
                 (send dc get-brush))
               (define old-pen
                 (send dc get-pen))
               (define gradient
                 (make-object
                  linear-gradient%
                  dx dy
                  dx (+ dy height)
                  `((0 ,(make-object color% color-1))
                    (1 ,(make-object color% color-2)))))
               (send dc set-brush
                 (new brush% [gradient gradient]))
               (send dc set-pen
                 (new pen% [width border-width]
                           [color border-color]))
               (send dc draw-rectangle dx dy width height)
               (send dc set-brush old-brush)
               (send dc set-pen old-pen))
             width height))

(define color-of-soundness "coral")
(define color-of-performance "skyblue")

;; -----------------------------------------------------------------------------

(define (sec:title)
  (pslide
    #:go (coord 1/2 1/2)
    (cc-superimpose
      (rectangle/gradient client-w 300 #:color-1 color-of-soundness #:color-2 color-of-performance)
      (vc-append 60
        @title{A Spectrum of Soundness and Performance}
        (vc-append 10
          @mytext{Ben Greenman}
          @mytext{Northeastern University})))
    @;{
      Hi everyone
    }))

(define (sec:intro)
  (pslide
    (mytext "noise")
    ;@comment{
    ;  As you all know, there are many choices in mixed-typed language design.
    ;  In the beginning, need to decide the expressions and types in the language,
    ;   and the granularity where types can be mixed.
    ;  Second, need to decide whether to add a dynamic type, and if so need to a type
    ;   precision relation.
    ;  Third, need to define a core language --- possibly the same as the
    ;   surface language --- and a translation from surface to core.
    ;  Finally, need a semantics for the core language.
    ;}
  ))

;      None of these steps are entirely straightforward, though there is
;       significant progress on ``gradualizing'' the typing system and generating
;       a semantics .... I would say, AGT gives a specification and the gradualizer
;       is closer to an efficient implementation.
;      But that's part of why this is an exciting area.
;      There's no standard textbook for mixed-typed languages, no G-TAPL; in
;       some way we're all trying to figure out what chapters belong in a
;       textbook called ``gradual types and programming languages''.
;
;      Lately I have been interested in the relation between the static type
;       system and the semantics in different languages; in particular, looking
;       at "if a program is well typed, what soundness guarantee does the
;       semantics preserve?"
;      What are the implications for reasoning about programs and for performance.
;
;      (Need to say 'migratory typing')
;
;      To focus on these questions of soundness and performance, useful to step
;       outside the strictly-speaking world of gradual typing and drop the
;       dynamic type.
;      So we just have to worry about what are the types in the language and
;       what happens at runtime when an untyped value flows into a typed context.
;      With this in mind, I'm going to present one language, one static type
;       system, and three semantics.
;      Each semantics will ? its own soundness and performance.
;
;      Alright. A useful way to model this situation is by splitting the
;       surface language into two parts:
;       a dynamically-typed surface language e_D ::= x | e_D e_D | lam x e_D | ....
;       and a statically-typed surface language e_S ::= ... lam x t e_S | ....
;      The e_S language allows type annotations, so here is a bare-minimum
;       grammar for types.
;      Int is a base type, just to get things off the ground.
;      Nat is another base type, interesting because of its relation to Int:
;      - they're in a subtyping relation
;      - adds a logical distinction to the types that isn't part of the "host language"
;      - reflects the set-based reasoning that happens in e_D programs
;      That gives us two parallel languages.
;      To combine the languages, add so-called _boundary terms_ dyn and stat,
;       to go from e_D to e_S and vice-versa.
;
;      I've been calling "e_S" typed; we can make that precise by adding a
;       static typing system.
;      For the most part, a standard TAPL type system.
;      The important non-standard part is the rule for a boundary term.
;      To finish this rule, need a ``typing system'' for e_D terms to at least
;       make sure that embedded e_S terms are well-typed; the judgment
;       I've been using is one that also checks for free variables.
;      Pretty sure that is optional, for what I want to study that is to follow,
;
;      NAMELY, what is soundness for this pair of language?
;      If e_S has type T and we have a semantics (and translation) what parts
;       of T preserved?
;
;      Today I'm going to present three approaches.
;      All motivated by things that have proven useful in implementations
;      --- thats just to say these soundnesses are not my idea; I'm bringing
;          those ideas into a new common framework --- (needs work)
;
;      Right, three approaches.
;      These are based on three perspectives on the role of types.
;      If you ask, "what is the meaning of types?"
;      - types are for enforcing levels of abstraction
;      - types are for static analysis
;      - types prevent undefined behavior (Milner: going wrong)
;      Thats the high-level intuition.
;      On a more technical level, the three approaches interpret boundary terms
;       in different ways
;
;      ONE: guarantee that if a value flow in from untyped code (dyn T v)
;       then the result has type T.
;      For base types this is easy to do, check that value is an Int or Nat.
;      For inductive types (rather, finitely constructed structures),
;       a full check implies checking the values shape and recursively checking
;       its components.
;      For coinductive types, we're a little stuck because 
;       You generally can't take a run-time representation of a function and
;       be sure that it always computes well-typed outputs.
;      --- use Robby's function-machine notation ---
;      So instead decompose and re-apply the boundary.
;
;      Notice there are two boundaries now, on the input and output of the
;       function.
;      So far we've been talking about the output; also need to talk about the
;       input to prevent typed functions from receiving arguments outside their
;       domain.
;      The reverse strategy is simpler: allow base types, recursively protect
;       inductive types, and monitor coinductive types.
;
;      Now that we have the new monitor values, need types and semantics for
;       these in the core language.
;      Here is a straightforward implementation.
;      Has some obvious inefficiencies ... allocation, indirection, and
;       unbounded space , also the cost of checking that we mentioned before
;       ... but now you get the idea.
;
;      (All on one slide) call this the natural embedding, because thats the
;       name Matthews and Findler used for a similar model that combined ML
;       and Scheme.
;
;       A few slides ago we said the important property of this embedding is
;        that untyped values flowing into typed have the correct type.
;       Based on this property, we can prove the following soundness results:
;       - if e:T then either ....
;       - if e then either .... w TagError
;       That concludes the first strategy
;
;       TWO: a second approach to boundaries is to let any kind of value
;        pass between typed and untyped code.
;       Based on the "static only" idea.
;       Whether the boundary says Int Nat pair or function, just let the value
;        through, and vice-versa for `stat` boundaries.
;       This has **zero** run-time cost and a simple semantics, there are no
;        new kinds of values, so no need for new rules.
;
;       But the guarantee is obviously weaker.
;       If (dyn T v) reduces to v' then the only sure thing is that v is
;        a well-formed value.
;       So when it comes to soundness for the pair of languages, we're down to
;        the lowest common-denominator.
;
;       In constrast to the natural embedding, call this the erasure embedding.
;
;       (summary slide, mark off 1 and 2 ?)
;
;       THREE: third approach, based on the idea that types are to prevent
;       undefined behavior.
;       First, we define undefined behavior as applying a non-function or
;        giving a primitive operation a value outside its domain.
;       In addition to the classic "* can only be applied to numbers", add a
;        logical distinction that says "* can only be applied to things matching
;        its static type".
;       So `((lambda (x : Nat) (* x x) : Nat) -1)` is going to get stuck because
;        `*` needs two natural numbers to return a natural number.
;       All these 'undefineds' are based on basic properties of values ---
;        which correspond to type constructors --- so
;        to a first approximation, can define the semantics of boundaries as
;        checking the first-order properties.
;       For integers and naturals, check the value.
;       For pair types, check the value is a pair.
;       For function types check the value is a closure.
;
;       This definition provides an interesting guarantee: if (dyn T v) = v'
;        then v' has the same type constructor as T ... more formally if we
;        define a map from types to constructors and a judgment that checks
;        whether a value matches a constructor, then we know v matches (floor T).
;       Also interesting, the boundary has unit-cost.
;       No matter what type we are expecting, it suffices to do one constructor
;        check.
;       No recursion, no allocation, no new values, no indirection.
;
;       However we can't state an interesting soundness theorem yet,
;        because although `(+ 2 HOLE)` cannot go wrong,
;        terms like `(+ 2 (fst HOLE))` can go wrong ... for example
;        `E[(dyn NatxNat ((0,1),(2,3)))]`
;
;       (actually step through the evaluation)
;
;       Similarly, terms like `(+ 2 (HOLE 2))` can go wrong for untyped functions,
;        e.g. `E[(dyn Nat->Nat (lambda (x) -9))]`
;
;       (step through again)
;
;       So we need to do something about inductive and coinductive types.
;       But we want to keep this semantics for the boundary terms --- it looks
;        good for performance.
;       What we can do instead is change the core language to look out for
;        problematic contexts like `(fst HOLE)` and `(HOLE e)` ... contexts
;        that extract 
;       In general these are elimination forms, and the property we want is
;        the same as for boundary terms; namely if the elimination form has
;        type T and reduces to a value, the value has the same constructor.
;
;       Mission accomplished by adding `(check K e)` to core language and
;        a translation that wraps typed calls of `(fst e)` and `(e e)` with a
;        check based on their static type.
;       That handles 2/4 the other two are `snd`, which is easy, and function
;        application, e.g. `((stat T->T' (lambda x:T e)) e')`
;       Fix by checking the argument of a typed function every time its applied;
;        this was can prove substitution `e[x <- v]` preserves the property.
;
;       This strategy is very much inspired by Vitousek's _transient_ semantics,
;        presented at an earlier one of these meetings.
;       We call it by a different name though, the **locally-defensive embedding**
;        as an effort to tease apart the three novel ideas in transient
;        - only check constructors
;        - forget previous types (migth know from M. Greenberg)
;        - static add defensive checks based on local type annotations
;       (Lunch would be a good time to argue about the name)
;
;       Now we can prove an interesting soundness that sits between the type-sound
;        and type-agnostic soundness for the first two strategies.
;       - if e:T then e~>e' and ... v:K
;       - if e then e~>e' and ...
;
;       Does everyone believe its possible to prove this theorem?
;         if not ... maybe helps to say we have 2 type systems, the unchanged
;          static and a dynamic one, and now .... \vdash (e e) : T and \vdash e e : Any
;
;       You may find this soundness upsetting.
;       Well for one it is sound but its non-compositional.
;       Suppose you have a pair value imported from dynamically-typed code,
;        `(dyn IntxInt v)`
;        might expect that every value extracted from `v` is an `Int`, but
;        that is only true **in the scope of the type annotation**.
;       If that same value flows out and in, it can change types:
;        `(dyn NatxNat (stat IntxInt (dyn IntxInt v)))`
;       Makes it much more difficult to reason about what is happening, in general.
;       In specific programs with lots of type annotations, maybe less of a problem.
;
;       At this point we've seen three strategies: check types, check constructors,
;        check nothing, and seen three soundness theorems.
;       Clearly types stronger than constructors stronger than nothing.
;
;       We also have an idea about the relative performance of the three,
;        seems typed will be significantly slower; unclear how slow constructored
;        will be.
;       Of course now that we have three "apples to apples" models, these serve
;        as a roadmap for three "apples to apples" implementations.
;
;       We forked Typed Racket and changed its semantics to enforce type constructor
;        soundness.
;       For the most part this was about cutting things, but two tasks deserve comment:
;       - rewriting type-checked terms with locally-defensive checks
;       - picking the constructor for other types
;
;       This gives three implementations
;       - typed racket, natural embedding
;       - racket, erasure embedding
;       - locally-defensive racket for the LD embedding
;
;       0. empty graphs, number of configurations
;          now you know there are 9 benchmarks, I can tell you they're all
;           functional programs, and you can basically see the number of modules in each
;          hey these look empty but they all report the performance of erasure,
;           relative to itself --- all that white space
;
;       1. blue line shows overhead of type soundness as implemented in Typed
;          Racket.
;          The x-axis is overhead, the y-axis is % of configurations that meet
;           this overhead
;          in FSM for example, half the configurations have at most 2x overhead
;           and the other half is off the charts
;          Shaded because this is a cumulative distribution function
;
;       2. lets add locally-defensive racket ... the orange line is overhead
;          of constructor soundness as implemented by our prototype
;          In many cases its better, FSM for sure is an improvement.
;
;          (pause to let them read)
;
;          Some cases are worse though, can see this by looking at where the
;          fully-typed configuration falls on the graphs (maybe graph by hand?)
;
;          Happens because constructor-sound does its rewriting pass on all
;           typed code.
;          Type-sound, on the other hand, adds overhead on demand when values
;           cross the boundary.
;          So that pays off in nearly-typed configurations, but usually the
;           boundaries outweight the optimizations
;
;       Any questions? This is all I'm planning to say about performance.
;
;       Moving on we've talked about soundness and we've seen an example of
;        performance.
;       We can also do apples-to-apples metatheory using the models.
;
;       First result, for typed expressions that do not contain any boundary
;        terms, all three approaches satisfy a strong "soundness for a single
;        language" theorem.
;       (straightforward, proves that pair-of-languages is harder?)
;
;       Second result, for program where only boundaries are of base type,
;        then N and LD are equivalent.
;       Not the same, because LD will perform checks in the typed code,
;        but they both check the same properties at a boundary.
;       (More precisely, follows from the same canonical forms lemma for base types)
;       "Third", LD and E are not equivalent for the same programs.
;       This is because we have a type for natural numbers --- more generally
;        a logical type that isn't enforced by the runtime.
;       Example (our favorite):
;        `(lambda x:Nat (* x x)) : Nat` applied to `(dyn Nat -2)`,
;        get error in LD and positive 4 in E.
;       Funny case where 2 wrongs make a right.
;
;       Final thing I want to mention, the strategies are not equal when it comes
;        to detecting a mismatch between a static type and an untyped value.
;       The natural embedding detects a mismatch as early as possible,
;        either by traversing a structured value `(dyn NatxNat (1, -2))`
;        or by monitoring a higher-order value.
;       The erasure embedding does not detect mismatches.
;       The locally-defensive embedding detects a mismatch as late as possible,
;        just before the program commits a type error.
;       Makes it much harder to trace the source of the type error back to
;        the original boundary term --- worth remarking that Vitousek etal
;        have a work-around for this, disclaimer it reports a set of boundary
;        terms and factors everything through a global space-unbounded blame heap.
;
;
;    })
;  (void))

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

(define (sec:summary)
  (define x-min 0.1)
  (define x-max 0.9)
  (define y-min 0.6)
  (define y-max 0.2)
  (pslide
    #:layout 'full-center
    #:go (coord x-min y-min) (tag-pict (blank 0 0) 'origin)
    #:go (coord x-min y-max) (tag-pict (blank 0 0) 'top-left)
    #:go (coord (+ x-min 0.1) y-max)
    (text "Natural")
    #:go (coord (+ x-min 0.1 (/ (- x-max x-min) 2)) (+ y-max (/ (- y-min y-max) 2)))
    (text "Locally-Defensive")
    #:go (coord x-max y-min) (tag-pict (blank 0 0) 'bot-right)
    #:go (coord (- x-max 0.1) y-min)
    (text "Erasure")
    #:next
    #:set (let ([p ppict-do-state])
            (pin-arrow-line 10 p (find-tag p 'origin) lb-find (find-tag p 'top-left) lt-find))
    #:set (let ([p ppict-do-state])
            (pin-arrow-line 10 p (find-tag p 'origin) lb-find (find-tag p 'bot-right) rb-find))
    ;; TODO add grid?
    #:next
    #:go (at-find-pict 'origin cc-find 'cc)
    (rectangle 200 100)
    )
    ;@comment{
    ;  In summary:
    ;  - there are at least three interesting notions of soundness for a pair
    ;    of languages
    ;  - the three notions explore a spectrum of soundness and performance for
    ;    the pair of languages (labeled here as "proofs" and performance)
    ;  - third, unexplored dimension is what programmers think of these
    ;    choices ... erasure for javascript is doing extremely well,
    ;    natural embedding gets sympathy but not so much support when its adding
    ;    overhead, and Locally-defensive we just don't know. Might be worst or
    ;    best of both worlds; Pyret and Dart are using it tho.
    ;  The end.
    ;}
  (void))

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
