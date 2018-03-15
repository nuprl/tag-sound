#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma *extra-def-space*)]

@; TODO
@; - fill in TODO about what else is in the figure
@; - classify examples as "good" "bad" "maybe"
@;   with dangerous bends
@; - one point of GT is that need to build incrementally,
@;   but the errors are definitely not incremental
@; - erasure's simplicity is GREAT, easy to implement understand maintain,
@;   more time to spend on the IDE
@; - N / LD agree for base types

@; ML = static typing , N = natural embedding , E = erasure embedding , K = locally-defensive embedding
@; t = type or sizeof type , e = small number , d = small number
@;---
@; base-types t   | 1 |       1 | 0   |     1 |
@; first-order t  | 1 |       1 | 0   |   1/t |
@; higher-order t | 1 | t-e / t | 0   |     e |
@; errors         | 1 |     1-e | 0   |     e |
@; perf mixed     | 0 |       e | 1   |   1-e |
@; perf typed     | 1 |       1 | 1-d | 1/loc |

@; @subsection[#:tag "sec:higher-order-type:verdict"]{Summary}
@; The natural embedding is "semantically sound" inasense, LD and E are not

@; -----------------------------------------------------------------------------

@; TODO new intro ... all 3 lie on spectrum of soundness & spectrum of performnace . what means?

The natural, erasure, and locally-defensive embeddings provide three different
 notions of soundness, reproduced in @figure-ref{fig:X-soundness}.
At a high level, all three guarantee that reduction is fully-defined for
 well-typed programs.
The natural and locally-defensive embeddings additionally guarantee that typed
 expressions do not raise tag errors.
Only the natural embedding guarantees that well-typed expressions reduce to
 well-typed values.

When it comes to predicting the behavior of programs, the three notions
 of soundness have subtle consequences.
The examples on the right column of @figure-ref{fig:X-soundness} give an
 illustration; the natural embedding eagerly enforces boundary terms,
 the erasure embedding never enforces boundary terms,
 and the locally-defensive embedding enforces type constructors but nothing else.
The rest of this section compares the embeddings along a few different axes.


@figure["fig:X-soundness" "Soundness" @(parameterize ((*extra-def-space* "[1ex]")) @list[
    @twocolumn[
      @tr-theorem[#:key #false @elem{static @${\mathbf{N}}-soundness}]{
        If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
        @linebreak[]
        of the following holds:
        @itemlist[
          @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
          @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrND \tagerror} }
          @item{ @${e \rrNSstar \boundaryerror} }
          @item{ @${e} diverges}
        ] }

      @${\begin{array}{l}
        \edyn{\tint}{\vpair{1}{1}}
      \\\qquad \rrNSstar \boundaryerror
      \\[1.2ex]
        \edyn{\tpair{\tint}{\tint}}{\vpair{1}{\vlam{x}{x}}}
      \\\qquad \rrNSstar \boundaryerror
      \\[1.2ex]
        \edyn{(\tarr{\tint}{\tint})}{(\vlam{x}{\vpair{x}{x}})}
      \\\qquad \rrNSstar \vmonfun{(\tarr{\tint}{\tint})}{\vclosure}
      \end{array}}
    ]

    @twocolumn[
      @tr-theorem[#:key #false @elem{static @${\mathbf{E}}-soundness}]{
        If @${\wellM e : \tau} then @${\wellEE e} and one
        @linebreak[]
        of the following holds:
        @itemlist[
          @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
          @item{ @${e \rrEEstar \tagerror} }
          @item{ @${e \rrEEstar \boundaryerror} }
          @item{ @${e} diverges}
        ] }

      @${\begin{array}{l}
        \edyn{\tint}{\vpair{1}{1}}
      \\\qquad \rrEEstar \vpair{1}{1}
      \\[1.2ex]
        \edyn{\tpair{\tint}{\tint}}{\vpair{1}{\vlam{x}{x}}}
      \\\qquad \rrEEstar \vpair{1}{\vclosure}
      \\[1.2ex]
        \edyn{(\tarr{\tint}{\tint})}{(\vlam{x}{\vpair{x}{x}})}
      \\\qquad \rrEEstar \vclosure
      \end{array}}
    ]

    @twocolumn[
      @tr-theorem[#:key #false @elem{static @${\mathbf{K}}-soundness}]{
        If @${\wellM e : \tau} then 
        @${\wellM e : \tau \carrow e''}
        and @${\wellKE e'' : \tagof{\tau}}
        @linebreak[]
        and one of the following holds:
        @itemlist[
          @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
          @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
          @item{ @${e'' \rrKSstar \boundaryerror} }
          @item{ @${e''} diverges }
        ] }

      @${\begin{array}{l}
        \edyn{\tint}{\vpair{1}{1}}
      \\ \qquad \rrKSstar \boundaryerror
      \\[1.2ex]
        \edyn{\tpair{\tint}{\tint}}{\vpair{1}{\vlam{x}{x}}}
      \\\qquad \rrKSstar \vpair{1}{\vclosure}
      \\[1.2ex]
        \edyn{(\tarr{\tint}{\tint})}{(\vlam{x}{\vpair{x}{x}})}
      \\\qquad \rrKSstar \vclosure
      \end{array}}
    ]
])]

@section{For Base Types}

For a program that computes a value of base type, it can be tempting to think
 that dynamic typing provides all the soundness that matters in practice.
After all, Ruby and Python throw a @tt{TypeError} if a program attempts to
 add an integer to a string.
Similarly, the erasure embedding throws a tag error if an expression adds a
 number to a pair.
It appears that dynamic typing catches any mismatch between a value and a
 base type.

This claim is only true, however, if the static typing system is restricted
 to match the domain checks that dynamic typing happens to enforce.
Adding a @emph{logical} distinction between natural numbers and integers,
 as in the erasure embedding, can lead to silent failures at runtime.
For example, if a negative number flows into a typed context
 expecting a natural number, the context may compute a well-typed result
 by dividing the ill-typed input by itself.@note{Reynolds classic paper on
  types and abstraction begins with a similar example, based on a distinction
  between real numbers and non-negative reals@~cite[r-ip-1983].}

@dbend{
  \begin{array}{l}
  \wellM \equotient{(\edyn{\tnat}{{-2}})}{(\edyn{\tnat}{{-2}})} : \tnat \rrEEstar 0
  \end{array}
}

Both the natural embedding and the locally-defensive embedding are sound for
 base types, in the sense that if @${v} is a value of type @${\tnat} according
 to the embedding, then @${v} is a natural number.
Furthermore, these embeddings define equivalent reduction sequences for any
 expression in which all type boundaries are of base type@~cite[gf-tr-2018].


@subsection[#:tag "sec:base-type:verdict"]{Summary}

The natural and locally-defensive embeddings are dynamically sound for base
 types.
The erasure embedding is unsound for base types.


@section{For First-Order, Non-Base Types}

The practical difference between the natural and locally-defensive embeddings
 becomes clear in a mixed-typed program that deals with pair values.
The natural embedding checks the contents of a pair; the locally-defensive
 embedding only checks the constructor.

@dbend{
  \begin{array}{l}
    \wellM \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \rrNSstar \boundaryerror
    \\
    \wellM \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \carrow ; \rrKSstar \vpair{-2}{-2}
  \end{array}
}

Extracting a value from an ill-typed pair may detect the mismatch.
The semantics depends on what type the context happens to expect.

@dbend{
  \begin{array}{l}
    \wellM \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}})} : \tnat \carrow ; \rrKSstar \boundaryerror
    \\
    \wellM \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}})} : \tint \carrow ; \rrKSstar {-2}
  \end{array}
}

@; more to say?


@subsection[#:tag "sec:first-order-type:verdict"]{Summary}

The natural embedding is dynamically sound for first-order, non-base types.
The locally-defensive embedding only enforces the top-level type constructor,
 and the erasure embedding is unsound.


@section{For Higher-Order Types}

One promising application of migratory typing is to layer a typed interface
 over an existing, dynamically-typed library of functions.
As a corollary of type soundness, the natural embedding checks that the library
 and the clients match the interface.

The locally-defensive and erasure embeddings do not support this use-case.
Retrofitting a type onto a dynamically-typed function @${f} does not
 guarantee that @${f} respects its arguments.
Conversely, there is no guarantee that untyped clients of a function @${g} match its interface;
 the erasure embedding ignores the types, and the locally-defensive embedding
 checks only that the exported value is a function.

@dbend{
  \begin{array}{l}
  f = \vlam{x}{\efst{x}}
  \\
  \wellM \eapp{(\edyn{\tarr{\tint}{\tint}}{f})}{2} : \tint \carrow \rrKSstar \tagerror
  \\
  g = \edyn{(\tarr{\tpair{\tint}{\tint}}{\tint})}{(\vlam{x}{\efst{x}})}
  \\
  \wellM \eapp{(\esta{\tarr{\tint}{\tint}}{g})}{{2}} \carrow \rrKDstar \tagerror
  \end{array}
}

On a related note, it is possible to cast a function type to any other
 in the locally defensive embedding.
Programmers must take care not to write such code by accident.

@dbend{
  \begin{array}{l}
       \wellM \vlam{\tann{f}{\tarr{\tint}{\tint}}}{}
    \\ \qquad \edyn{(\tarr{\tnat}{\tnat})}{(\esta{(\tarr{\tint}{\tint})}{f})}
    \\ : \tarr{(\tarr{\tint}{\tint})}{(\tarr{\tnat}{\tnat})}
  \end{array}
}


@subsection[#:tag "sec:higher-order-type:verdict"]{Summary}

The natural embedding monitors higher-order values and reports the first
 evidence of a type mismatch.
The locally-defensive embedding spot-checks the interactions between a higher-order
 value and a typed context.
The erasure embedding is unsound for higher-order values.


@section{For Error Messages}

The examples above have shown that the natural embedding detects errors
 earlier than the locally-defensive and erasure embeddings.
This temporal difference has implications for the quality of error messages
 that each embedding can produce.
@; A top-quality error message accurately blames one boundary for the fault.

The erasure embedding detects a runtime type mismatch as late as possible, namely,
 just before invoking @${\delta} with an invalid argument.
Outside of printing a stack trace, it cannot do much to infer the source of the
 bad value.
When the source is off the stack, the erasure embedding is helpless.

@dbend{
  \begin{array}{l}
  \esum{1}{(\edyn{\tint}{\vpair{2}{2}})} \rrEEstar \esum{1}{\vpair{2}{2}} \rrEEstar \tagerror
  \end{array}
}

The locally-defensive embedding can detect a runtime type mismatch in two ways:
 at a type boundary or at a @${\vchk} expression.
In the latter case, the locally-defensive embedding is no better off than the
 erasure embedding.
It is unclear how to trace the value that failed the check back to the type
 boundary where it originated.
@citet[vss-popl-2017] have explored a strategy for improving these error
 messages, but the strategy reports a set of potentially-guilty boundaries
 rather than pinpointing the faulty one.

By contrast, an implementation of the natural embedding can store debugging
 information in the monitor values it creates.
When such a monitor detects a type mismatch, it can identify the boundary term
 that originated the error.
Typed Racket implements this strategy@~cite[tfffgksst-snapl-2017];
 when it detects a runtime type error, the programmer knows exactly which
 boundary violated its assertion: either the boundary type is wrong or the
 dynamically-typed code has a latent bug.

@;; too big
@;To illustrate the differences between the three embeddings, the following
@; example traces the execution of a dynamically-typed function that returns
@; an unexpected result to a typed context.
@;
@;@dbend{
@;  \esum{1}{(\eapp{(\edyn{(\tarr{\tint}{\tint})}{(\vlam{x}{\vpair{x}{x}})})}{2})}
@;    \rrNSstar \esum{1}{(\esta{\tint}{
@;}


@subsection[#:tag "sec:errors:verdict"]{Summary}

In the natural embedding, every error due to a dynamically-typed value in
 a statically typed context can be attributed to a faulty boundary between
 static and dynamic code.
The locally-defensive embedding has limited ability to detect and report
 such errors.
The erasure embedding has no ability to detect type boundary errors at runtime.


@section{For the Performance of Mixed-Typed Programs}

Enforcing soundness in a mixed-typed program adds performance overhead.
This cost can be high in the locally-defensive embedding, and enormous in the
 natural embedding.

The locally-defensive embedding incurs type-constructor checks at three places:
 type boundaries, applications of typed functions, and explicit @${\vchk} terms.
While each check adds a small cost,@note{In the model, checks have @${O(1)} cost.
  In the implementation, checks have basically-constant cost @${O(n)} where
  @${n} is the number of types in the widest union type
  @${(\tau_0 \cup \ldots \cup \tau_{n-1})} in the program.}
 these costs accumulate.
Furthermore, the added code and branches may affect JIT compilation.

The natural embedding incurs three significantly larger kinds of costs.
First, there is the cost of checking a value at a boundary.
Such checks may need to traverse the (first-order) value to compute its type.
Second, there is an allocation cost when a higher-order value crosses a boundary.
Third, monitored values suffer an indirection cost; for example,
 a monitor guarding a dynamically-typed function checks every result computed
 by the function.
This indirection may affect JIT inlining decisions.

@; because Typed Racket @bm{synth} spends a large amount of time
@; eagerly traversing data structures and monitoring their components.


@subsection[#:tag "sec:mixed-perf:verdict"]{Summary}

The cost of enforcing soundness in the natural embedding may slow a working
 program by two orders of magnitude.
The cost of the locally-defensive embedding is far lower, typically within
 one order of magnitude.
The erasure embedding adds no overhead.


@section{For the Performance of Fully-Typed Programs}

If a program has few dynamically-typed components, then the locally-defensive
 embedding is likely to perform the worst of the three embeddings.
This poor performance stems from the ahead-of-time completion function,
 which rewrites all typed expressions to unconditionally check each function
 application and pair projection.
For example, a function that adds both elements of a pair value must check
 that its input has integer-valued components.
These checks cost time and are unnecessary if the input value is typed.

@dbend{
  \begin{array}{l}
  \wellM \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\efst{x})}{(\esnd{x})}} : \tarr{\tpair{\tint}{\tint}}{\tint}
  \\ \carrow \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\echk{\tint}{(\efst{x})})}{(\echk{\tint}{(\esnd{x})})}}
  \\
  \end{array}
}

As a general rule, adding type annotations leads to a linear performance
 degredation in the locally-defensive embedding@~cite[gm-pepm-2018 gf-tr-2018].

By contrast, the natural embedding pays to enforce soundness only when static
 and dynamic components interact.
Furthermore, a compiler may leverage the soundness of the natural embedding
 to produce code that is more efficient than the erasure embedding.
In many dynamically typed language, primitives check the
 type-tag of their arguments and dispatch to a low-level procedure.
Sound static types can eliminate the need to dispatch@~cite[stff-padl-2012] 


@subsection[#:tag "sec:typed-perf:verdict"]{Summary}

The natural embedding adds no overhead to fully-typed programs and may enable
 type-based optimizations that improve performance.
The locally-defensive embedding suffers its worst-case overhead on fully-typed
 programs, as it always defends typed code against possibly-untyped inputs.
The erasure embedding adds no overhead to fully-typed programs.

