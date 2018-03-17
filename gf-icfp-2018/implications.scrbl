#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma *extra-def-space*)]

@Sections-ref{sec:design} and @secref{sec:evaluation} present the two critical aspects of the three
approaches to combining statically typed and dynamically typed code via a
twin-pair of languages: their semantics within a single framework and
their performance characteristics relative to a single base language and
the same suite of benchmark programs.
Equipped with this objective
information, we can now explain the logical and performance consequences of
choosing one of these three approaches. 

For the logical consequences, we proceed in a type-directed manner.
As @section-ref{sub:base} explains, there is no difference between the natural
 embedding and the locally-defensive one for base types, but the erasure
 embedding may yield totally distinct (wrong) answers.
After moving from base types to trees over first-order types, we can explain
 the truly essential difference; while the natural embedding allows
 developers to reason compositionally about type annotations, users of
 the locally defensive variant must always consider the whole program (@section-ref{sub:first-order}).
For higher-order types, the non-compositional behavior means that logical
 errors may go undetected in seemingly type-correct code (@section-ref{sub:ho}).
As mentioned already, the three approaches provide
 radically different support when it comes to boundary errors and debugging
 them (@section-ref{sub:err}).

For consequences with respect to performance, our work somewhat confirms
the implicit conjectures of the literature that lowering the standards of
safety pays off---but only to some degree.
As @section-ref{sub:perf-mixed}
interprets the findings of the previous section, the locally-defensive
embedding is significantly more efficient when it comes to mixed-typed
programs.
By contrast, we remind readers in @section-ref{sub:perf-total} that
fully typed programs run safely and faster with the natural embedding
because the optimizer can take full advantage of the types, and the natural
embedding safely skips checking in this case.


@section[#:tag "sub:base"]{For Base Types}

For a program that computes a value of base type, it can be tempting to think
 that dynamic typing (via erasure) provides all the soundness that matters in practice.
After all, Ruby and Python throw a @tt{TypeError} if a program attempts to
 add an integer to a string.
Similarly, the erasure embedding throws a tag error if an expression adds a
 number to a pair.

This claim is only true, however, if the static typing system is restricted
 to match the domain checks that dynamic typing happens to enforce.
Adding a @emph{logical} distinction between natural numbers and integers,
 as demonstrated in the type system of @figure-ref{fig:multi-preservation},
 can lead to silent failures at runtime.
For example, if a negative number flows into a typed context
 expecting a natural number, the context may compute a well-typed result
 by dividing the ill-typed input by itself.@note{Reynolds classic paper on
  types and abstraction begins with a similar example, based on a distinction
  between real numbers and non-negative reals@~cite[r-ip-1983].}

@dbend[
  @warning{
    \wellM (\equotient{(\edyn{\tnat}{{-2}})}{(\edyn{\tnat}{{-2}})}) : \tnat \rrEEstar (\equotient{{-2}}{{-2}}) \rrEEstar 1
  }
]

@exact{\noindent}Other host languages may allow more extreme kinds of silent failures.
JavaScript, for example, supports adding a number to a string, array, or object.

Both the natural embedding and the locally-defensive embedding are sound for
 base types, in the sense that if @${v} is a value of type @${\tnat},
 then @${v} is a natural number.
More formally, their canonical forms lemmas coincide for base types.
In the appendix, we show that these embeddings define equivalent reduction
 sequences for any expression in which all type boundaries are of base
 type@~cite[gf-tr-2018].


@section[#:tag "sub:first-order"]{For First-Order, Non-Base Types}

The practical difference between the natural and locally-defensive embeddings
 becomes clear in a mixed-typed program that deals with pair values.
The natural embedding checks the contents of a pair; the locally-defensive
 embedding only checks the constructor.@note{In this and similar examples,
  we write @${\wellM e : \tau \rrKSstar e'} as shorthand for
  @${\wellM e : \tau \carrow e'' \wedge e'' \rrKSstar e'}.}

@dbend[
  @safe{
    \wellM \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \rrNSstar \boundaryerror
  }
  @warning{
    \wellM \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \rrKSstar \vpair{-2}{-2}
  }
]

@exact{\noindent}Extracting a value from an ill-typed pair may detect the mismatch,
 but the semantics depends on what type the context happens to expect.
Put another way, a developer cannot compositionally reason that a value of type
 @${\tpair{\tau_0}{\tau_1}} contains components of type @${\tau_0} and type @${\tau_1};
 only reasoning about the context can tell.

@dbend[
  @safe{
    \wellM \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}})} : \tnat \rrKSstar \boundaryerror
  }
  @warning{
    \wellM \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-2}})} : \tint \rrKSstar {-2}
  }
]


@section[#:tag "sub:ho"]{For Higher-Order Types}

One promising application of migratory typing is to layer a typed interface
 over an existing, dynamically-typed library of functions.
As a corollary of type soundness, the natural embedding checks that the library
 and the clients match the interface.
For the low effort of converting library documentation into a type specification,
 the library author is protected against latent bugs and the library's clients
 receive a machine-checked API.

The locally-defensive and erasure embeddings do not support this use-case;
 the erasure embedding ignores the types, and the locally-defensive embedding
 checks only that the exported value is a function.
Retrofitting a type onto a dynamically-typed function @${f} therefore does not
 enforce that @${f} respects its arguments.
Conversely, there is no guarantee that untyped clients of a function @${g} abide by its interface;

@dbend[
  @warning{
    \begin{array}{l}
      f = \edyn{\tarr{\tint}{\tint}}{(\vlam{x}{\efst{x}})}
      \\
      \wellM (\eapp{f}{2}) : \tint \rrKSstar \efst{2} \rrKSstar \tagerror
      \\[1ex]
    \end{array}
  }
  @warning{
    \begin{array}{l}
      g = \edyn{(\tarr{\tpair{\tint}{\tint}}{\tint})}{(\vlam{x}{\esnd{x}})}
      \\
      \wellM \eapp{(\esta{\tarr{\tint}{\tint}}{g})}{{2}} \rrKDstar \esnd{2} \rrKDstar \tagerror
    \end{array}
  }
]


@section[#:tag "sub:err"]{For Error Messages}

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

@dbend[
  @warning{
    \esum{1}{(\edyn{\tint}{\vpair{2}{2}})} \rrEEstar \esum{1}{\vpair{2}{2}} \rrEEstar \tagerror
  }
]

The locally-defensive embedding can detect a runtime type mismatch in two ways:
 at a type boundary or at a @${\vchk} expression.
In the latter case, the locally-defensive embedding is no better off than the
 erasure embedding.

@dbend[
  @warning{
    \echk{\knat}{(\esnd{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{{-2}}{{-2}}})})} \rrKSstar \echk{\knat}{{-2}} \rrKSstar \boundaryerror
  }
]

@noindent[]It is unclear how to trace the value that failed the check back to the type
 boundary where it originated.
@citet[vss-popl-2017] have explored a strategy for improving these error
 messages, but the strategy adds significant performance overhead and reports a
 set of potentially-guilty boundaries rather than pinpointing the faulty one.

By contrast, an implementation of the natural embedding can store debugging
 information in the monitor values it creates.
When such a monitor detects a type mismatch, it can identify the boundary term
 that originated the error, even when the boundary is off the stack@~cite[tfffgksst-snapl-2017].
This information tells the developer exactly where to begin debugging:
 either the boundary type is wrong or the
 dynamically-typed code has a latent bug.


@section[#:tag "sub:perf-mixed"]{For the Performance of Mixed-Typed Programs}

Enforcing soundness in a mixed-typed program adds performance overhead.
As the graphs in @section-ref{sec:evaluation} demonstrate for the benchmarks,
 this cost can be high in the locally-defensive embedding, and enormous in the
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
 a monitor guarding a dynamically-typed function must every result computed
 by the function.


@section[#:tag "sub:perf-total"]{For the Performance of Fully-Typed Programs}

If a program has few dynamically-typed components, then the locally-defensive
 embedding is likely to perform the worst of the three embeddings.
This poor performance comes about because all typed expressions unconditionally
 check each function application and pair projection; after all, a dynamically-typed
 program may later invoke a compiled, typed function.
For example, a function that adds both elements of a pair value must check
 that its input has integer-valued components.

@dbend[
  @warning{
    \begin{array}{l}
    \wellM \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\efst{x})}{(\esnd{x})}} : \tarr{\tpair{\tint}{\tint}}{\tint}
    \\ \carrow \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\echk{\tint}{(\efst{x})})}{(\echk{\tint}{(\esnd{x})})}}
    \\[0.4ex]
    \end{array}
  }
]

@noindent[]As a general rule, adding type annotations adds a linear-time performance
 degredation@~cite[gm-pepm-2018 gf-tr-2018].

By contrast, the natural embedding pays to enforce soundness only if static
 and dynamic components interact.
If there are few interactions, the program will spend little time enforcing soundness.
Furthermore, a compiler may leverage the soundness of the natural embedding
 to produce code that is more efficient than the erasure embedding.
In many dynamically typed language, primitives check the
 type-tag of their arguments and dispatch to a low-level procedure.
Sound static types can eliminate the need to dispatch@~cite[stff-padl-2012],
 and thus the natural embedding's performance can exceed that of the erasure embedding.


