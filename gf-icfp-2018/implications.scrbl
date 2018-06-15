#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Implications}

@Sections-ref{sec:design} and @secref{sec:evaluation} present the two critical aspects of the three
approaches to combining statically typed and dynamically typed code via a
twin pair of languages: (1) their semantics within a single framework and
(2) their performance characteristics relative to a single base language and
the same suite of benchmark programs.
Equipped with this objective
information, we can now explain the logical implications and the performance consequences of
choosing one of these three approaches. 

For the logical consequences, we proceed in a type-directed manner.
At the level of base types, there is no difference between the @|holong|
 embedding and the @|folong| one, but the @|eolong|
 embedding may give a different result due to a logical error (@section-ref{sub:base}).
After moving from base types to trees of base types, we can explain
 the truly essential difference between the @|holong| and @|folong| semantics:
 while the @|holong| embedding allows
 developers to reason compositionally about type annotations, users of
 the @|folong| variant must always consider the whole program (@section-ref{sub:first-order}).
This non-compositional behavior means that logical errors may go undetected in
 seemingly type-correct code.
Higher-order types are similarly afflicted by the non-compositional behavior of
 the @|folong| embedding (@section-ref{sub:ho}).
Lastly, the three approaches provide
 radically different support when it comes to boundary errors and debugging
 them (@section-ref{sub:err}).

For consequences with respect to performance, our work somewhat confirms
the conjectures of the literature that lowering the standards of
safety pays off---but only to some degree.
While the @|folong| embedding adds less overhead than @|holong| to a large portion of the mixed-typed
programs (@section-ref{sub:perf-mixed}),
readers must keep two caveats in mind.
For one, the @|folong| approach imposes a run-time checking overhead
 that is directly proportional to the number of types in the program.
Second, the @|holong| embedding may exploit the full soundness of type annotations.
As a result, programs with many type annotations tend to run faster under
 the @|holong| semantics than the @|folong| one (@section-ref{sub:perf-total}).


@section[#:tag "sub:base"]{For Base Types}

For a program that computes a value of base type, it can be tempting to think
 that dynamic typing (via @|eolong|) provides all the soundness that matters in practice.
After all, Ruby and Python throw a @tt{TypeError} if a program attempts to
 add an integer to a string.
Similarly, the @|eolong| embedding throws a tag error if an expression adds a
 number to a pair.

This claim is only true, however, if the static typing system is restricted
 to exactly match the host language's notion of dynamic typing.
Adding a @emph{logical} distinction between natural numbers and integers,
 as demonstrated in the type system of @figure-ref{fig:multi-preservation},
 can lead to silent failures at run-time when a negative integer flows into
 a context expecting a natural number.
If the numbers represent votes, for example@~cite[tfffgksst-snapl-2017],
 then the lack of run-time checking can change the outcome of an election.


@;@dbend[
@;  @warning{
@;    \wellM (\equotient{(\edyn{\tnat}{{-2}})}{(\edyn{\tnat}{{-2}})}) : \tnat \rrESstar (\equotient{{-2}}{{-2}}) \rrESstar 1
@;  }
@;]
@;@exact{\noindent}

Other host languages may allow more diverse kinds of silent failures.
JavaScript, for example, supports adding a number to a string, array, or object.
TypeScript programmers must keep this behavior in mind to protect their type-erased
 code against JavaScript.@note{@tt{io.ts} adds some protection to TypeScript: @url{https://lorefnon.tech/2018/03/25/typescript-and-validations-at-runtime-boundaries}}

@; https://twitter.com/jbandi/status/965005464638541825

Both the @|holong| embedding and the @|folong| embedding are sound for
 base types, e.g.,
 if @${v} is a value of type @${\tnat}, then @${v} is a natural number.
Informally, the two approaches performs the same check at a boundary of base type.


@section[#:tag "sub:first-order"]{For First-Order, Non-Base Types}

@figure["fig:silent-failure" @elem{Logical error using polar-form complex numbers}
        @reynolds-pict]

The practical difference between the @|holong| and @|folong| embeddings
 becomes clear in a mixed-typed program that deals with pairs.
The @|holong| embedding checks the contents of a pair; the @|folong|
 embedding only checks the constructor:@note{In this and similar examples,
  we write @${\wellM e : \tau \rrKSstar e'} to abbreviate:
  @${\wellM e : \tau \carrow e'' \mbox{ for some $e''$ and } e'' \rrKSstar e'}.}

@dbend[
  @safe{
    \wellM \edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \rrNSstar \boundaryerror
  }
  @warning{
    \wellM \edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}} : \tpair{\tnat}{\tnat} \rrKSstar \vpair{-2}{-2}
  }
]

@exact{\noindent}Extracting a value from an ill-typed pair might not detect the mismatch,
 depending on what type of value the context expects.
For example, a typed expression can safely extract a negative integer from a
 pair of natural numbers if the expression happens to expect an integer:

@dbend[
  @safe{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}})} : \tnat \rrKSstar \boundaryerror
  }
  @warning{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}})} : \tint \rrKSstar {-2}
  }
]

@exact{\noindent}Similarly, a dynamically-typed expression can extract anything
 from a type-annotated pair:

@dbend[
  @warning{
    \wellM \efst{(\esta{(\tpair{\tnat}{\tnat})}{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}})})} \rrKDstar -2
  }
]

@exact{\noindent}Put another way, a developer cannot assume
 that a value of type @${\tpair{\tau_0}{\tau_1}} contains components of type
 @${\tau_0} and type @${\tau_1} because type-constructor soundness is not compositional.

@;Run-time checks in typed code provide a shallow form of defense, but limited by the context

Reynolds classic paper on types and abstraction begins with a similar example 
 based on a distinction between real numbers and non-negative reals@~cite[r-ip-1983].
The story starts with two professors teaching two sections in complex variables:

 @nested[#:style 'inset @emph{
   In one section, Professor Descartes announced that a complex number was an ordered pair of
   reals [...] In the other section, Professor Bessel announced that a complex
   number was an ordered pair of reals the first of which was nonnegative [...]
 }]@;
@;
@Figure-ref{fig:silent-failure} adapts this example to a mixed-typed world.
The typed module on left defines addition for
 ``Bessel-style'' complex numbers; the function adds the components of the given
 numbers.
The dynamically-typed module on the right mistakenly calls the addition function
 on two ``Descartes-style'' numbers, one of which does not match the type for
 Bessel numbers.

Indeed, each of the three approaches to migratory typing behave differently on this program.
The @|holong| embedding correctly rejects the application of @tt{add_B} at the
 boundary between the two modules:

@dbend{
  @safe{
    \wellM \texttt{(add\_B d0 d1)} \ccNS \boundaryerror
  }
}

@exact{\noindent}The @|eolong| embedding does not detect the type error, and silently computes
 a well-typed, nonsensical result:

@dbend{
  @warning{
    \wellM \texttt{(add\_B d0 d1)} \rrESstar \texttt{(list 2 1)}
  }
}

@exact{\noindent}The @|folong| embedding @emph{either} computes a
 nonsensical result or raises a boundary error somewhere within the @tt{map} function:

@dbend{
  @warning|{
    \wellM \texttt{(add\_B d0 d1)} \rrKSstar
      \left\{\begin{array}{l l}
         \texttt{(list 2 1)} & \mbox{if \texttt{map} does not check the Bessel type}
      \\ \boundaryerror & \mbox{if \texttt{map} does check the type}
      \end{array}\right.
  }|
}

@exact{\noindent}it is impossible to predict the outcome without knowing the
 local type annotations within @tt{map}.


@section[#:tag "sub:ho"]{For Higher-Order Types}

One promising application of migratory typing is to layer a typed interface
 over an existing, dynamically-typed library of functions.
For the low effort of converting library documentation into a type specification,
 the library author is protected against latent bugs and the library's clients
 benefit from a machine-checked API.
@; See @~cite[wmwz-ecoop-2017] for motivation.

@Figure-ref{fig:db-app} demonstrates this use-case.
The module on the left represents a dynamically-typed library that
 manages a SQL database.
The module on the right represents a dynamically-typed web application;
 the application uses the database library to create and access user accounts.
In the middle, the type annotations formalize the interface between the database
 layer and the application.

With the @|holong| embedding, a developer can trust the type annotations.
The database module may assume well-typed arguments and the application
 is guaranteed well-typed results, despite the lack of static types within
 either module.

In contrast, the @|eolong| embedding completely ignores types at run-time
 and treats the middle module of @figure-ref{fig:db-app} as one large comment.
The types are just for documentation, and perhaps IDE tools.

The @|folong| embedding provides a limited compromise: for every
 value that flows from untyped to typed, the semantics checks that the
 value constructor matches the type constructor.
Concretely, there is one run-time check that ensures @racket[create] is bound to
 a function.

This single check does little to verify the correctness of the dynamically-typed
 code.
In terms of the model,
 retrofitting a type onto a dynamically-typed function @${f} does not
 enforce that @${f} respects its arguments:

@dbend[
  @warning{
    \begin{array}{l}
      f = \edyn{(\tarr{\tint}{\tint})}{(\vlam{x}{\efst{x}})}
      \\
      \wellM (\eapp{f}{2}) : \tint \rrKSstar \efst{2} \rrKSstar \tagerror
      \\[1ex]
    \end{array}
  }
]

@exact{\noindent}Conversely, there is no guarantee that untyped clients of a function @${g} abide by its interface:

@dbend[
  @warning{
    \begin{array}{l}
      g = \edyn{(\tarr{\tpair{\tint}{\tint}}{\tint})}{(\vlam{x}{\esnd{x}})}
      \\
      \wellM \eapp{(\esta{(\tarr{\tint}{\tint})}{g})}{{2}} \rrKDstar \esnd{2} \rrKDstar \tagerror
    \end{array}
  }
]

@exact{\noindent}Thus for all practical purposes, the benefits of writing a typed API in a
 @|folong| system are vanishingly small.

@figure["fig:db-app" @elem{Adding types between two untyped modules}
        db-app-pict]


@section[#:tag "sub:err"]{For Error Messages}

The examples above show that the @|holong| embedding detects errors
 earlier than the @|folong| and @|eolong| embeddings.
This temporal difference has implications for the quality of error messages
 that each embedding can produce.
@; A top-quality error message accurately blames one boundary for the fault.

The @|eolong| embedding detects a run-time type mismatch as late as possible, namely,
 just before an invalid operation.
Outside of printing a stack trace, it cannot do much to infer the source of the
 bad value.
When the source is off the stack, the @|eolong| embedding is impoverished:

@dbend[
  @warning{
    \esum{1}{(\edyn{\tint}{\vpair{2}{2}})} \rrESstar \esum{1}{\vpair{2}{2}} \rrESstar \tagerror
  }
]

The @|folong| embedding can detect a run-time type mismatch in two ways:
 at a type boundary or at a @${\vchk} expression.
In the latter case, @|folong| is no better off than
 @|eolong| for reporting the relevant value and type:

@dbend[
  @warning{
    \echk{\knat}{(\esnd{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{{-2}}{{-2}}})})} \rrKSstar \echk{\knat}{{-2}} \rrKSstar \boundaryerror
  }
]

@noindent[]@citet[vss-popl-2017] propose a strategy for improving the @|folong| error
 messages, but the strategy may double the running time of a program and reports
 a set of potentially-guilty boundaries rather than pinpointing the faulty one.

By contrast, an implementation of the @|holong| embedding can store debugging
 information in the monitor values it creates.
When such a monitor detects a type mismatch, the monitor can report the boundary term
 that originated the error even when the boundary is off the stack@~cite[tfffgksst-snapl-2017].
This information tells the developer exactly where to begin debugging:
 either the type annotation is wrong or the
 dynamically-typed code has a latent bug.


@section[#:tag "sub:perf-mixed"]{For the Performance of Mixed-Typed Programs}

Enforcing soundness in a mixed-typed program adds performance overhead.
As the graphs in @section-ref{sec:evaluation} demonstrate,
 this cost can be high (10x) in the @|folong| embedding and enormous
 (1000x) in the @|holong| embedding.

The @|folong| embedding incurs type-constructor checks at three places:
 type boundaries, applications of typed functions, and explicit @${\vchk} terms.
While each check adds a small cost,@note{In the model, checks have @${O(1)} cost.
  In the implementation, checks have near-constant cost @${O(n)} where
  @${n} is the number of types in the widest union type
  @${(\tau_0 \cup \ldots \cup \tau_{n-1})} in the program.}
 these costs accumulate.
Furthermore, the added code and branches may affect JIT compilation.

The @|holong| embedding incurs three significant kinds of costs.
First, there is the cost of checking a value at a boundary.
Second, there is an allocation cost when a higher-order value crosses a boundary.
Third, monitored values suffer an indirection cost; for example,
 a monitor guarding a dynamically-typed function must check every result computed
 by the function.

Each kind of cost may be arbitrarily large.
The (time) cost of checking an algebraic type depends on the size of the
 given value.
The (time and space) cost of allocation grows with the number
 of boundary-crossings, as does the (time) cost of indirection.
@; (@section-ref{sec:related-work:performance} reviews potential solutions)
In the following example, an untyped function crosses three boundaries and
 consequently accumulates three monitors:

@dbend[
  @warning{
    \begin{array}{l}
      \edyn{(\tarr{\tnat}{\tnat})}{(\esta{(\tarr{\tint}{\tint})}{(\edyn{(\tarr{\tint}{\tint})}{\vlam{x}{x}})})}
      \\ \rrNSstar \vmonfun{(\tarr{\tnat}{\tnat})}{(\vmonfun{(\tarr{\tint}{\tint})}{(\vmonfun{(\tarr{\tint}{\tint})}{\vlam{x}{x}})})}
      \\[0.4ex]
    \end{array}
  }
]

@noindent[]Furthermore, the indirection added by monitors may limit the effectiveness of
 a JIT compiler.


@section[#:tag "sub:perf-total"]{For the Performance of Fully-Typed Programs}

If a program has few dynamically-typed components, then the @|folong|
 embedding is likely to perform the worst of the three embeddings.
This poor performance comes about because all typed expressions unconditionally
 check their inputs.
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

@noindent[]As a rule-of-thumb, adding types seems to add a linear-time performance
 degredation@~cite[gm-pepm-2018 gf-tr-2018].

By contrast, the @|holong| embedding pays to enforce soundness only if static
 and dynamic components interact.
If there are few interactions, the program spends little time enforcing soundness.
Furthermore, a compiler may leverage the soundness of the @|holong| embedding
 to produce efficient code.
In many dynamically typed language, primitives check the
 type-tag of their arguments and dispatch to a low-level procedure.
Sound static types can eliminate the need to dispatch@~cite[stff-padl-2012],
 and thus the @|holong| embedding's performance can exceed that of the @|eolong| embedding (as shown in @figure-ref{fig:typed-speedup}).


