#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Implications}

@Sections-ref{sec:design} and @secref{sec:evaluation} present the two critical aspects of the three
approaches to combining statically typed and dynamically typed code via a
twin pair of languages: (1) their semantics within a single framework and
(2) their performance characteristics relative to a single base language on
the same suite of benchmark programs.
Equipped with this objective
information, we can now explain the logical implications and the performance consequences of
choosing one of these three approaches. 

For the logical consequences, we proceed in a type-directed manner.
At the level of base types, there is no difference between the @|holong|
 embedding and the @|folong| one, but the @|eolong|
 embedding may give a different result due to a violation of the types (@section-ref{sub:base}).
After moving from base types to trees of base types, we can explain
 the truly essential difference between the @|holong| and @|folong| semantics:
 while the @|holong| embedding allows
 developers to reason compositionally about type annotations, users of
 the @|folong| variant must always consider the whole program (@section-ref{sub:first-order}).
This non-compositional behavior means that a violation of the type annotations
 may go undetected in seemingly type-correct code.
Higher-order types are similarly afflicted by the non-compositional behavior of
 the @|folong| embedding (@section-ref{sub:ho}).
Lastly, the three approaches provide
 radically different support when it comes to boundary errors and debugging
 them (@section-ref{sub:err}).

For consequences with respect to performance, our work somewhat confirms
the conjectures of the literature that lowering the standards of
safety pays off---but only to some degree.
While the @|folong| embedding adds less overhead than the @|holong| embedding to a large portion of the mixed-typed
programs (@section-ref{sub:perf-mixed}),
readers must keep two caveats in mind.
For one, the @|folong| approach imposes a run-time checking overhead
 that is directly proportional to the number of types in the program.
Second, the @|holong| approach may exploit the full soundness of type annotations.
As a result, programs with many type annotations tend to run faster under
 the @|holong| semantics than the @|folong| one (@section-ref{sub:perf-total}).


@section[#:tag "sub:base"]{For Base Types}

For a program that computes a value of base type, it can be tempting to think
 that dynamic typing (via @|eolong|) provides all the soundness that matters in practice.
After all, Ruby and Python throw a @tt{TypeError} if a program attempts to
 add an integer to a string.
Similarly, the @|eolong| embedding throws a @${\tagerror} if an expression adds a
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
 code against JavaScript.@note{The @tt{io.ts} library adds run-time validation to TypeScript:@linebreak[]
  @exact{\indent}@hyperlink["https://lorefnon.tech/2018/03/25/typescript-and-validations-at-runtime-boundaries"]{@tt{lorefnon.tech/2018/03/25/typescript-and-validations-at-runtime-boundaries}}}

@; pydantic for python : https://pydantic-docs.helpmanual.io/
@; also, PEP for variable annotations : https://www.python.org/dev/peps/pep-0526/
@; https://twitter.com/jbandi/status/965005464638541825
@; more python : https://github.com/Instagram/MonkeyType
@; many of the python links are from : https://www.bernat.tech/the-state-of-type-hints-in-python/

Both the @|holong| embedding and the @|folong| embedding are sound for
 base types, e.g.,
 if @${v} is a value of type @${\tnat}, then @${v} is a natural number.
Informally, the two approaches perform the same check at a boundary of base type.


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
For example, a typed context can safely extract a negative integer from a
 pair of natural numbers if the context happens to expect an integer:

@dbend[
  @safe{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}})} : \tnat \rrKSstar \boundaryerror
  }
  @warning{
    \wellM \efst{(\edyn{(\tpair{\tnat}{\tnat})}{\vpair{-2}{-2}})} : \arraycell{\tint}{\tnat} \rrKSstar {-2}
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
 based on a distinction between real numbers and non-negative reals@~cite[r-ip-1983]:
@; The story starts with two professors teaching two sections in complex variables:

 @nested[#:style 'inset @emph{
   In one section, Professor Descartes announced that a complex number was an ordered pair of
   reals [...] In the other section, Professor Bessel announced that a complex
   number was an ordered pair of reals the first of which was nonnegative [...]
 }]@;
@;
@Figure-ref{fig:silent-failure} adapts this example to a mixed-typed world.
The typed module on left defines addition for
 ``Bessel-style'' complex numbers; the function adds the components of the given
 pairs.
The dynamically-typed module on the right mistakenly calls the addition function
 on two ``Descartes-style'' numbers, one of which does not match the type for
 Bessel numbers.

Indeed, each of the three approaches to migratory typing behaves differently on this program.
The @|holong| embedding correctly rejects the application of @tt{add-B} at the
 boundary:

@dbend{
  @safe{
    \wellM \texttt{(add-B d0 d1)} \ccNS \boundaryerror
  }
}

@exact{\noindent}The @|eolong| embedding silently computes a well-typed, nonsensical result:

@dbend{
  @warning{
    \wellM \texttt{(add-B d0 d1)} \rrESstar \texttt{(list 2 1)}
  }
}

@exact{\noindent}The @|folong| embedding @emph{either} computes a
 nonsensical result or raises a boundary error somewhere within the @tt{map} function:

@dbend{
  @warning|{
    \wellM \texttt{(add-B d0 d1)} \rrKSstar
      \left\{\begin{array}{l l}
         \texttt{(list 2 1)} & \mbox{if \texttt{map} does not check the Bessel type}
      \\ \boundaryerror & \mbox{if \texttt{map} does check the type}
      \end{array}\right.
  }|
}

@exact{\noindent}It is impossible to predict the outcome without knowing the
 local type annotations within @tt{map}.


@section[#:tag "sub:ho"]{For Higher-Order Types}

@figure["fig:db-app" @elem{Adding types between two untyped modules}
        db-app-pict]

One promising application of migratory typing is to layer a typed interface
 over an existing, dynamically-typed library of functions.
For the low effort of converting library documentation into a type specification,
 the library's author and clients benefit from a machine-checked API.
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
The types are just for documentation and the IDE.

The @|folong| embedding provides a limited compromise: for every
 value that flows from untyped to typed, the implementation checks that the
 value constructor matches the type constructor.
Concretely, there is one run-time check that ensures @racket[create] is bound to
 a function.

This single check does little to verify the correctness of the dynamically-typed
 code.
In terms of the model,
 retrofitting a ``@|folong|'' type onto a higher-order function @${f} does not
 enforce that @${f} respects its arguments:

@dbend[
  @warning{
    \begin{array}{l}
      f = (\vlam{x}{\eapp{x}{\vpair{1}{1}}})
      \\
      h = \edyn{(\tarr{\tnat}{\tnat})}{(\vlam{y}{\esum{y}{y}})}
      \\
      \wellM \eapp{(\edyn{(\tarr{(\tarr{\tnat}{\tnat})}{\tnat})}{f})}{h} : \tnat \rrKSstar
      \eapp{f}{h} \rrKSstar \eapp{h}{\vpair{1}{1}} \rrKSstar \tagerror
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


@section[#:tag "sub:err"]{For Error Messages}

@figure["fig:list-error" @elem{Type-mismatch between a library function and client, adapted from @citet[vksb-dls-2014].}
        list-pict]

Errors matter.
Indeed @citet[vksb-dls-2014] claim that improved error messages are ``one of
 the primary benefits'' of adding types to a dynamically-typed language.
To illustrate, they describe a program similar to @figure-ref{fig:list-error}
 in which an untyped module sends a list of strings to a typed function that
 expects a list of numbers:

 @nested[#:style 'inset @emph{
   if the library authors make use of gradual typing [...] then the error can
   be localized and caught before the call to @tt{moment} [...] the runtime
   error points to the call to @tt{moment}
 }]

@noindent[]This claim assumes that the gradual typing system enforces types.
The @|holong| embedding is one such approach; it catches the error before the
 call to @tt{moment}:

@dbend[
  @safe{
    \wellM \texttt{(moment lst)} \rrNDstar \texttt{(moment ($\vfromdynN$(Listof(Float), lst))} \rrNDstar \boundaryerror
  }
]

The @|eolong| embedding performs the call to @tt{moment} just like a dynamically-typed language.
If the numeric operations check their inputs, the execution ends in a tag error.
If the primitives are un-checked, however, then the call may compute a nonsensical result:

@dbend[
  @warning|{
    \wellM \texttt{(moment lst)} \rrEDstar
      \left\{\begin{array}{l l}
         \tagerror & \mbox{if \texttt{mean} or \texttt{-} check for strings}
      \\ -1        & \mbox{if the primitives are unchecked}
      \end{array}\right.
  }|
]

The @|folong| embedding confirms that @tt{lst} is a list, and then proceeds
 with the call.
Since the body of @tt{moment} never directly extracts a float from the list,
 it is impossible to predict what happens during the call.
For example, @tt{mean} can raise a boundary error, raise a tag error, or
 silently compute a sum of string pointers.
In the latter cases, the client cannot be sure whether
 the error is their own fault or due to a bug in the library:

@dbend[
  @warning|{
    \wellM \texttt{(moment lst)} \rrKDstar
      \left\{\begin{array}{l l}
         \boundaryerror & \mbox{if \texttt{mean}, \texttt{-}, or \texttt{map} are typed}
      \\ \tagerror & \mbox{if \texttt{mean} or \texttt{-} check for strings}
      \\ -1        & \mbox{if the primitives are unchecked}
      \end{array}\right.
  }|
]

@noindent[]@citet[vss-popl-2017] propose a strategy that points the @|folong|
 error message to the call to @tt{moment}, but the strategy may double the
 running time of a program and reports a set of potentially-guilty boundaries
 rather than pinpointing the faulty one.

By contrast, the @|holong| embedding can identify the first violation of the
 types --- even for higher-order interactions --- by storing debugging information
 in monitor values@~cite[tfffgksst-snapl-2017].
Equipped with the relevant boundary term, the developer knows exactly where to
 begin debugging: either the type annotation is wrong or the dynamically-typed
 code does not match the type.


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
The added code and branches may affect JIT compilation.

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

@noindent[]Finally, the indirection added by monitors may limit the effectiveness of
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

@noindent[]As a rule-of-thumb, adding types imposes (at least) a linear-time performance
 degredation@~cite[gm-pepm-2018 gf-tr-2018].

The @|holong| embedding pays to enforce soundness only if static
 and dynamic components interact.
If there are few interactions, the program spends little time enforcing soundness.

Furthermore, the soundness of the @|holong| embedding means that a compiler can
 apply classic, type-directed optimizations.
Thus the @|holong| embedding's performance can exceed that of the @|eolong| embedding, as shown in @figure-ref{fig:typed-speedup}.
Typed Racket (@|TR_N|) in particular applies optimizations to unbox primitive values,
 select low-level primitive operations,
 provide fast access to data structures,
 and eliminate unused branches@~cite[stff-padl-2012 stf-oopsla-2012].

