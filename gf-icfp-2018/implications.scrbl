#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]

@; TODO
@; - fill in TODO about what else is in the figure
@; - classify examples as "good" "bad" "maybe"
@;   with dangerous bends
@; - one point of GT is that need to build incrementally,
@;   but the errors are definitely not incremental

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
  \tann{x}{\tnat} \wellM \equotient{x}{x} : \tnat
  \\
  \wellM \edyn{\tnat}{-2} : \tnat
  \\
  \equotient{(\edyn{\tnat}{-2})}{(\edyn{\tnat}{-2})} \rrEEstar 0
  \end{array}
}

Both the natural embedding and the locally-defensive embedding are sound for
 base types, in the sense that if @${v} is a value of type @${\tnat} according
 to the embedding, then @${v} is a natural number.
Furthermore, these embeddings define equivalent reduction sequences for any
 expression in which all type boundaries are of base type.


@subsection[#:tag "sec:base-type:verdict"]{Summary}

The natural and locally-defensive embeddings are dynamically sound for base
 types.
The erasure embedding is unsound for base types.


@section{For First-Order, Non-Base Types}
@subsection[#:tag "sec:first-order-type:verdict"]{Summary}

The natural embedding is dynamically sound for first-order, non-base types.
The locally-defensive embedding only enforces the top-level type constructor,
 and the erasure embedding is unsound.


@section{For Higher-Order Types}



@subsection[#:tag "sec:higher-order-type:verdict"]{Summary}

The natural embedding monitors higher-order values and reports the first
 evidence of a type mismatch.
The locally-defensive embedding checks each the constructor any result
 sent from a higher-order value to a typed context.
The erasure embedding is unsound for higher-order values.


@section{For Errors and Error Messages}

Reynolds

Error messages.


@subsection[#:tag "sec:errors:verdict"]{Summary}

In the natural embedding, every error due to a dynamically-typed value in
 a statically typed context can be attributed to a faulty boundary between
 static and dynamic code.
The locally-defensive embedding has limited ability to detect and report
 such errors.
The erasure embedding has no ability to detect type errors at runtime.


@section{For the Performance of Mixed-Typed Programs}

Enforcing soundness in a mixed-typed program adds performance overhead.
This cost can be high in the locally-defensive embedding, and enormous in the
 natural embedding.

The locally-defensive embedding incurs type-constructor checks at:
 type boundaries, applications of typed functions, and explicit @${\vchk} terms.
Each check adds a small cost,@note{In the model, checks have @${O(1)} cost.
  In the implementation, checks have basically-constant cost @${O(n)} where
  @${n} is the number of types in the widest union type
  @${(\tau_0 \cup \ldots \cup \tau_{n-1})} in the program.}
 however, these costs accumulate.
Furthermore, the added code and branches may affect JIT compilation.

The natural embedding incurs three significantly larger kinds of costs.
First, there is the cost of checking a value at a boundary.
Such checks may need to traverse the entire value to compute its type.
Second, there is an allocation cost when a higher-order value crosses a boundary.
Third, monitored values suffer an indirection cost; for example,
 a monitor guarding a dynamically-typed function checks every result computed
 by the function.
@; add note about TR contract optimizer?

@Secref{sec:conclusion} offers suggestions for reducing the cost of soundness.
The most promising direction is to combine @|LD-Racket| with the Pycket
 tracing JIT compiler@~cite[bbst-oopsla-2017].


@subsection[#:tag "sec:mixed-perf:verdict"]{Summary}

The cost of enforcing soundness in the natural embedding may slow a working
 program by two orders of magnitude.
The cost of the locally-defensive embedding is far lower, typically within
 one order of magnitude.
The erasure embedding adds no overhead to mixed-typed programs.


@section{For the Performance of Fully-Typed Programs}

If a program has few dynamically-typed components, then the locally-defensive
 embedding is likely to perform the worst of the three embeddings.
This poor performance stems from the ahead-of-time completion function,
 which rewrites all typed expressions to unconditionally check each function
 application and pair projection.
For example, a function that adds both elements of a pair value must check
 that its input has integer-valued components.
These checks cost time, and are unnecessary if the input value is typed.

@dbend{
  \begin{array}{l}
  \wellM \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\efst{x})}{(\esnd{x})}} : \tarr{\tpair{\tint}{\tint}}{\tint}
  \\ \carrow \vlam{\tann{x}{\tpair{\tint}{\tint}}}{\esum{(\echk{\tint}{(\efst{x})})}{(\echk{\tint}{(\esnd{x})})}}
  \\
  \end{array}
}

As a general rule, adding type annotations leads to a linear performance
 degredation in the locally-defensive embedding@~cite[gm-pepm-2018 gf-tr-2018].

By contrast, the natural embedding only pays to enforce soundness when static
 and dynamic components interact.
Furthermore, a compiler may leverage the soundness of the natural embedding
 to produce code that is more efficient than the erasure embedding.
In many dynamically typed language, primitives such as @${\vsum} check the
 type-tag of their arguments and dispatch to a low-level routine.
Sound static types can eliminate the need to dispatch.
Typed Racket implements this@~cite[stff-padl-2012] 


@subsection[#:tag "sec:typed-perf:verdict"]{Summary}

The natural embedding adds no overhead to fully-typed programs and may enable
 type-based optimizations that improve performance.
The locally-defensive embedding suffers its worst-case overhead on fully-typed
 programs, as it defends all typed code against possibly-untyped inputs.
The erasure embedding adds no overhead to fully-typed programs.


@; =============================================================================
@; =============================================================================

@;@; 0 the embeddings are weaker
@;
@;The natural, erasure, and locally-defensive embeddings implement distinct
@; reduction relations that provide three different notions of soundness,
@; reproduced in @figure-ref{fig:X-soundness}.
@;At a high level, all three guarantee that reduction is fully-defined for
@; well-typed programs.
@;The natural and locally-defensive embeddings additionally guarantee that typed
@; expressions do not raise tag errors.
@;And only the natural embedding guarantees that well-typed expressions reduce to
@; well-typed values.
@;
@;These three notions of soundness and evaluation have subtle consequences
@; when it comes to reasoning about programs.
@;Soundness describes the possible result values, and possible errors that may
@; arise.
@;The notions of reduction describe performance when all goes well.
@;Here we contrast three broad classes of implications: implications for
@; type-based reasoning, implications for mixed-typed programs, and
@; implications for fully-typed programs.
@;
@;@figure["fig:X-soundness" "Soundness" @list[
@;  @twocolumn[
@;    @tr-theorem[#:key #false @elem{static @${\mathbf{N}}-soundness}]{
@;      If @${\wellM e : \tau} then @${\wellNE e : \tau} and one
@;      @linebreak[]
@;      of the following holds:
@;      @itemlist[
@;        @item{ @${e \rrNSstar v \mbox{ and } \wellNE v : \tau} }
@;        @item{ @${e \rrNSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrND \tagerror} }
@;        @item{ @${e \rrNSstar \boundaryerror} }
@;        @item{ @${e} diverges}
@;      ] }
@;
@;    "example"
@;  ]
@;
@;  @twocolumn[
@;    @tr-theorem[#:key #false @elem{static @${\mathbf{E}}-soundness}]{
@;      If @${\wellM e : \tau} then @${\wellEE e} and one
@;      @linebreak[]
@;      of the following holds:
@;      @itemlist[
@;        @item{ @${e \rrEEstar v \mbox{ and } \wellEE v} }
@;        @item{ @${e \rrEEstar \tagerror} }
@;        @item{ @${e \rrEEstar \boundaryerror} }
@;        @item{ @${e} diverges}
@;      ] }
@;
@;    "example"
@;  ]
@;
@;  @twocolumn[
@;    @tr-theorem[#:key #false @elem{static @${\mathbf{K}}-soundness}]{
@;      If @${\wellM e : \tau} then 
@;      @${\wellM e : \tau \carrow e''}
@;      and @${\wellKE e'' : \tagof{\tau}}
@;      @linebreak[]
@;      and one of the following holds:
@;      @itemlist[
@;        @item{ @${e'' \rrKSstar v} and @${\wellKE v : \tagof{\tau}} }
@;        @item{ @${e'' \rrKSstar \ctxE{\edyn{\tau'}{\ebase[e']}} \mbox{ and } e' \rrKD \tagerror} }
@;        @item{ @${e'' \rrKSstar \boundaryerror} }
@;        @item{ @${e''} diverges }
@;      ] }
@;
@;    "example"
@;  ]
@;]]
@;
@;
@;@section{For Compositional Reasoning}
@;@; aaha THIS is the headline I'm looking for!
@;@; thesis: types have weaker meaning
@;
@;The embeddings' notions of soundness hinder programmers' ability to compositionally
@; reason about programs via type annotations.
@;In a purely statically typed language, if @${v} is a value of type @${\tpair{\tau_0}{\tau_1}}
@; then it follows that @${v} must be a pair @${\vpair{v_0}{v_1}} and furthermore
@; @${v_0} is of type @${\tau_0} and @${v_1} is of type @${\tau_1}.
@;Similarly, a value of type @${\tarr{\tau_d}{\tau_c}} must be a function;
@; expressions in the body of the function may compositionally assume
@; similar facts about arguments to the function, and clients of the function may
@; assume @${\tau_c} of the results it produces.
@;A programmer building an application can compose proofs to derive:
@; if a function returns a value of type @${\tpair{\tau_0}{\tau_1}} then this
@; value has a first component of type @${\tau_0}; soundness guarantees this
@; reasoning at runtime.
@;
@;The same guarantee does not hold in the natural embedding.
@;For example, a value of type @${\tarr{\tint}{\tint}} might be a typed function
@; or a monitor for a dynamically-typed value.
@;But @${\rrNSstar} makes a monitor behave like a typed function; this kind of
@; function might error but it is safe.
@;Same behavior in any future context.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    v & = & \edyn{\tarr{\tint}{\tint}}{(\vlam{x}{\vpair{x}{x}})} \rrNSstar \vmonfun{(\tarr{\tint}{\tint}}{(\vlam{x}{\vpair{x}{x}})}
@;  \\\esd_0 & = & \eapp{\ehole}{1}
@;  \\\esd_1 & = & \eapp{(\esta{\tarr{\tint}{\tint}}{\ehole})}{1}
@;  \\\esd_0[v] & \rrNSstar & \boundaryerror
@;  \\\esd_1[v] & \rrNSstar & \boundaryerror
@;  \end{array}
@;}
@;
@;The erasure embedding provides no guarantees.
@;Any value can inhabit any type, so there is no type-based reasoning whatsoever.
@;Negative numbers can masquerade as natural numbers, and functions can pretend
@; to be simple values.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    \edyn{\tnat}{-4} & \rrEEstar & -4
@;    \\\edyn{\tnat}{\vpair{\vlam{x}{x}}{\vlam{y}{y}}} & \rrEEstar & \vpair{\vlam{x}{x}}{\vlam{y}{y}}
@;  \end{array}
@;}
@;
@;The locally-defensive embedding guarantees only the outermost shape of a value.
@;A value of type @${\tint} must be an integer and a value of type @${\tnat} must
@; be a natural number.
@;A value of type @${\tpair{\tnat}{\tnat}} might contain any kind of values, however,
@; and a function of type @${\tarr{\tint}{\tint}} can produce any kind of result.
@;
@;One use case of gradual typing is inserting a typed API between an untyped
@; library and an untyped client@~cite[afgt-oopsla-2014].
@; @; DefinitelyTyped is not really an example of this
@;In the locally-defensive embedding, the types confirm the constructors and
@; then wash away.
@;The client has to access the data in typed code to get anything deeper.
@;
@;Constructor-level is very shallow, allows a type-cast operator by sending
@; one value across two boundaries
@;A function can have a completely incorrect type in one context.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-3}} & \rrKSstar & \vpair{-2}{-3}
@;  \\\eapp{(\esta{\tarr{\tint}{\tint}}{\edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{-3}}})}{1} & \rrKSstar & -3
@;  \end{array}
@;}
@;
@;@; too much typing ... maybe leave forgetful-ness for the performance part?
@;@dbend{
@;  \emph{cast} = \vlam{\tann{f}{\tarr{\tau_d}{\tau_c}}}{\edyn{\tarr{\tau_d'}{\tau_c'}}{\esta{\tarr{\tau_d}{\tau_c}}{f}}}
@;}
@;
@;In summary:
@; the natural embedding supports compositional type-based reasoning with the
@;  caveat of more errors;
@; the erasure embeddings does not support any kind of type-based reasoning;
@; and the locally-defensive supports a non-compositional constructor-based kind
@;  of reasoning.
@;
@;
@;@; -----------------------------------------------------------------------------
@;@section{For Errors and Error Messages}
@;@; thesis: silent and hard-to-trace errors in typed contexts
@;
@;@; start with Reynolds?
@;
@;The change in the meaning of types expands the class of errors that a programmer
@; must be prepared to debug.
@;If one takes the view that types are assertions about the kind of values that
@; can inhabit variables, then these assertions can silently fail.
@;This affects the ability to give informative error messages, or indicate any
@; error at all.
@;
@;The natural embedding may silently fail when a dynamically-typed function
@; enters typed code, because the function opaque to the type system.
@;A silent failure will be detected, however, the first time this function is
@; applied to a witnessing input --- no matter the context.
@;The erasure embedding fails silently at every opportunity.
@;The locally-defensive embedding may silently fail for functions and pairs.
@;Whether these failures are detected depends on the type annotations on their
@; uses.
@;
@;Here is a simple example for a product type.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    e & = & \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-1}{-2}})}
@;  \\ e & \rrNSstar & \efst{\boundaryerror}
@;  \\ e & \rrEEstar & {-1}
@;  \\ \wellM e : \tint & \carrow & \echk{\kint}{e} \rrKSstar \echk{\kint}{{-2}} \rrKSstar \boundaryerror
@;  \end{array}
@;}
@;
@;Analogous example for a function.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    e & = & \eapp{(\vlam{\tann{f}{\tarr{\tnat}{\tint}}}{\eapp{f}{2}})}{(\edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{{-4}}})}
@;  \\e & \rrNSstar & \boundaryerror
@;  \\e & \rrEEstar & {-4}
@;  \\e & \rrKSstar & {-4}
@;  \end{array}
@;}
@;
@;Another simple example for a function.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    e & = & \edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{\esum{x}{{-1}}}}
@;  \\\eapp{e}{1} & \rrNSstar & 0
@;  \\\eapp{e}{0} & \rrNSstar & \boundaryerror
@;  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrNSstar & \boundaryerror
@;  \\
@;  \\\eapp{e}{1} & \rrEEstar & 0
@;  \\\eapp{e}{0} & \rrEEstar & {-1}
@;  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrEEstar & {-1}
@;  \\
@;  \\\eapp{e}{1} & \rrKSstar & 0
@;  \\\eapp{e}{0} & \rrKSstar & \boundaryerror
@;  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrKSstar & {-1}
@;  \end{array}
@;}
@;
@;An implementation of the natural embedding can use eager detection to provide
@; helpful error messages.
@;Typed Racket, for example, implements the natural embedding and reports
@; runtime type errors in terms of @emph{the} static boundary between typed and untyped
@; code that led to the fault@~cite[tfffgksst-snapl-2017].
@;If such an error occurs, the programmer knows exactly where to start looking
@; for the source of the bug: either type annotation is wrong, or the untyped
@; code has a latent bug.
@;The error is either directly at the boundary or at a boundary internalized in a monitor.
@;Monitors provide a hook.
@;
@;The erasure embedding has no ability to detect errors, and therefore its ability
@; to produce error messages is a moot point.
@;
@;The locally-defensive embedding has limited information.
@;When an error occurs, the system has a plain value and an incompatible type
@; annotation.
@;No clue how the value got there.
@;This is especially bad if programmers follow John Hughes advice and build large
@; functions from small reusable components.
@;
@;Here is a tame example, adapted from @citet[vss-popl-2017].
@;This function @${g} is unsafe IMO.
@;The value of its argument can be any pair, but only pairs of integers can be
@; passed to @${f}.
@;What happens is that @${f} raises a tag error and the user cannot tell where
@; they went wrong without looking at the body of @${f}.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    f & = & \vlam{x_0}{\esum{\efst{ints}}{\esnd{ints}}}
@;  \\g & = & \vlam{\tann{x_1}{\tpair{\tint}{\tint}}}{\eapp{f}{x_1}}
@;  \end{array}
@;}
@;
@;@citet[vss-popl-2017] have explored one way of improving the locally-defensive
@; errors.
@;They build a map from values (specifically, memory addresses) to type casts
@; (boundaries).
@;When something goes wrong, they display a set of casts to narrow down the search.
@;
@;@; obviously set is worse ... can we give example where set inaccurate???
@;
@;
@;@section{For Base-Type Interactions}
@;
@;Despite their differences in general, the natural and locally-defensive
@; embeddings provide the same soundness for base types.
@;The type @${\tint} is only inhabited by integers and the type @${\tnat}
@; is only inhabited by natural numbers (see the canonical forms lemmas, @secref{sec:bridge}).
@;This similarity is because base types provide immediate accountability@~cite[mt-oopsla-2017]
@; at the cost of a single constructor check.
@;It follows that the natural embedding and locally-defensive embedding provide
@; equal semantics for all expressions @${e} whose boundary terms only exchange
@; values of base type.
@;For example:
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    e_0 & = & \edyn{\tint}{1}
@;  \\e_0 & \rrNSstar & 1
@;  \\e_0 & \rrKSstar & 1
@;  \\
@;  \\e_1 & = & \edyn{\tnat}{\vpair{1}{1}}
@;  \\e_1 & \rrNSstar & \boundaryerror
@;  \\e_1 & \rrKSstar & \boundaryerror
@;  \end{array}
@;}
@;
@;@; and more generally for any pure context
@;
@;See the appendix for a formal statement and proof.
@;If type boundaries are severely limited in expressiveness, then the
@; natural and locally-defensive embeddings agree.
@;
@;What about the erasure embedding?
@;There is a difference
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    \emph{natd} & = & \vlam{\tann{n}{\tnat}}{\vlam{\tann{d}{\tnat}}{\equotient{n}{d}}}
@;  \\e & = & \eapp{\eapp{\esta{\tarr{\tnat}{\tarr{\tnat}{\tnat}}}{\emph{natd}}}{{-2}}}{{-2}}
@;  \\ e & \rrNSstar & \boundaryerror
@;  \\ e & \rrEEstar & 1
@;  \\ e & \rrKSstar & \boundaryerror
@;  \end{array}
@;}
@;
@;The issue here is the @${\Delta} rule @${\Delta(\vquotient, \tnat, \tnat) = \tnat},
@; if types are not enforced, then calls to @${\vquotient} can receive any type
@; of arguments.
@;Unless the type system is limited to the host language and nothing more,
@; some programs behave differently when the types are not enforced.
@;Too bad!
@;The silent failure with @emph{natd} can be hard to debug, but its an error
@; that a type system can prevent.
@;
@;
@;@section{For the Performance of Mixed-Typed Programs}
@;
@;Each embedding pays a different cost when a value crosses a type boundary.
@;The natural embedding eagerly checks finite values and allocates a monitor
@; for function values; the checks have variable cost depending on value and
@; expected type, and the allocation has a pervasive kind of cost.
@;The erasure embedding pays zero cost.
@;The locally-defensive embedding pays a unit cost for each crossing.
@;If, for example, a well-typed value crosses a boundary expecting a pair
@; type, then each embedding takes a different course of action.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    v & = & \vpair{1}{\vlam{x}{x}}
@;  \\\esd & = & \edyn{\tpair{\tnat}{\tarr{\tint}{\tint}}}{\ehole}
@;  \\\esd[v] & \rrNSstar & \vpair{1}{\edyn{\tarr{\tint}{\tint}}{\vlam{x}{x}}}
@;  \\        & \rrNSstar & \vpair{1}{\vmonfun{\tarr{\tint}{\tint}}{\vlam{x}{x}}}
@;  \\\esd[v] & \rrEEstar & v
@;  \\\esd[v] & \rrKSstar & v
@;  \end{array}
@;}
@;
@;If a function crosses multiple boundaries, the natural embedding allocates
@; one monitor for each.
@;The erasure and locally-defensive embeddings do not allocate anything.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;    v & = & \vlam{\tann{x}{\tint}}{x}
@;  \\e & = & \edyn{\tarr{\tnat}{\tnat}}{(\esta{\tarr{\tint}{\tint}}{v})}
@;  \\e & \rrNSstar & \vmonfun{\tarr{\tnat}{\tnat}}{(\vmonfun{\tarr{\tint}{\tint}}{v})}
@;  \\e & \rrEEstar & v
@;  \\e & \rrKSstar & v
@;  \end{array}
@;}
@;
@;When it comes time to apply a monitored function, the natural embedding suffers
@; an indirection cost as it traverses the monitors.
@;The locally-defensive embedding, on the other hand, checks the type constructor
@; of the result.
@;
@;@dbend{
@;  \begin{array}{l c l}
@;  \eapp{(\vmonfun{\tarr{\tnat}{\tnat}}{(\vmonfun{\tarr{\tint}{\tint}}{v})})}{4} & \rrNSstar & \edyn{\tnat}{(\esta{\tint}{(\eapp{v}{\esta{\tint}{(\edyn{\tnat}{4})}})})}
@;  \\ & \rrNSstar & \edyn{\tnat}{(\esta{\tint}{4}}
@;  \\ & \rrNSstar & 4
@;  \end{array}
@;}
@;
@;@dbend{
@;  \begin{array}{l c l}
@;  \eapp{v}{4} : \tnat & \carrow & \echk{\knat}{(\eapp{v}{4})}
@;  \\ & \rrKSstar & \echk{\knat}{4}
@;  \\ & \rrKSstar & 4
@;  \end{array}
@;}
@;
@;The natural embedding pays for @emph{checking} any type,
@; and for @emph{allocation} and @emph{indirection} on higher-order values.
@;The locally-defensive embeddings pays for checking constructors at the boundary
@; and for checking the result of any elimination form.
@;In a program where large data structures or functions repeatedly cross
@; type boundaries, the natural embedding may suffer a huge performance overhead.
