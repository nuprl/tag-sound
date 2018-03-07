#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Apples-to-Apples Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]

@; thesis: soundness matters

@; TODO
@; - kind-of-mention performance, but do NOT focus, that's for next section
@; - fill in TODO about what else is in the figure
@; - classify examples as "good" "bad" "maybe"
@;   with dangerous bends
@; - one point of GT is that need to build incrementally,
@;   but the errors are definitely not incremental

@; -----------------------------------------------------------------------------

@; 0 the embeddings are weaker

The natural, erasure, and locally-defensive embeddings implement distinct
 reduction relations that provide three different notions of soundness,
 reproduced in @figure-ref{fig:X-soundness}.
At a high level, all three guarantee that reduction is fully-defined for
 well-typed programs.
The natural and locally-defensive embeddings additionally guarantee that typed
 expressions do not raise tag errors.
And only the natural embedding guarantees that well-typed expressions reduce to
 well-typed values.

These three notions of soundness and evaluation have subtle consequences
 when it comes to reasoning about programs.
Soundness describes the possible result values, and possible errors that may
 arise.
The notions of reduction describe performance when all goes well.
Here we contrast three broad classes of implications: implications for
 type-based reasoning, implications for mixed-typed programs, and
 implications for fully-typed programs.

@figure["fig:X-soundness" "Soundness" @list[
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

    "example"
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

    "example"
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

    "example"
  ]
]]


@section{For Compositional Reasoning}
@; aaha THIS is the headline I'm looking for!
@; thesis: types have weaker meaning

The embeddings' notions of soundness hinder programmers' ability to compositionally
 reason about programs via type annotations.
In a purely statically typed language, if @${v} is a value of type @${\tpair{\tau_0}{\tau_1}}
 then it follows that @${v} must be a pair @${\vpair{v_0}{v_1}} and furthermore
 @${v_0} is of type @${\tau_0} and @${v_1} is of type @${\tau_1}.
Similarly, a value of type @${\tarr{\tau_d}{\tau_c}} must be a function;
 expressions in the body of the function may compositionally assume
 similar facts about arguments to the function, and clients of the function may
 assume @${\tau_c} of the results it produces.
A programmer building an application can compose proofs to derive:
 if a function returns a value of type @${\tpair{\tau_0}{\tau_1}} then this
 value has a first component of type @${\tau_0}; soundness guarantees this
 reasoning at runtime.

The same guarantee does not hold in the natural embedding.
For example, a value of type @${\tarr{\tint}{\tint}} might be a typed function
 or a monitor for a dynamically-typed value.
But @${\rrNSstar} makes a monitor behave like a typed function; this kind of
 function might error but it is safe.
Same behavior in any future context.

@dbend{
  \begin{array}{l c l}
    v & = & \edyn{\tarr{\tint}{\tint}}{(\vlam{x}{\vpair{x}{x}})} \rrNSstar \vmonfun{(\tarr{\tint}{\tint}}{(\vlam{x}{\vpair{x}{x}})}
  \\\esd_0 & = & \eapp{\ehole}{1}
  \\\esd_1 & = & \eapp{(\esta{\tarr{\tint}{\tint}}{\ehole})}{1}
  \\\esd_0[v] & \rrNSstar & \boundaryerror
  \\\esd_1[v] & \rrNSstar & \boundaryerror
  \end{array}
}

The erasure embedding provides no guarantees.
Any value can inhabit any type, so there is no type-based reasoning whatsoever.
Negative numbers can masquerade as natural numbers, and functions can pretend
 to be simple values.

@dbend{
  \begin{array}{l c l}
    \edyn{\tnat}{-4} & \rrEEstar & -4
    \\\edyn{\tnat}{\vpair{\vlam{x}{x}}{\vlam{y}{y}}} & \rrEEstar & \vpair{\vlam{x}{x}}{\vlam{y}{y}}
  \end{array}
}

The locally-defensive embedding guarantees only the outermost shape of a value.
A value of type @${\tint} must be an integer and a value of type @${\tnat} must
 be a natural number.
A value of type @${\tpair{\tnat}{\tnat}} might contain any kind of values, however,
 and a function of type @${\tarr{\tint}{\tint}} can produce any kind of result.

One use case of gradual typing is inserting a typed API between an untyped
 library and an untyped client@~cite[afgt-oopsla-2014].
 @; DefinitelyTyped is not really an example of this
In the locally-defensive embedding, the types confirm the constructors and
 then wash away.
The client has to access the data in typed code to get anything deeper.

Constructor-level is very shallow, allows a type-cast operator by sending
 one value across two boundaries
A function can have a completely incorrect type in one context.

@dbend{
  \begin{array}{l c l}
    \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-3}} & \rrKSstar & \vpair{-2}{-3}
  \\\eapp{(\esta{\tarr{\tint}{\tint}}{\edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{-3}}})}{1} & \rrKSstar & -3
  \end{array}
}

@; too much typing ... maybe leave forgetful-ness for the performance part?
@dbend{
  \emph{cast} = \vlam{\tann{f}{\tarr{\tau_d}{\tau_c}}}{\edyn{\tarr{\tau_d'}{\tau_c'}}{\esta{\tarr{\tau_d}{\tau_c}}{f}}}
}

In summary:
 the natural embedding supports compositional type-based reasoning with the
  caveat of more errors;
 the erasure embeddings does not support any kind of type-based reasoning;
 and the locally-defensive supports a non-compositional constructor-based kind
  of reasoning.


@; -----------------------------------------------------------------------------
@section{For Errors and Error Messages}
@; thesis: silent and hard-to-trace errors in typed contexts

@; start with Reynolds?

The change in the meaning of types expands the class of errors that a programmer
 must be prepared to debug.
If one takes the view that types are assertions about the kind of values that
 can inhabit variables, then these assertions can silently fail.
This affects the ability to give informative error messages, or indicate any
 error at all.

The natural embedding may silently fail when a dynamically-typed function
 enters typed code, because the function opaque to the type system.
A silent failure will be detected, however, the first time this function is
 applied to a witnessing input --- no matter the context.
The erasure embedding fails silently at every opportunity.
The locally-defensive embedding may silently fail for functions and pairs.
Whether these failures are detected depends on the type annotations on their
 uses.

Here is a simple example for a product type.

@dbend{
  \begin{array}{l c l}
    e & = & \efst{(\edyn{\tpair{\tnat}{\tnat}}{\vpair{-1}{-2}})}
  \\ e & \rrNSstar & \efst{\boundaryerror}
  \\ e & \rrEEstar & {-1}
  \\ \wellM e : \tint & \carrow & \echk{\kint}{e} \rrKSstar \echk{\kint}{{-2}} \rrKSstar \boundaryerror
  \end{array}
}

Analogous example for a function.

@dbend{
  \begin{array}{l c l}
    e & = & \eapp{(\vlam{\tann{f}{\tarr{\tnat}{\tint}}}{\eapp{f}{2}})}{(\edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{{-4}}})}
  \\e & \rrNSstar & \boundaryerror
  \\e & \rrEEstar & {-4}
  \\e & \rrKSstar & {-4}
  \end{array}
}

Another simple example for a function.

@dbend{
  \begin{array}{l c l}
    e & = & \edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{\esum{x}{{-1}}}}
  \\\eapp{e}{1} & \rrNSstar & 0
  \\\eapp{e}{0} & \rrNSstar & \boundaryerror
  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrNSstar & \boundaryerror
  \\
  \\\eapp{e}{1} & \rrEEstar & 0
  \\\eapp{e}{0} & \rrEEstar & {-1}
  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrEEstar & {-1}
  \\
  \\\eapp{e}{1} & \rrKSstar & 0
  \\\eapp{e}{0} & \rrKSstar & \boundaryerror
  \\\eapp{(\esta{\tarr{\tnat}{\tnat}}{e}}{0} & \rrKSstar & {-1}
  \end{array}
}

An implementation of the natural embedding can use eager detection to provide
 helpful error messages.
Typed Racket, for example, implements the natural embedding and reports
 runtime type errors in terms of @emph{the} static boundary between typed and untyped
 code that led to the fault@~cite[tfffgksst-snapl-2017].
If such an error occurs, the programmer knows exactly where to start looking
 for the source of the bug: either type annotation is wrong, or the untyped
 code has a latent bug.
The error is either directly at the boundary or at a boundary internalized in a monitor.
Monitors provide a hook.

The erasure embedding has no ability to detect errors, and therefore its ability
 to produce error messages is a moot point.

The locally-defensive embedding has limited information.
When an error occurs, the system has a plain value and an incompatible type
 annotation.
No clue how the value got there.
This is especially bad if programmers follow John Hughes advice and build large
 functions from small reusable components.

Here is a tame example, adapted from @citet[vss-popl-2017].
This function @${g} is unsafe IMO.
The value of its argument can be any pair, but only pairs of integers can be
 passed to @${f}.
What happens is that @${f} raises a tag error and the user cannot tell where
 they went wrong without looking at the body of @${f}.

@dbend{
  \begin{array}{l c l}
    f & = & \vlam{x_0}{\esum{\efst{ints}}{\esnd{ints}}}
  \\g & = & \vlam{\tann{x_1}{\tpair{\tint}{\tint}}}{\eapp{f}{x_1}}
  \end{array}
}

@citet[vss-popl-2017] have explored one way of improving the locally-defensive
 errorrs.
They build a map from values (specifically, memory addresses) to type casts
 (boundaries).
When something goes wrong, they display a set of casts to narrow down the search.

@; obviously set is worse ... can we give example where set inaccurate???


@section{For First-Order Interactions}

The natural and locally defensive embeddings give equivalent results for
 programs with first-order interactions.
See theorem TODO.

@; How does performance differ? I think natural is just BETTER

In retrospect, OOPSLA 2017 was a terrific conference for first-order migratory
 typing.
@citet[mt-oopsla-2017] demonstrate a model and implementation of a sound
 nominally-typed object-oriented language.
The type-checks are all first-order name checks; gradual typing is fast.
Work by @citet[rat-oopsla-2017] suggests that if type checks are the same
 as the runtime system's tag checks, performance is also great.

@; Unclear exactly how these systems are ...
@;  rat don't give a soundness theorem, I think they have the co-natural embedding
@;  mt  are extremely limited in the programs they can write



@section{For the Performance of Mixed-Typed Programs}

If a program has boundary terms, the natural embedding pays a significant price
 in three forms:
 checking, indirection, and allocation.
By @emph{checking}, we refer to the cost of validating a type-tag and recursively
 validating the components of a structured value.
For example, checking a list structure built from @${N} pair values requires
 (at least) @${2N} recursive calls.
Function monitors add an @emph{indirection} cost.
Every call to a monitored function incurs one additional boundary-crossing.
If a value repeatedly crosses boundary terms, these type-checking layers
 can accumulate without bound.@note{In a language with a JIT compiler,
  indirection may also affect inlining decisions.
  @; TODO does Spenser's work validate this?
  }
Finally, the @emph{allocation} cost of building a monitor value
 also adds to the performance overhead.

These add up, visually too. TODO

The erasure embedding has no soundness and no performance cost.

The locally-defensive embedding has a small cost for each boundary,
 one constructor-check more than the erasure embedding.
Illustrate please.


@section{For the Performance of Fully-Typed Programs}

@; with no boundaries
@; - natural has no overhead, fully sound
@; - erasure has small overhead, fully sound
@; - LD has overhead, though fully sound

If a typed expression has no boundary terms, the locally-defensive embedding
 pays a cost.
This is because it defends all typed expressions against possible untyped input.
Makes sense with separate compilation.

Example

In contrast, the natural embedding adds no overhead.

Furthermore, the natural embedding uses an efficient reduction relation in typed
 code.
Should run faster than the erasure embedding, and a real implementation should
 be able to leverage typed optimizations.

