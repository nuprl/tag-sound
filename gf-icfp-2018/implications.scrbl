#lang gf-icfp-2018
@title[#:tag "sec:implications"]{Apples-to-Apples Implications}
@require[(only-in "techreport.rkt" tr-theorem tr-lemma)]

@; thesis: soundness matters

@; TODO
@; - revisit soundness
@; - contrast with examples
@; - kind-of-mention performance, but do NOT focus, that's for next section
@; - single-language corollaries ... not exactly sure how to weave these in
@; - fill in TODO about what else is in the figure
@; - classify examples as "good" "bad" "maybe"
@;   with dangerous bends

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

@dbend{
  \begin{array}{l c l}
    \edyn{\tpair{\tnat}{\tnat}}{\vpair{-2}{-3}} & \rrKSstar & \vpair{-2}{-3}
  \\\eapp{(\esta{\tarr{\tint}{\tint}}{\edyn{\tarr{\tnat}{\tnat}}{\vlam{x}{-3}}})}{1} & \rrKSstar & -3
  \end{array}
}

In summary:
 the natural embedding supports compositional type-based reasoning with the
  caveat of more errors;
 the erasure embeddings does not support any kind of type-based reasoning;
 and the locally-defensive supports a non-compositional constructor-based kind
  of reasoning.


@section{For Errors and Error Messages}

The change in the meaning of types expands the class of errors that a programmer
 must be prepared to debug.





The natural embedding does not eliminate the runtime type error, but
 detects such errors as soon as possible.
If a finite value reaches a type boundary, the natural embedding checks that
 the value is well-typed.
If an infinite (procedural) value reaches a type boundary, the natural embedding
 monitors the value and reports the first witness (if any) that the value
 is not well-typed.
An implementation can leverage this property to provide detailed error messages.
Typed Racket, for example, implements the natural embedding and reports
 runtime type errors using the static boundary between typed and untyped
 code that led to the fault@~cite[tfffgksst-snapl-2017].
If such an error occurs, the programmer knows exactly where to start looking
 for the source of the bug: either type annotation is wrong, or the untyped
 code has a latent bug.

The erasure embedding does nothing to prevent runtime type errors.
Anything can happen at runtime.
When reasoning about correctness, a programmer needs to forget the types.
Risk of silent failures!

Example: TODO

There is nothing to say about error messages.

The locally-defensive embedding is a weak compromise.
On one hand, it allows silent type errors for non-base types.
In the Reynolds example, the locally-defensive embedding will substitute the
 ill-typed pair into the body of the function: TODO

On the other hand, the locally-defensive embedding detects any type errors
 involving base types.
This halts the Reynolds program before it commits a type error: TODO

More generally, the locally-defensive embedding @emph{eventually} detects every
 type error in a ``live'' value, but misses type errors in unused code paths.

When it comes to reporting these errors, however, the locally defensive embedding
 is at a serious disadvantage compared to the natural embedding.
The only information at hand is that an assertion failed.
Values are not monitored, so there is no way to attribute the failure to a boundary
 between typed and untyped code.

@citet[vss-popl-2017] have explored one alternative to this limitation.
They keep a registry of values and track the type annotations that each value
 flows through.
This information can point to a set of boundaries when an assertion fails.
Less precise!


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

