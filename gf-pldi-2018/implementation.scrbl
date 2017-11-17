#lang gf-pldi-2018
@title[#:tag "sec:implementation"]{Scaling the Model to an Implementation}

@; -----------------------------------------------------------------------------

The models make a few technical simplifications, and do not address
 the full range of types found in practical languages.
Here we sketch how to overcome these limitations.


@section{Compiling to a Host Language}

The semantics of the models are specified as small-step operational semantics
 for an expression language.
Futhermore, the type-sound embeddings (natural, co-natural, forgetful, and locally-defensive)
 use two mutually-recursive reduction relations.
In practice, a migratory typing system for a language @${\langD}
 compiles statically-typed code to the host language, @${\langD}, and uses
 its operational semantics.
This raises two questions for our models.

The first question is how to represent the static types
 that the models use in monitor values and function applications.
For a monitor value @${(\vmonfun{\tarr{\tau_d}{\tau_c}}{v})}, a suitable
 compiled representation is @${(\vmonfun{\vpair{e_d}{e_c}}{v})} where
 @${e_d} is a host-language function that checks whether a value matches the
 domain type.
For functions @${(\vlam{\tann{x}{\tau}}{e})} in the forgetful embedding,
 the function domain @${\tau} can replace the domain type in its enclosing monitor.
 @;because the domain that the context expects is only important for proving type soundness.
Finally, a function @${(\vlam{\tann{x}{\tau}}{e})} in the locally-defensive
 embedding can compile to a function that checks the actual value of
 @${x} against the type @${\tau} before executing the function body@~cite[vss-popl-2017].

The second question is whether it is type-sound to use the @${\langD} reduction relation
 on statically-typed terms.
This is sound for all the models in this paper.
Intuitively, the only difference between static and dynamic reduction in the models
 is how they interpose boundary terms and the number of run-time checks they
 perform.
The boundaries are irrelevant in an implementation because there is only one
 notion of reduction.
As for the run-time checks, the static reduction can skip checks that the
 dynamic reduction must perform.
Thus it is safe to use the more conservative, dynamically-typed reduction relation.


@section{Tags for Additional Types}

The literature on migratory typing describes methods for implementing
 a variety of types, including untagged union types@~cite[thf-popl-2008]
 and structural class types@~cite[tfdffthf-ecoop-2015].
Those techniques apply to the co-natural and forgetful embeddings.
@; WHAT ABOUT BLAME???

Techniques for the locally-defensive embedding are less well-known, so we describe a few here.
To support @emph{types for mutable data}, it suffices to tag-check every
 read from a mutable data structure.
If all reads are checked, then writes to a mutable value do not require a tag check.

To support @emph{structural class types} and functions with @emph{optional and keyword arguments},
 a language designer has two choices.
One choice is to simply check that the incoming value is a class or procedure.
A second is to use reflective operations (if the language supports them)
 to count the methods and arity of the incoming value.
In our experience, the latter does not add significant overhead.

To support @emph{untagged union types}, the language of tags @${K} requires
 a matching tag combinator.
Let @${\mathsf{or}} be this constructor; the
 tag for a union type @${(\cup~\tau_0~\tau_1)} is then @${(\mathsf{or}~K_0~K_1)}
 where @${K_i} is the tag of type @${\tau_i}.

To support @emph{recursive types} of the form @${(\trec{\alpha}{\tau})},
 a suitable type-tag is the tag of @${(\vsubst{\tau}{\alpha}{\trec{\alpha}{\tau}})}.
This definition is well-founded provided the type variable @${\alpha} appears
 only as the parameter to a @emph{guarded} type.
A parameterized type is guarded if its type-tag does not depend on its argument types.

To support @emph{universal types} of the form @${\tall{\alpha}{\tau}}, we
 use the tag @${\tagof{\tau}} and define @${\tagof{\alpha} = \kany}.
Intuitively, there is no need to tag-check the use of a type variable because
 type variables have no elimination forms.

