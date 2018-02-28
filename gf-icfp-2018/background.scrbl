#lang gf-icfp-2018
@title[#:tag "sec:background"]{Related Work}

@; TODO
@; - space-efficient contracts has a useful summary at the top,
@;   we should at least put that in section 2
@;   ... erased/natural are the standard, here's sketch of our three embeddings
@;   (2017-12-21 : what does this mean?)
@; - change 'untyped code' ... to something else ..  dynamic , legacy , 

@; @parag{Assumptions}
@; (0) no lump embedding! want observationally-equal values across boundaries
@; (1) boundaries are explicit in syntax
@; (2) no Dyn type, no type compatibility
@; (3) all values can cross boundary
@; (4) at least one ``infinite'' value
@; (5) type system makes finer distinctions than primops
@; (6) same values, don't need to convert floats to ints etc.

@; -----------------------------------------------------------------------------

The introduction does not have the space to talk about related work.
This secetion needs to fill the gap: justify informal claims, summarize the
 pre-migratory typing work, trace the origins of the three approaches, and
 the origins of ``spectrum of soundness''.

It is very important that we compare to like types and explain how this is not that.
The breezy related work that we tried last time clearly did not work.

@exact{\clearpage}

@;Given a dynamically typed language, the design of a migratory type system
@;poses two problems. The first one concerns the existing programming idioms. 
@;To avoid the need for large-scale rewrites, the new type system ought to
@;support existing idioms, which may necessitate the invention of new type
@;system elements. The second one concerns the boundary between the typed and
@;the untyped portions of code repositories. As mentioned, we cannot assume
@;that developers equip all their untyped code with the necessary type
@;annotations so mixed-typed programs will exist. This paper focuses on the
@;second problem, because it is the dominant source of performance problems
@;and deserves more attention than it has received initially. 
@;
@;Our novel take on this ``boundary problem'' is to understand it as a
@;multi-language problem in the spirit of Matthews and Findler@~cite[mf-toplas-2007].
@;From this perspective, a migratory type system
@;for a dynamically-typed host language @${\langD} adds two key pieces: (1) a
@;statically-typed language @${\langS}, and (2) a typed foreign function
@;interface (FFI) between the languages.  The language @${\langS} is basically
@;like the host language with syntax for explicit type annotations.  The
@;foreign function interface (FFI) is typically part of a runtime system that
@;monitors interactions between statically-typed and dynamically-typed
@;values. The FFI @emph{introduces} the boundary (and therefore run-time)
@;checks that ensure type soundness.
@;@; TODO matthias marked 'introduces' ... not sure why, can't read the writing
@;
@;From the literature on multi-language semantics we know that an FFI requires
@;a well-specified embedding of values from one language in the other and
@;that this embedding aims to provide a soundness guarantee. Since
@;@${\langD} and @${\langS} share values, value conversion is not a problem@~cite[gff-oopsla-2005 bbdt-ecoop-2016].
@;
@;@; TODO make the choices clearer, via 'on one hand' / 'other hand' ?
@;@bold{Note} We must make a choice concerning which values may cross
@;these special boundaries. To keep the boundaries as inexpensive as
@;possible, we might wish to restrict the set of FFI values to just numbers
@;and characters, i.e., small, ``flat'' values. To facilitate the migration
@;from the untyped world to the typed one, we ought to allow such boundaries
@;to show up wherever developers need them, which implies that all kinds of
@;values may cross the boundaries. All practical forms of migratory
@;and gradual type system prefer the second choice, and so do we in this
@;paper. @bold{End}
@;
@;An @emph{embedding} in this sense may consist of static and dynamic
@;components.  On the static end, the multi-language may add expression and
@;value forms, as well as typing rules for the new additions.  At a minimum,
@;the extension must include so-called @emph{boundary terms} to draw a line
@;between code from either source language; we use @${(\edyn{\tau}{e})} and
@;@${(\esta{\tau}{e})}.
@;A @${\vdyn} expression embeds a dynamically-typed expression @${e} into a
@;statically-typed context that expects a value of type @${\tau}.
@;A @${\vsta} expression embeds a statically-typed expression @${e}
@;of type @${\tau} into a dynamically-typed context.
@;
@;@; TODO still unclear
@;On the dynamic end, the multi-language requires type-directed strategies
@;for moving value forms across boundary terms.
@;Depending on the chosen strategy, the multi-language may need a way of associating
@;type information with a value; for example, to assert claims such as ``@${v} is an
@;dynamically-typed function that typed code expects to receive integers from.''
@;
@;The following section develops several different strategies in the context
@;of several lambda-calculus based language models. Each embedding strategy comes with
@;soundness benefits and performance costs, which just these choices
@;explain. Some choices explain existing industrial choices, while others
@;explain academic choices.
@;@; "academic" ???
