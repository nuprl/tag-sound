#lang gf-pldi-2018
@title[#:tag "sec:related-work"]{Related Work}

Reticulated is a gradual typing system for Python@~cite[vksb-dls-2014].
Checks happen in ad-hoc places (just list them, don't really say @emph{ad-hoc}).
Model proven to implement type-tag soundness.
Performance good.
In contrast we have principled checks.

Like types@~cite[bfnorsvw-oopsla-2009] are annotations with no semantics.
@citet[rnv-ecoop-2015] apply the idea to TypeScript; TypeScript has only like types,
 and their work gives programmers the choice of using (concrete) types that
 are enforced at run-time.
We generalize the idea.
