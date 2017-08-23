#lang gf-pldi-2018
@title[#:tag "sec:related-work"]{Related Work}

Reticulated is a gradual typing system for Python@~cite[vksb-dls-2014].
Checks happen in ad-hoc places (just list them, don't really say @emph{ad-hoc}).
Model proven to implement type-tag soundness.
Performance good.
In contrast we have principled checks.

Like types@~cite[bfnorsvw-oopsla-2009] are annotations with no semantics.
@citet[rnv-ecoop-2015] apply the idea to TypeScript; TypeScript has like types
 by default and programmers may opt-in to concrete (enforced) types.
In contrast, our types always have semantics.
The question is when those semantics get enforced.

