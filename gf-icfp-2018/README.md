paper
===

"Spectrum of soundness"

TODO
---
- L 153 parens around dyn
- L 360 should be v:t not v
- L 362 give example of well-typed and divergent
- L Fig 4 A \not\in e' what is e' (confused ref 5 too)
- L 245-250 lifting is weird
- L 256 no free variables (hey all those are bound by Gamma he says)
- L 265 subset types no matching tag dont know what this means
- L 380 "LM does not have semantics" what does that mean?
- L ??? please RS RD and not R R'
- L 284 wtf does bowtie do
- L 655 conatural affects semantics but forgetful does not
- L 655 formal statement of how they differ???
- L 747 LF same notion of soundness (OH NO PLEASE don't say the same)
- L 70 do not call typescript gradual, please say optional
- L 648 typo, safety => soundness
- L 703 more clarification that you can forget safely
- L 1003 are you enforcing parametricity?
- L 1023 dont say "theoretical artifact" they may actually be useful in javascript etc.
- referee 3 pldi: clearly cite Vitousek for locally-defensive
- Fig 4 how does dyn language know the type context into which e is being embedded?
- Fig 4 inherits?
- L 461 what is category 1 category 2?
- L 463 typo in reynolds example
- L 685 could cache results of successful check?
X L 705 does not make sense (missing 'that combines')
- L 904 example of well-typed that is not well-tagged (impossible)
- L 1046 what about object-oriented?

- is the bowtie relation always correct?
- investigate performance of morsecode


TYPESETTING
- "flushleft" the typing rules
- rename A to R (for "result"?) .. maybe see mason/talcott for ideas
- ICFP 27 pages max, (bib excluded)
       acmsmall

- - -

imagine car manufacturer, certified vehicle, consumer buys it and
 starts replacing/modifying the parts. "Just trust me" he tells the car.
after changes maybe runs maybe doesn't, can make any guarantees about how
 it runs?

or, factory recycling

MT: replace parts of program with "trust me" things in the gamma.
 could be very useful, like z3 or some fast library for fast things.
 what guarantees about "mixed" programs?
