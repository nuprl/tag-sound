paper
===

"Spectrum of soundness"

TODO
---

- investigate performance of morsecode
- remove "trust me" in forgetful model
- type soundness isn't the only reason for type systems, see:
  - typescript
  - java
  - pluggable types
  - "any language without a proof (ocaml haskell TR)"
- rename TYPE-ERROR VALUE-ERROR to be more like "good error" "bad error"?
  because some VALUE-ERROR really look like type errors (boudnary error)
- converting to typed "not guaranteed to improve performance"
  ... second-system syndrome?
- NOTE natural->forgetful is a MAJOR CHANGE
  and natural->delayed is minor

- intro: "sound" => "conventionally sound"

TYPESETTING
- e D A ... more space ... between notions of reduction and their arguments
  - same for fusion reduction
- "flushleft" the typing rules
- arrow types closer together


Meeting with Matthias, hope to have a good Sec 2 Sec 3 this weekend!
---

I. intro, credits to Siek/Greenberg/Findler
   -

II. Macro Gradual Typing as Multi-Lang
  - natural is sound but slow
  - identity is fast but "unsound"

III. Compromise  / Sacrifice / The Descent
  1. sources of cost
    - O(n) checks
    - indirection (JIT)
    - allocation
    - errors.... very important very hard to say
  2. attack checks
  3. attack checks
  4. attack checks

IV. Scaling the Model to an Implementation
  - general advice, where to add checks
  - remove unnecessary checks
  - module-level, requires and provides
  - TR specific???

V. Performance
  - how to measure, summarize JFP
  - plots
  - look at that

VI. Related

VII. Conclusion
  - what do types mean?
  - "watch this space"

-----------------------------------------------------------------------------

imagine car manufacturer, certified vehicle, consumer buys it and
 starts replacing/modifying the parts. "Just trust me" he tells the car.
after changes maybe runs maybe doesn't, can make any guarantees about how
 it runs?

MT: replace parts of program with "trust me" things in the gamma.
 could be very useful, like z3 or some fast library for fast things.
 what guarantees about "mixed" programs?
