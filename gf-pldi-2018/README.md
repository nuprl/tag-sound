paper
===

"Spectrum of soundness"

TODO
---

- type soundness isn't the only reason for type systems, see:
  - typescript
  - java
  - pluggable types
  - "any language without a proof (ocaml haskell TR)"
- rename TYPE-ERROR VALUE-ERROR to be more like "good error" "bad error"?
  because some VALUE-ERROR really look like type errors (boudnary error)
- converting to typed "not guaranteed to improve performance"
  ... second-system syndrome?

- intro: "sound" => "conventionally sound"


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
