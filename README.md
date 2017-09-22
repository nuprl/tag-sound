shallow
===

Exploring tag soundness in Typed Racket.

tag soundness
---

A tag sound language guarantees that if `\vdash e : \tau` then either:
- `e ->* v` and `v : \tau`
- `e` diverges
- `e` reduces to an error due to a partial primitive (index out of bounds)

Example: Reticulated Python is tag sound


TODO
---

- [ ] "strictness" analysis
  - TR is 100% eager
  - retic is lazy, with 1 lookahead (the tag)
  - racket is totally lazy
