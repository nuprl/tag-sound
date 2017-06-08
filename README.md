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

- [ ] think about tag soundness in Typed Racket
- [ ] build simple model, quickly! try to state and prove properties
- [ ] extend Typed Racket
