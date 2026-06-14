/-
Shared machinery for putting chart structures on projective zero loci.

Currently a stub; concrete content will land here as `ProjectiveCurve/Line`,
`Elliptic`, `Hyperelliptic`, and `PlaneCurve` are built out and reveal which
utilities want to be shared.

Planned utilities:
* `implicitFunctionChart` — build a `PartialHomeomorph` from the implicit
  function theorem, specialized to zero loci of a single complex-analytic
  function `f : ℂ^n → ℂ` with nonvanishing partial derivative.
* Common lemmas for gluing affine charts of `ℙ^n(ℂ)` along the standard
  `{x_i ≠ 0}` covers.
* Proofs that compositions of projective and affine chart-changes
  restricted to an algebraic curve are holomorphic.
-/
import Mathlib
