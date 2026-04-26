/-
# Challenge extensions

Theorems extending Buzzard's challenge to concrete curve families,
serving as end-to-end tests of the formalization (cocycle 1-forms +
finite-dim bridge + genus + Jacobian + functoriality).

Currently:
- `Jacobians.Extensions.Hyperelliptic` — `dx/y` and `x^k dx/y` as
  holomorphic 1-forms, the genus formula, the hyperelliptic
  involution, and Weierstrass-point count, for the **odd-degree** case
  (`HyperellipticOdd H h`).
- `Jacobians.Extensions.HyperellipticEven` — analogous warm-ups + genus
  formula for the **even-degree** case (`HyperellipticEvenProj H` for
  `h : ¬ Odd H.f.natDegree`).
-/

import Jacobians.Extensions.Hyperelliptic
import Jacobians.Extensions.HyperellipticEven
