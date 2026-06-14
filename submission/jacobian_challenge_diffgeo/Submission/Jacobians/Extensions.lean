/-
# Challenge extensions

Theorems extending Buzzard's challenge to concrete curve families,
serving as end-to-end tests of the formalization (cocycle 1-forms +
finite-dim bridge + genus + Jacobian + functoriality).

Currently:
- `Jacobians.Extensions.HyperellipticEven` — warm-ups + genus formula
  for the **even-degree** case (`HyperellipticEvenProj H` for
  `h : ¬ Odd H.f.natDegree`); the genus theorem is **completed** (PR #96).
- `Jacobians.Extensions.HyperellipticOdd` — the parallel **odd-degree**
  extension project (`HyperellipticOdd H h`): `dx/y` and `x^k dx/y` as
  holomorphic 1-forms, the genus formula, the hyperelliptic involution,
  and Weierstrass-point count. Mirrors the even file; its warm-ups and
  upper-bound genus are `sorry` scaffolds (a stretch track, not required
  for the core challenge).
- `Jacobians.Extensions.AbelJacobi` — Abel-Jacobi-side tests on the
  hyperelliptic curves: period-lattice rank `2g`, σ-equivariance
  `A(σ P) = -A(P)`, Abel's theorem on the principal divisor of
  `x - x₀`, and the Riemann bilinear relations on the canonical
  period matrix.
-/

import Submission.Jacobians.Extensions.HyperellipticOdd
import Submission.Jacobians.Extensions.HyperellipticEven
import Submission.Jacobians.Extensions.AbelJacobi
