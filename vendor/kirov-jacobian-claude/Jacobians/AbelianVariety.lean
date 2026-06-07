/-
Part A — standalone abelian-variety machinery, parameterized over an
arbitrary finite-dimensional ℂ-vector space `V`.

Content is split across four submodules:

* `Jacobians.AbelianVariety.Lattice`  — lattice conventions (uses Mathlib's `IsZLattice`).
* `Jacobians.AbelianVariety.Siegel`   — Siegel upper half space `𝔥_g`.
* `Jacobians.AbelianVariety.ComplexTorus` — `V ⧸ Λ` with the seven typeclass instances.
* `Jacobians.AbelianVariety.Theta`    — Riemann theta series.

See `docs/formalization-plan.md` §3 for the design.
-/
import Jacobians.AbelianVariety.Lattice
import Jacobians.AbelianVariety.ComplexTorus
import Jacobians.AbelianVariety.Siegel
import Jacobians.AbelianVariety.Theta
