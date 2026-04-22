/-
Part B — Riemann-surface-specific constructions.

Content is split across six submodules:

* `Jacobians.RiemannSurface.OneForm`       — `HolomorphicOneForm X`
* `Jacobians.RiemannSurface.PathIntegral`  — line integration along smooth paths
* `Jacobians.RiemannSurface.Homology`      — `H_1(X, ℤ) := Abelianization (π₁ X x₀)`
* `Jacobians.RiemannSurface.IntersectionForm` — Hurewicz + symplectic pairing
* `Jacobians.RiemannSurface.Periods`       — period pairing + period matrix in `𝔥_g`
* `Jacobians.RiemannSurface.Genus`         — `genus X := finrank ℂ (HolomorphicOneForm X)`

See `docs/formalization-plan.md` §4 for the design.
-/
import Jacobians.RiemannSurface.OneForm
