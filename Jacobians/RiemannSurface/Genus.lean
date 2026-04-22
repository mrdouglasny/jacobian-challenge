/-
`genus X` — the geometric genus of a compact Riemann surface.

**Definition.** `genus X := Module.finrank ℂ (HolomorphicOneForm X)`.

**Design constraint (per Codex and Claude reviews):** `Module.finrank`
returns `0` when the module is infinite-dimensional. If
`FiniteDimensional ℂ (HolomorphicOneForm X)` is only a theorem (not a
global instance), every downstream `finrank` use can silently collapse
to `0`, and the `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` instance
becomes a charted space over `Unit` — type-correct but semantically dead.

So the `FiniteDimensional` instance is installed globally in
`Jacobians/Axioms/FiniteDimOneForms.lean` (`AX_FiniteDimOneForms`), and
this file just depends on it.

**No alternative "topological genus" here.** The identity `2g = b_1` (rank
of `H_1` equals twice the analytic genus) is Hodge theory; not needed
for the 24 Challenge sorries. If invoked later it's a derived theorem,
not an axiom.

See `docs/formalization-plan.md` §4.6.
-/
import Jacobians.RiemannSurface.OneForm
import Jacobians.Axioms.FiniteDimOneForms

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- The geometric genus of a compact Riemann surface `X`, defined as the
ℂ-dimension of the space of holomorphic 1-forms on `X`.

For `X = ProjectiveLine`, this will be `0` (no non-zero holomorphic
1-forms on ℙ¹). For a smooth plane curve of degree `d`, Plücker gives
`(d-1)(d-2)/2`. For a hyperelliptic curve `y² = f(x)` with `f` squarefree
of degree `2g+1` or `2g+2`, this is `g`. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm X)

end Jacobians.RiemannSurface
