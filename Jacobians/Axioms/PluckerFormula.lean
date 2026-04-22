/-
`AX_PluckerFormula`: genus of a smooth plane curve.

**Statement.** For `F : HomogeneousPoly ℂ[x, y, z] d` with `d ≥ 3` and
non-vanishing gradient on `{F = 0}`, the smooth projective plane curve
`X := SmoothPlaneCurve F` has genus

    genus X = (d - 1)(d - 2) / 2.

**Why true.** Adjunction formula on `ℙ²`: `ω_X = O_X(d - 3)` for a
smooth degree-`d` plane curve. Then `dim H⁰(X, ω_X) = dim H⁰(ℙ², O(d-3))
- dim H⁰(ℙ², O(-d + d - 3)) = ((d-3+2)(d-3+1)/2) - 0 = (d-1)(d-2)/2`.

**Why axiomatized.** The classical proof goes through adjunction on
`ℙ²`, which in turn needs sheaf cohomology of line bundles on
projective space. Same story as `AX_RiemannRoch` and `AX_SerreDuality`
— the scaffolding isn't in Mathlib.

**Scope.** Only needed for Track 2 `PlaneCurve.lean`. For `ProjectiveLine`
and `HyperellipticCurve`, the genus is computed directly (0 for ℙ¹, `g`
for `y² = f(x)` with `deg f = 2g+1` or `2g+2`).

See `docs/formalization-plan.md` §7; discharge priority #6.
Reference: Griffiths-Harris Ch. 2.4; Mumford's Red Book Ch. III §8.
-/
import Jacobians.RiemannSurface.Genus

namespace Jacobians.Axioms

-- TODO (AX_PluckerFormula): precise Lean statement requires
-- `SmoothPlaneCurve F`, which will live in
-- `Jacobians/ProjectiveCurve/PlaneCurve.lean` (not yet built).
-- Declare when consumed.

end Jacobians.Axioms
