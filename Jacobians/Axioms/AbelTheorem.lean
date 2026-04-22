/-
`AX_AbelTheorem`: Abel's theorem — the Abel-Jacobi map is injective in
positive genus.

**Statement.** For `X` a compact Riemann surface of positive genus and
`P₀ : X` any basepoint, the Abel-Jacobi map `ofCurve P₀ : X → Jacobian X`
is injective.

**Why true.** Classical. Two routes:

1. Riemann theta divisor: if `ofCurve P = ofCurve Q` with `P ≠ Q`,
   Riemann's theorem on the theta divisor produces a meromorphic
   function with exactly divisor `P - Q`, which contradicts the
   maximum modulus principle (unless `g = 0`).

2. Forster-style residue calculus: a direct argument using meromorphic
   1-forms and winding numbers, avoiding theta functions.

**Why axiomatized.** Route 1 needs `RiemannTheta` + Riemann's theorem on
the theta divisor (a nontrivial analytic-geometry theorem). Route 2 needs
meromorphic-differential residue theory on compact Riemann surfaces,
which Mathlib does not have at this pin. Either way, this is deep.

See `docs/formalization-plan.md` §7; discharge priority #9 (deepest).
Reference: Mumford Vol I §II.3.3–II.3.5; Forster Ch. III.
-/
import Jacobians.RiemannSurface.Periods

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff

-- TODO (AX_AbelTheorem): the statement references `ofCurve` which lives
-- in `Jacobian/AbelJacobi.lean` (not yet built). Declare here when the
-- Jacobian bridge lands.
--
-- Target signature (sketch):
--
--   axiom AX_AbelTheorem {X : Type*} [...] (P₀ : X)
--       (h : 0 < genus X) :
--       Function.Injective (ofCurve P₀)

end Jacobians.Axioms
