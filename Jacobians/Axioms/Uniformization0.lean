/-
`AX_genus_eq_zero_iff_homeo`: uniformization for genus 0.

**Classical theorem.** A compact connected Riemann surface has genus 0
iff it is homeomorphic (and in fact biholomorphic) to the Riemann
sphere `ℂP¹`, which in turn is homeomorphic to the 2-sphere
`S² ⊂ ℝ³`.

This is one direction of the **Uniformization Theorem** for compact
Riemann surfaces:
  - `g = 0` ⟹ `X ≃ ℂP¹ ≃ₜ S²` (Poincaré, Koebe).
  - `g = 1` ⟹ `X ≃ ℂ / Λ` for some rank-2 lattice `Λ`.
  - `g ≥ 2` ⟹ `X ≃ ℍ / Γ` for some Fuchsian group `Γ`.

Buzzard's challenge asks for the biconditional in the `g = 0` case,
phrased in terms of homeomorphism with
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

**Why axiomatized.** The proof requires either:
  1. **Riemann-Roch + Serre duality.** For `g = 0` a divisor of
     degree 1 gives a degree-1 meromorphic function, hence a
     biholomorphism `X ≃ ℂP¹`. Needs divisor + sheaf cohomology
     infrastructure (not in Mathlib at this pin).
  2. **Direct construction via harmonic functions** (Hilbert's
     method). Solve a Dirichlet problem on an annulus, take the
     real part to get a meromorphic function. Needs elliptic PDE
     theory on manifolds.
  3. **Hodge theory.** Use `H^0(X, Ω¹) = 0` (characterization of
     `g = 0`) to construct harmonic differentials.

All three are substantial independent formalization projects. The
`⇐` direction `X ≃ₜ S² ⟹ g = 0` is easier (just pull back forms
through the homeomorphism), but the axiom packages both.

Stereographic identification `ℂP¹ ≃ₜ S²` is constructed concretely
in `Jacobians/ProjectiveCurve/Line.lean` via
`onePointEquivSphereOfFinrankEq`. The axiom asserts the analogous
identification for *any* compact Riemann surface of genus 0.

See `docs/formalization-plan.md` §7; discharge priority: tied to
`AX_RiemannRoch` and `AX_SerreDuality`.
Reference: Forster, *Lectures on Riemann Surfaces*, Ch. IV;
Farkas-Kra, *Riemann Surfaces*, Ch. IV §5.
-/
import Jacobians.RiemannSurface.Genus

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom.** Genus-0 uniformization. A compact connected Riemann
surface has genus 0 iff it is homeomorphic to the 2-sphere. -/
axiom AX_genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))

end Jacobians.Axioms
