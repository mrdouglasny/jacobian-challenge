/-
`AX_genus_eq_zero_iff_homeo`: uniformization for genus 0. **DISCHARGED** —
theorem since 2026-06-11 (formerly an axiom).

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

**How it was discharged** (both legs theorem-grade, standard-3):

* `⇒` (`Jacobians/RiemannSurface/GenusZeroForward.lean`,
  `nonempty_homeo_sphere_of_genus_eq_zero`): the keystone-backed
  Riemann–Roch theorem at a point divisor gives `h⁰((p)) = 2` when
  `g = 0`, hence a degree-one meromorphic function with principal
  divisor `(Q₁) - (Q₂)`; such a function is a biholomorphism to `ℙ¹`
  (`degreeOne_equiv_projectiveLine`), and `ℙ¹ ≃ₜ S²` by the
  stereographic homeomorphism of `Jacobians/ProjectiveCurve/Line.lean`.

* `⇐` (`Jacobians/Bridge/SphereGenusZero.lean`,
  `genus_eq_zero_of_homeo_sphere_unconditional`): transport simple
  connectedness of `S²` (proved via the ported two-open van Kampen
  development, `Jacobians/Topology/SphereSimplyConnected.lean`) across
  the homeomorphism, then every holomorphic 1-form has a global
  primitive (developing map), which is constant by Liouville, so
  `genus X = 0` (`Jacobians/RiemannSurface/GenusZeroBackward.lean`).

Reference: Forster, *Lectures on Riemann Surfaces*, Ch. IV;
Farkas-Kra, *Riemann Surfaces*, Ch. IV §5.
-/
import Submission.Jacobians.RiemannSurface.Genus
import Submission.Jacobians.RiemannSurface.GenusZeroForward
import Submission.Jacobians.Bridge.SphereGenusZero

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Genus-0 uniformization** (formerly an axiom, now a theorem). A compact
connected Riemann surface has genus 0 iff it is homeomorphic to the
2-sphere. -/
theorem AX_genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨Jacobians.RiemannSurface.nonempty_homeo_sphere_of_genus_eq_zero,
    Jacobians.RiemannSurface.genus_eq_zero_of_homeo_sphere_unconditional⟩

end Jacobians.Axioms
