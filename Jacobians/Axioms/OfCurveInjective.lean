import Jacobians.Axioms.AbelTheorem
import Jacobians.RiemannSurface.DegreeOneGenusZero

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- The Abel-Jacobi map is injective on positive-genus compact Riemann surfaces.

Derived from the period-triangle basepoint-independence theorem, Abel's theorem
on degree-zero divisors, and the positive-genus obstruction to principal
divisors of the form `(Q₁) - (Q₂)`. -/
theorem AX_ofCurve_inj {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (P : X) (_h : 0 < Jacobians.RiemannSurface.genus X) :
    Function.Injective (ofCurveImpl X P) := by
  intro Q₁ Q₂ heq
  let D : Divisor X := FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂
  have hdiffP : ofCurveImpl X P Q₁ - ofCurveImpl X P Q₂ = 0 := by
    rw [heq, sub_self]
  have hbase :=
    ofCurveImpl_basepoint_independent (X := X) P (Classical.arbitrary X) Q₁ Q₂
  have hAJ : abelJacobiDiv X D = 0 := by
    rw [show abelJacobiDiv X D =
        ofCurveImpl X (Classical.arbitrary X) Q₁ -
          ofCurveImpl X (Classical.arbitrary X) Q₂ by
      simp [D, abelJacobiDiv]]
    rw [← hbase, hdiffP]
  have hdeg : D ∈ (Divisor.deg X).ker := by
    simp [D, Divisor.deg]
  have hprincipal : D ∈ PrincipalDivisors X := by
    rw [← AX_AbelTheorem (X := X)]
    exact ⟨hAJ, hdeg⟩
  exact principal_imp_eq_of_genus_pos _h Q₁ Q₂ hprincipal

end Jacobians.Axioms
