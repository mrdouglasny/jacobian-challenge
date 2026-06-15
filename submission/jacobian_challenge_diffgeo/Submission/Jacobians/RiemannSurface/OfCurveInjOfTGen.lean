/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Jacobians.Axioms.AbelJacobiDivDef
import Submission.Jacobians.Axioms.OfCurveInjective
import Submission.Jacobians.Bridge.AbelEngineAdapter

universe u v w

/-!
# Abel–Jacobi injectivity from T-GEN (no `AX_PeriodCycleBasis`)

`AX_ofCurve_inj` (positive-genus injectivity of `ofCurveImpl X P`) currently
carries `AX_PeriodCycleBasis`, inherited from `AX_AbelTheorem` — specifically
from the **⊆** direction `Jacobians.Bridge.abel_subset`, whose only
conditionality is the cycle-basis expansion of the divisor's zero-period
homology class.

Under **T-GEN** (`AnalyticLoopsGenerateH1 x₀`: analytic-loop classes
`ℤ`-span `H1 X x₀`) the **⊆** direction is already discharged
`AX_PeriodCycleBasis`-free by `Jacobians.Bridge.abel_subset_basis_free`
(the `#198` single-loop generator replaces the cycle-basis `repr`). Since
`AX_ofCurve_inj` uses Abel's theorem **only in the ⊆ direction** (it derives
`D ∈ PrincipalDivisors` from `AJ(D) = 0 ∧ deg D = 0`, never the converse),
routing through `abel_subset_basis_free` makes the whole injectivity proof
standard-3 + T-GEN.

## Main result

* `ofCurveImpl_inj_of_tgen` — `AnalyticLoopsGenerateH1 (Classical.arbitrary X)
  → 0 < genus X → Function.Injective (ofCurveImpl X P)`, with
  `#print axioms` = `[propext, Classical.choice, Quot.sound]` (plus the
  explicit T-GEN hypothesis). No `AX_PeriodCycleBasis`.

Once T-GEN is an unconditional theorem (the PL lane), this drops its
hypothesis and `AX_ofCurve_inj` becomes axiom-free mechanically.

Note this is the *injectivity* headline only — the Abel-Jacobi map is a
group homomorphism between the *abelian-group* structures of `X` and
`Jacobian X`, both of which are already `AX_PeriodCycleBasis`-free
(`ofCurveImpl`, `abelJacobiDiv` are standard-3). The `ContMDiff`
functoriality headlines (`pushforward_contMDiff`, …) are a *separate*
story: they are differentiability claims on the `Jacobian X` *manifold*,
whose `ChartedSpace`/`IsManifold` instances bake in `AX_PeriodCycleBasis`
through the global `Axioms.instPeriodLatticeDiscrete` / `Axioms.AX_PeriodLattice`
instances — see the module docstring of `OfCurveInjOfTGen`'s sibling note
and the report. Those drop the axiom only when the *global instances* are
reproven from T-GEN, which is the PL-lane discharge, not an `_of_tgen`
rewiring at the consumer.
-/

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians Jacobians.Axioms Jacobians.RiemannSurface

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Abel–Jacobi injectivity from T-GEN, `AX_PeriodCycleBasis`-free.**

For a positive-genus compact Riemann surface, `ofCurveImpl X P` is injective.
This is the same statement as `AX_ofCurve_inj`, but its proof routes the
Abel ⊆ step through the basis-free engine
`Jacobians.Bridge.abel_subset_basis_free` over the explicit T-GEN
hypothesis, so its kernel closure is standard-3 + T-GEN — no
`AX_PeriodCycleBasis`.

Proof: two points with equal Abel-Jacobi images give a degree-0 divisor
`D = (Q₁) - (Q₂)` with `AJ(D) = 0` (basepoint independence) and `deg D = 0`;
the basis-free ⊆ direction puts `D` in `PrincipalDivisors X`; the
positive-genus obstruction `principal_imp_eq_of_genus_pos` then forces
`Q₁ = Q₂`. -/
theorem ofCurveImpl_inj_of_tgen
    (hgen : AnalyticLoopsGenerateH1 (Classical.arbitrary X))
    (P : X) (h : 0 < Jacobians.RiemannSurface.genus X) :
    Function.Injective (ofCurveImpl X P) := by
  intro Q₁ Q₂ heq
  let D : Axioms.Divisor X := FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂
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
  have hdeg : D ∈ (Axioms.Divisor.deg X).ker := by
    simp [D, Axioms.Divisor.deg]
  have hker : D ∈ (abelJacobiDiv X).ker ⊓ (Axioms.Divisor.deg X).ker :=
    ⟨hAJ, hdeg⟩
  have hprincipal : D ∈ PrincipalDivisors X :=
    Jacobians.Bridge.abel_subset_basis_free hgen hker
  exact principal_imp_eq_of_genus_pos h Q₁ Q₂ hprincipal

end Jacobians.RiemannSurface
