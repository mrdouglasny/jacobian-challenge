import Jacobians.Challenge

/-!
Comparator challenge restatement of Buzzard's Jacobian Challenge v0.4 —
the 11 named property lemmas/theorems in `Jacobians.Challenge`.
Each is restated with `:= sorry` so the comparator verifies the solution
uses identical statements.

The 7 typeclass instances and definitional obligations are verified by
`Jacobians/ChallengeConformance.lean` in CI; comparator checks the theorems.

Run against `config-buzzard.json` once `AX_PeriodCycleBasis` and
`AX_AbelTheorem` are discharged.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobiansTest

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

theorem genus_eq_zero_iff_homeo :
    genus X = 0 ↔
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := sorry

theorem ofCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian.ofCurve P) := sorry

theorem ofCurve_self (P : X) :
    Jacobian.ofCurve P P = 0 := sorry

theorem ofCurve_inj (P : X) (h : 0 < genus X) :
    Function.Injective (Jacobian.ofCurve P) := sorry

theorem pushforward_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ)
      ω (Jacobian.pushforward f hf) := sorry

theorem pushforward_id_apply (P : Jacobian X) :
    Jacobian.pushforward id contMDiff_id P = P := sorry

theorem pushforward_comp_apply
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian X) :
    Jacobian.pushforward (g ∘ f) (hg.comp hf) P =
      Jacobian.pushforward g hg (Jacobian.pushforward f hf P) := sorry

theorem pullback_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ)
      ω (Jacobian.pullback f hf) := sorry

theorem pullback_id_apply (P : Jacobian X) :
    Jacobian.pullback id contMDiff_id P = P := sorry

theorem pullback_comp_apply
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian Z) :
    Jacobian.pullback (g ∘ f) (hg.comp hf) P =
      Jacobian.pullback f hf (Jacobian.pullback g hg P) := sorry

theorem pushforward_pullback (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) =
      ContMDiff.degree f hf • P := sorry

end JacobiansTest
