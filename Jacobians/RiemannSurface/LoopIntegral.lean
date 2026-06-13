/-
Homology-level period pairing.

**Re-founded (REFOUND lane, Discussion #235).** `loopIntegralToH1` is now
defined as `developingPeriodMap` — the axiom-free developing-value period
pairing (`DevelopingPeriodMap.lean`), whose `ℤ`-linear extension over `H1`
comes from `Abelianization.lift` (no chosen cycle basis) and whose
`ℂ`-linearity in the form comes from `developingValue`'s form-linearity. This
removes `AX_PeriodCycleBasis` from the closure of `loopIntegralToH1`,
`periodMap`, `periodMapInBasis`, and `periodLatticeInBasis`. The
cycle-basis-facing lemma `loopIntegralToH1_loop` is preserved (now proved
axiom-free through the developing-value/canonical-arc agreement).
-/
import Jacobians.Axioms.PeriodCycleBasis
import Jacobians.RiemannSurface.CanonicalArcIntegral
import Jacobians.RiemannSurface.DevelopingPeriodMap

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

/-- The period integrand of each cycle-basis loop is interval-integrable.

This was formerly an axiom scoped to cycle-basis loops; the strong
`AnalyticArc` field now proves the statement for every analytic arc. -/
theorem AX_cycleBasisLoop_integrable {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (cb : Jacobians.Axioms.PeriodCycleBasis X x₀)
    (i : Fin (2 * genus X)) (form : HolomorphicOneForm X) :
    IntervalIntegrable (canonicalIntegrand (cb.loops i).arc form) MeasureTheory.volume 0 1 :=
  analyticArc_canonicalIntegrand_intervalIntegrable (cb.loops i).arc form

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The period functional of an analytic arc, bundled as a genuine
`ℂ`-linear map once all period integrands along the arc are integrable. -/
noncomputable def arcPeriodFunctional (γ : AnalyticArc X)
    (hγ : ∀ form : HolomorphicOneForm X,
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume 0 1) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun form := canonicalArcIntegral γ form
  map_add' f g := canonicalArcIntegral_add γ f g (hγ f) (hγ g)
  map_smul' c f := by simpa using canonicalArcIntegral_smul γ c f

/-- `arcPeriodVec`'s first component is the A-period functionals
(`αEmbed` projection) — the `arcPeriodFunctional` form of the layout pin
`Jacobians.Axioms.arcPeriodVec_fst`. -/
theorem arcPeriodVec_fst_eq_arcPeriodFunctional {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X}
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (Jacobians.Axioms.arcPeriodVec loops η).1 i =
      arcPeriodFunctional (loops (Jacobians.Axioms.αEmbed i)).arc
        (fun form =>
          analyticArc_canonicalIntegrand_intervalIntegrable
            (loops (Jacobians.Axioms.αEmbed i)).arc form) η :=
  rfl

/-- `arcPeriodVec`'s second component is the B-period functionals
(`βEmbed` projection) — the `arcPeriodFunctional` form of the layout pin
`Jacobians.Axioms.arcPeriodVec_snd`. -/
theorem arcPeriodVec_snd_eq_arcPeriodFunctional {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X}
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (Jacobians.Axioms.arcPeriodVec loops η).2 i =
      arcPeriodFunctional (loops (Jacobians.Axioms.βEmbed i)).arc
        (fun form =>
          analyticArc_canonicalIntegrand_intervalIntegrable
            (loops (Jacobians.Axioms.βEmbed i)).arc form) η :=
  rfl

/-- The homology-level period pairing, **re-founded** as the axiom-free
developing-value period map (`developingPeriodMap`). The `ℤ`-linear extension
over `H1 X x₀` is supplied by `Abelianization.lift` (universal property of
abelianization — no chosen cycle basis); the `ℂ`-linearity in the form by
`developingValue`'s form-linearity. -/
noncomputable def loopIntegralToH1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  developingPeriodMap x₀

/-- On the homology class of any analytic loop, evaluating `loopIntegralToH1`
at a form returns that loop's canonical arc integral. **Axiom-free**: the
developing-value functional agrees with the canonical arc integral on loop
classes (`developingValue_eq_canonicalArcIntegral`). -/
theorem loopIntegralToH1_loopToHomology_apply {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (loop : AnalyticLoop X x₀)
    (form : HolomorphicOneForm X) :
    loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology loop) form =
      canonicalArcIntegral loop.arc form := by
  rw [loopIntegralToH1, developingPeriodMap_apply,
    ← developingValue_eq_canonicalArcIntegral x₀ form loop.arc]
  rfl

/-- On the homology class of a chosen cycle-basis loop, `loopIntegralToH1`
returns that loop's canonical period functional. **Now axiom-free** in its
proof (the value on a loop class is the canonical arc integral, independent
of any basis). -/
theorem loopIntegralToH1_loop {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (i : Fin (2 * genus X)) :
    let cb := Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)
    loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology (cb.loops i))
      = arcPeriodFunctional (cb.loops i).arc
          (fun form => AX_cycleBasisLoop_integrable x₀ cb i form) := by
  let cb := Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)
  change loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology (cb.loops i))
      = arcPeriodFunctional (cb.loops i).arc
          (fun form => AX_cycleBasisLoop_integrable x₀ cb i form)
  ext form
  rw [loopIntegralToH1_loopToHomology_apply]
  rfl

end Jacobians.RiemannSurface
