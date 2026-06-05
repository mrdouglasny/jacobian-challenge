/-
Cycle-basis construction of the homology-level period pairing.
-/
import Jacobians.Axioms.AnalyticCycleBasis
import Jacobians.RiemannSurface.CanonicalArcIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

/-- The period integrand of each (piecewise-analytic, rectifiable) cycle-basis
loop is interval-integrable. Classical regularity; dischargeable later by
strengthening `AnalyticArc`. Scoped to cycle-basis loops (false for arbitrary
cusp-y arcs). -/
axiom AX_cycleBasisLoop_integrable {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (cb : Jacobians.Axioms.AnalyticCycleBasis X x₀)
    (i : Fin (2 * genus X)) (form : HolomorphicOneForm X) :
    IntervalIntegrable (canonicalIntegrand (cb.loops i).arc form) MeasureTheory.volume 0 1

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

/-- The homology-level period pairing, constructed by integrating over the
analytic cycle-basis loops and extending `ℤ`-linearly over `H1 X x₀`. -/
noncomputable def loopIntegralToH1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  let cb := Classical.choice (Jacobians.Axioms.AX_AnalyticCycleBasis x₀)
  (cb.isBasis.constr ℤ
    (fun i =>
      arcPeriodFunctional (cb.loops i).arc
        (fun form => AX_cycleBasisLoop_integrable x₀ cb i form))).toAddMonoidHom

/-- On the homology class of a chosen cycle-basis loop, `loopIntegralToH1`
returns that loop's canonical period functional. -/
theorem loopIntegralToH1_loop {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (i : Fin (2 * genus X)) :
    let cb := Classical.choice (Jacobians.Axioms.AX_AnalyticCycleBasis x₀)
    loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology (cb.loops i))
      = arcPeriodFunctional (cb.loops i).arc
          (fun form => AX_cycleBasisLoop_integrable x₀ cb i form) := by
  let cb := Classical.choice (Jacobians.Axioms.AX_AnalyticCycleBasis x₀)
  change loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology (cb.loops i))
      = arcPeriodFunctional (cb.loops i).arc
          (fun form => AX_cycleBasisLoop_integrable x₀ cb i form)
  rw [← cb.loops_to_basis i]
  simp [loopIntegralToH1, cb]

end Jacobians.RiemannSurface
