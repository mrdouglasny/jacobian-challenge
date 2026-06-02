/-
# Pullback of holomorphic 1-forms by the hyperelliptic involution

The σ-pullback `σ* : Ω¹(X) → Ω¹(X)` on `X = HyperellipticEvenProj H`, defined
**concretely on the cocycle representation** (no `pullbackOneForm` axiom).

For `σ := hyperellipticEvenInvol H` (proven `ContMDiff` in `Involution.lean`),
the classical pullback `σ*ω = ω ∘ dσ` reads, in chart coordinates,

    (σ*ω).coeff q z = ω.coeff (σ q) (A_q z) · B_q z

with `A_q z := extChartAt (σq) (σ ((extChartAt q).symm z))` (follow σ into the
σq-chart) and `B_q z := fderiv (extChartAt(σq) ∘ σ ∘ (extChartAt q).symm) z 1`
(the chart-derivative of σ). The map `extChartAt(σq) ∘ σ ∘ (extChartAt q).symm`
is `writtenInExtChartAt … q σ`, so all of `Involution.lean`'s smoothness applies
to it directly.

**Correction to the roadmap.** The naive `ω.coeff (σq) z` is NOT a submodule
element: it fails the cotangent cocycle at branch points (projY chart, σ acts
`y↦−y`, derivative `−1`) and at the two ∞ points (σ swaps them). The honest
factor `B_q` fixes this; it evaluates to `1` on the smooth-Y (projX) charts, so
`σ*` reduces there to the naive formula — exactly where Mσ.4 consumes it
(`pullbackInvolutionCoeff_projX`).

See `docs/Msigma3-codex-plan.md`.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenForm
import Jacobians.RiemannSurface.OneForm
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace Jacobians.ProjectiveCurve

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface

variable {H : HyperellipticData}

/-- The σ-pullback of a holomorphic 1-form, at the coefficient level.
Guarded to vanish off the chart target so `IsZeroOffChartTarget` is immediate. -/
noncomputable def pullbackInvolutionCoeff [Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    HyperellipticEvenProj H → ℂ → ℂ :=
  fun q =>
    Set.indicator (extChartAt 𝓘(ℂ, ℂ) q).target
      (fun z =>
        form.coeff (hyperellipticEvenInvol H q)
            ((extChartAt 𝓘(ℂ, ℂ) (hyperellipticEvenInvol H q))
              (hyperellipticEvenInvol H ((extChartAt 𝓘(ℂ, ℂ) q).symm z)))
          * fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) (hyperellipticEvenInvol H q)) ∘
                hyperellipticEvenInvol H ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1)

variable [Fact (¬ Odd H.f.natDegree)]

/-- On the chart target, `pullbackInvolutionCoeff` is the honest pullback
formula (the `if`-guard is `True`). -/
lemma pullbackInvolutionCoeff_eq_on_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (q : HyperellipticEvenProj H) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target) :
    pullbackInvolutionCoeff form q z =
      form.coeff (hyperellipticEvenInvol H q)
          ((extChartAt 𝓘(ℂ, ℂ) (hyperellipticEvenInvol H q))
            (hyperellipticEvenInvol H ((extChartAt 𝓘(ℂ, ℂ) q).symm z)))
        * fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) (hyperellipticEvenInvol H q)) ∘
              hyperellipticEvenInvol H ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 :=
  Set.indicator_of_mem hz _

/-- `pullbackInvolutionCoeff` vanishes off the chart target. -/
lemma pullbackInvolutionCoeff_zero_off
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    IsZeroOffChartTarget (HyperellipticEvenProj H) (pullbackInvolutionCoeff form) :=
  fun _ _ hz => Set.indicator_of_notMem hz _

/-- Analyticity of the pullback coefficient on each chart target. -/
lemma pullbackInvolutionCoeff_isHolomorphic
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    IsHolomorphicOneFormCoeff (HyperellipticEvenProj H) (pullbackInvolutionCoeff form) := by
  sorry

/-- The pullback coefficient satisfies the cotangent cocycle. -/
lemma pullbackInvolutionCoeff_cocycle
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    SatisfiesCotangentCocycle (HyperellipticEvenProj H) (pullbackInvolutionCoeff form) := by
  sorry

/-- The σ-pullback lands in the holomorphic-1-form submodule. -/
lemma pullbackInvolutionCoeff_mem
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    pullbackInvolutionCoeff form ∈ holomorphicOneFormSubmodule (HyperellipticEvenProj H) :=
  ⟨pullbackInvolutionCoeff_isHolomorphic form,
   pullbackInvolutionCoeff_cocycle form,
   pullbackInvolutionCoeff_zero_off form⟩

/-- The σ-pullback coefficient is additive in the form (pointwise: the
chart-derivative factor is form-independent). -/
lemma pullbackInvolutionCoeff_add
    (form₁ form₂ : HolomorphicOneForm (HyperellipticEvenProj H)) :
    pullbackInvolutionCoeff (form₁ + form₂) =
      pullbackInvolutionCoeff form₁ + pullbackInvolutionCoeff form₂ := by
  funext q z
  rw [Pi.add_apply, Pi.add_apply]
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
  · rw [pullbackInvolutionCoeff_eq_on_target (form₁ + form₂) q hz,
        pullbackInvolutionCoeff_eq_on_target form₁ q hz,
        pullbackInvolutionCoeff_eq_on_target form₂ q hz]
    simp only [HolomorphicOneForm.coeff_add, Pi.add_apply]; ring
  · rw [pullbackInvolutionCoeff_zero_off (form₁ + form₂) q z hz,
        pullbackInvolutionCoeff_zero_off form₁ q z hz,
        pullbackInvolutionCoeff_zero_off form₂ q z hz, add_zero]

/-- The σ-pullback coefficient is homogeneous in the form. -/
lemma pullbackInvolutionCoeff_smul (c : ℂ)
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    pullbackInvolutionCoeff (c • form) = c • pullbackInvolutionCoeff form := by
  funext q z
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
  · rw [pullbackInvolutionCoeff_eq_on_target (c • form) q hz,
        pullbackInvolutionCoeff_eq_on_target form q hz]
    simp only [HolomorphicOneForm.coeff_smul, Pi.smul_apply, smul_eq_mul]; ring
  · rw [pullbackInvolutionCoeff_zero_off (c • form) q z hz,
        pullbackInvolutionCoeff_zero_off form q z hz, mul_zero]

/-- **The hyperelliptic-involution pullback** `σ* : Ω¹(X) → Ω¹(X)`, as a
ℂ-linear endomorphism of holomorphic 1-forms on `X = HyperellipticEvenProj H`. -/
noncomputable def pullbackInvolution :
    HolomorphicOneForm (HyperellipticEvenProj H) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticEvenProj H) where
  toFun form := ⟨pullbackInvolutionCoeff form, pullbackInvolutionCoeff_mem form⟩
  map_add' form₁ form₂ := Subtype.ext (pullbackInvolutionCoeff_add form₁ form₂)
  map_smul' c form := Subtype.ext (pullbackInvolutionCoeff_smul c form)

@[simp] lemma pullbackInvolution_coeff
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    (pullbackInvolution form).coeff = pullbackInvolutionCoeff form := rfl

end Jacobians.ProjectiveCurve
