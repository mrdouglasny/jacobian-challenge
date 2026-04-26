/-
# Unified coefficient family on `HyperellipticEvenProj H`

Combines the affine bundle (`AffineForm.lean`) and the affine-infinity
bundle (`AffineInfinityForm.lean`) into a coefficient family on the
quotient `HyperellipticEvenProj H`. Two of the three submodule
predicates -- `IsHolomorphicOneFormCoeff` and `IsZeroOffChartTarget` --
follow directly from the summand bundles via case-split on
`Quotient.out`.

The third predicate -- `SatisfiesCotangentCocycle` -- splits into:
* same-summand cases: handled by the within-summand cocycle bundles
  from S3/S4.
* cross-summand cases (`Sum.inl × Sum.inr` and symmetric): the
  Möbius-transition gluing region. Currently axiomatized at the
  smoothness level (in `EvenAtlas.lean`); the cocycle equation will
  follow once those smoothness axioms are discharged with explicit
  chain-rule computations on `x ↦ 1/x` and the polynomial-root
  corrections.

The coefficient is parametrized by **two** polynomials `g_aff` and
`g_inf` -- one for each summand. For the form to be globally well-
defined (i.e. the cross-summand cocycle to close), `g_aff` and `g_inf`
must be related by the Möbius transformation
`g_inf(u) du/v = g_aff(1/u) (-du/u²) (u^(g+1)/v)`. This relation is
encoded in S5; here we set up the framework before assembling it.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineInfinityForm
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas

namespace Jacobians.ProjectiveCurve.HyperellipticEvenProj

open scoped Manifold ContDiff Topology
open Polynomial
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

variable {H : HyperellipticData}

/-- Unified coefficient family on `HyperellipticEvenProj H`: dispatch
to the affine or affine-infinity coefficient by case-splitting on
`Quotient.out q`. -/
noncomputable def hyperellipticEvenCoeff
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ) :
    HyperellipticEvenProj H → ℂ → ℂ := fun q =>
  match Quotient.out q with
  | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
  | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b

/-- The unified coefficient is analytic on each chart target. -/
theorem hyperellipticEvenCoeff_isHolomorphicOneFormCoeff
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsHolomorphicOneFormCoeff (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt]
  unfold chartAt
  rcases hQ : Quotient.out q with a | b
  · simp only [hQ]
    show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt (H := H) a)
        : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineCoeff_isHolomorphicOneFormCoeff
      (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtA] at h
    exact h
  · simp only [hQ]
    show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)
        : OpenPartialHomeomorph (HyperellipticAffineInfinity H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineInfinityCoeff_isHolomorphicOneFormCoeff
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtB] at h
    convert h using 1

/-- The unified coefficient vanishes off each chart target. -/
theorem hyperellipticEvenCoeff_isZeroOffChartTarget
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q z hz
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hz
  unfold chartAt at hz
  rcases hQ : Quotient.out q with a | b
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (affineLiftChart H hf.out a).target =
        (HyperellipticAffine.affineChartAt (H := H) a).target := by
      simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineCoeff_isZeroOffChartTarget (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtA]; exact hz
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (infinityLiftChart H hf.out b).target =
        (HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b).target := by
      simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineInfinityCoeff_isZeroOffChartTarget
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtB]; exact hz

/-! ## Same-summand cocycle equations (lifted from S3/S4)

The four-way cocycle case-split on `Quotient.out q × Quotient.out q'`
has same-summand and cross-summand cases. The same-summand cases lift
directly from the affine (resp. affine-infinity) bundle's
`SatisfiesCotangentCocycle` proof through `affineLiftChart`
(resp. `infinityLiftChart`).

Cross-summand cases (`Sum.inl × Sum.inr`, `Sum.inr × Sum.inl`) are
the gluing-region cocycles that depend on the Möbius `x ↦ 1/x`
transition smoothness — currently axiomatized in `EvenAtlas.lean`. -/

/-- Same-summand cocycle on the affine summand. -/
theorem hyperellipticEvenCoeff_cocycle_inl_inl
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (q q' : HyperellipticEvenProj H)
    (a a' : HyperellipticAffine H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inl a')
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  classical
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      affineLiftChart H hf.out a := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      affineLiftChart H hf.out a' := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineLiftChart H hf.out a).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineLiftChart H hf.out a).target
    rw [hChQ]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      ((affineLiftChart H hf.out a).symm : ℂ → HyperellipticEvenProj H) := by
    funext w; show (_root_.chartAt ℂ q).symm w = _; rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      ((affineLiftChart H hf.out a') : HyperellipticEvenProj H → ℂ) := by
    funext w; show (_root_.chartAt ℂ q') w = _; rw [hChQ']
  rw [hExtTarget] at hz
  rw [hExtSymm] at hSrc
  rw [extChartAt_source, hChQ'] at hSrc
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target] at hz
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm] at hSrc
  obtain ⟨a'', ha''_src, ha''_eq⟩ := hSrc
  have ha_eq : (HyperellipticAffine.affineChartAt (H := H) a).symm z = a'' :=
    proj_inl_injective H ha''_eq.symm
  have hSrcAff : (HyperellipticAffine.affineChartAt (H := H) a).symm z ∈
      (HyperellipticAffine.affineChartAt (H := H) a').source := by
    rw [ha_eq]; exact ha''_src
  have hExtTargetA : (extChartAt 𝓘(ℂ, ℂ) a).target =
      (HyperellipticAffine.affineChartAt (H := H) a).target := by
    rw [extChartAt_target]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hzA : z ∈ (extChartAt 𝓘(ℂ, ℂ) a).target := hExtTargetA ▸ hz
  have hSrcA : (extChartAt 𝓘(ℂ, ℂ) a).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) a').source := by
    rw [extChartAt_source]
    show (HyperellipticAffine.affineChartAt (H := H) a).symm z ∈ _
    exact hSrcAff
  have hAffCocy := hyperellipticAffineCoeff_satisfiesCotangentCocycle (H := H) g_aff
    a a' z hzA hSrcA
  have hLHS_evencoe : hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticAffineCoeff (H := H) g_aff a z := by
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z = _
    rw [hQ]
  have hRHS_evencoe : hyperellipticEvenCoeff (H := H) g_aff g_inf q' =
      hyperellipticAffineCoeff (H := H) g_aff a' := by
    funext w
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ']
  rw [hLHS_evencoe, hRHS_evencoe]
  rw [hExtCoe', hExtSymm]
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_def, OpenPartialHomeomorph.lift_openEmbedding_apply]
  -- After simp: goal matches hAffCocy modulo extChartAt vs affineChartAt
  -- (which are defeq for our trivial model 𝓘(ℂ, ℂ)).
  exact hAffCocy

/-- Same-summand cocycle on the affine-infinity summand. -/
theorem hyperellipticEvenCoeff_cocycle_inr_inr
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (q q' : HyperellipticEvenProj H)
    (b b' : HyperellipticAffineInfinity H)
    (hQ : Quotient.out q = Sum.inr b) (hQ' : Quotient.out q' = Sum.inr b')
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  classical
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      infinityLiftChart H hf.out b := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      infinityLiftChart H hf.out b' := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (infinityLiftChart H hf.out b).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (infinityLiftChart H hf.out b).target
    rw [hChQ]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      ((infinityLiftChart H hf.out b).symm : ℂ → HyperellipticEvenProj H) := by
    funext w; show (_root_.chartAt ℂ q).symm w = _; rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      ((infinityLiftChart H hf.out b') : HyperellipticEvenProj H → ℂ) := by
    funext w; show (_root_.chartAt ℂ q') w = _; rw [hChQ']
  rw [hExtTarget] at hz
  rw [hExtSymm] at hSrc
  rw [extChartAt_source, hChQ'] at hSrc
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target] at hz
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm] at hSrc
  obtain ⟨b'', hb''_src, hb''_eq⟩ := hSrc
  have hb_eq : (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).symm z = b'' :=
    proj_inr_injective H hb''_eq.symm
  have hSrcInf : (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).symm z ∈
      (HyperellipticAffine.affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b').source := by
    rw [hb_eq]; exact hb''_src
  have hExtTargetB : (extChartAt 𝓘(ℂ, ℂ) b).target =
      (HyperellipticAffine.affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b).target := by
    rw [extChartAt_target]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hzB : z ∈ (extChartAt 𝓘(ℂ, ℂ) b).target := hExtTargetB ▸ hz
  have hSrcB : (extChartAt 𝓘(ℂ, ℂ) b).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) b').source := by
    rw [extChartAt_source]
    show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).symm z ∈ _
    exact hSrcInf
  have hInfCocy := hyperellipticAffineInfinityCoeff_satisfiesCotangentCocycle
    (H := H) g_inf b b' z hzB hSrcB
  have hLHS_evencoe : hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticAffineInfinityCoeff (H := H) g_inf b z := by
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z = _
    rw [hQ]
  have hRHS_evencoe : hyperellipticEvenCoeff (H := H) g_aff g_inf q' =
      hyperellipticAffineInfinityCoeff (H := H) g_inf b' := by
    funext w
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ']
  rw [hLHS_evencoe, hRHS_evencoe]
  rw [hExtCoe', hExtSymm]
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_def, OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact hInfCocy

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
