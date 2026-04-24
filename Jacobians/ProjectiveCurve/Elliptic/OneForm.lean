import Jacobians.ProjectiveCurve.Elliptic
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.AbelianVariety

/-- The invariant differential `dz` on an elliptic curve, represented by the
chart-local coefficient `1` on each chart target (and `0` off-target, per
the `IsZeroOffChartTarget` normalisation). -/
noncomputable def ellipticDz (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    HolomorphicOneForm (Elliptic ω₁ ω₂ h) :=
  ⟨fun x z => Set.indicator (extChartAt 𝓘(ℂ, ℂ) x).target (fun _ => (1 : ℂ)) z, by
    refine ⟨?_, ?_, ?_⟩
    · -- analyticity on chart target
      intro x
      refine AnalyticOn.congr (f := fun _ => (1 : ℂ)) analyticOn_const ?_
      intro z hz
      simp only [Set.indicator_of_mem hz]
    · -- cotangent cocycle
      intro x y z hz hyz
      have htrans : (extChartAt 𝓘(ℂ, ℂ) y) ((extChartAt 𝓘(ℂ, ℂ) x).symm z) ∈
          (extChartAt 𝓘(ℂ, ℂ) y).target :=
        (extChartAt 𝓘(ℂ, ℂ) y).map_source hyz
      show Set.indicator (extChartAt 𝓘(ℂ, ℂ) x).target (fun _ => (1 : ℂ)) z =
        Set.indicator (extChartAt 𝓘(ℂ, ℂ) y).target (fun _ => (1 : ℂ))
          ((extChartAt 𝓘(ℂ, ℂ) y) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1)
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem htrans]
      have hf := ComplexTorus.transition_fderiv_apply_one (L := ellipticLattice ω₁ ω₂ h)
        (p := x) (q := y) hz hyz
      calc (1 : ℂ)
          = (1 : ℂ) * 1 := by norm_num
        _ = (1 : ℂ) *
            (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) := by
              exact (congrArg (fun w : ℂ => (1 : ℂ) * w) hf).symm
    · -- zero off chart target
      intro x z hz
      show Set.indicator _ (fun _ => (1 : ℂ)) z = 0
      exact Set.indicator_of_notMem hz _⟩

theorem ellipticDz_ne_zero (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    ellipticDz ω₁ ω₂ h ≠ 0 := by
  intro hzero
  let x : Elliptic ω₁ ω₂ h := Classical.choice inferInstance
  -- At the chart image (extChartAt 𝓘(ℂ, ℂ) x) x ∈ (extChartAt 𝓘(ℂ, ℂ) x).target
  -- the coefficient of ellipticDz equals 1.
  let z : ℂ := (extChartAt 𝓘(ℂ, ℂ) x) x
  have hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) x
  have hcoeff :
      (ellipticDz ω₁ ω₂ h).coeff x z = (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x z :=
    congrArg (fun form : HolomorphicOneForm (Elliptic ω₁ ω₂ h) => form.coeff x z) hzero
  have hone : (ellipticDz ω₁ ω₂ h).coeff x z = 1 := by
    show Set.indicator _ (fun _ => (1 : ℂ)) z = 1
    exact Set.indicator_of_mem hz _
  have hzeroCoeff : (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x z = 0 := rfl
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = (ellipticDz ω₁ ω₂ h).coeff x z := hone.symm
      _ = (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x z := hcoeff
      _ = 0 := hzeroCoeff
  exact one_ne_zero this

theorem genus_Elliptic_pos (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    0 < genus (Elliptic ω₁ ω₂ h) := by
  unfold genus
  by_contra hgenus
  have hfinrank : Module.finrank ℂ (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) = 0 :=
    Nat.eq_zero_of_not_pos hgenus
  letI : Subsingleton (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) := Module.finrank_zero_iff.mp hfinrank
  exact ellipticDz_ne_zero ω₁ ω₂ h (Subsingleton.elim _ _)

/-! ### Upper bound: `genus (Elliptic) ≤ 1`

Approach: the chart-centre coefficient function `x ↦ form.coeff x (chart x x)`
defines a smooth ℂ-valued function on the compact complex manifold `Elliptic`,
hence constant (Mathlib: `MDifferentiable.exists_eq_const_of_compactSpace`).
Combined with the `IsZeroOffChartTarget` normalisation, this forces
`form = c • ellipticDz` globally. -/

/-- Chart-centre coefficient of a holomorphic 1-form on `Elliptic`. -/
noncomputable def ellipticCoeffFun (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])
    (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h)) :
    Elliptic ω₁ ω₂ h → ℂ :=
  fun x => form.coeff x ((extChartAt 𝓘(ℂ, ℂ) x) x)

/-- The coefficient function relates chart-locally via the cocycle's
derivative-1 property on `Elliptic`. -/
theorem ellipticCoeffFun_eq_local (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])
    (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h))
    (x : Elliptic ω₁ ω₂ h) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    ellipticCoeffFun ω₁ ω₂ h form ((extChartAt 𝓘(ℂ, ℂ) x).symm z) = form.coeff x z := by
  dsimp [ellipticCoeffFun]
  let y : Elliptic ω₁ ω₂ h := (extChartAt 𝓘(ℂ, ℂ) x).symm z
  have hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
  have hcocy := form.2.2.1 x y z hz hy
  have hder := ComplexTorus.transition_fderiv_apply_one (L := ellipticLattice ω₁ ω₂ h)
    (p := x) (q := y) hz hy
  rw [show fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1 = 1 by
    simpa [y] using hder] at hcocy
  simpa [y] using hcocy.symm

/-- The chart-centre coefficient function is manifold-differentiable. -/
theorem ellipticCoeffFun_mdifferentiable (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂])
    (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h)) :
    MDifferentiable (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
      (ellipticCoeffFun ω₁ ω₂ h form) := by
  intro x
  rw [mdifferentiableAt_iff_source_of_mem_source (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
    (f := ellipticCoeffFun ω₁ ω₂ h form) (x := x) (x' := x) (by simp)]
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
  let e := extChartAt 𝓘(ℂ, ℂ) x
  have htarget : e.target ∈ 𝓝[Set.range (𝓘(ℂ, ℂ))] e x := by
    simpa [e] using extChartAt_target_mem_nhdsWithin (I := 𝓘(ℂ, ℂ)) x
  have heq :
      (ellipticCoeffFun ω₁ ω₂ h form ∘ e.symm) =ᶠ[𝓝[Set.range (𝓘(ℂ, ℂ))] e x]
        form.coeff x := by
    refine Filter.mem_of_superset htarget ?_
    intro z hz
    simpa [e] using ellipticCoeffFun_eq_local ω₁ ω₂ h form x hz
  have hdiffTarget : DifferentiableWithinAt ℂ (form.coeff x) e.target (e x) := by
    simpa [HolomorphicOneForm.coeff, e] using
      (form.2.1 x).differentiableOn (e x) <|
        by simpa [e] using mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) x
  have hvalue :
      (ellipticCoeffFun ω₁ ω₂ h form ∘ e.symm) (e x) = form.coeff x (e x) := by
    simpa [e] using
      ellipticCoeffFun_eq_local ω₁ ω₂ h form x
        (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) x)
  have hdiffAt : DifferentiableAt ℂ (form.coeff x) (e x) :=
    hdiffTarget.differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) x).mem_nhds <|
        by simpa [e] using mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) x)
  have hdiff :
      DifferentiableWithinAt ℂ (form.coeff x) (Set.range (𝓘(ℂ, ℂ))) (e x) := by
    simpa using hdiffAt.differentiableWithinAt
  exact (heq.differentiableWithinAt_iff hvalue).2 hdiff

/-- The chart-local coefficient is constant on all chart targets
(consequence of being smooth on a compact complex manifold, plus the
chart-local cocycle relation). -/
theorem ellipticCoeff_eq_const_on_targets (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂])
    (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h)) :
    ∃ c : ℂ, ∀ x : Elliptic ω₁ ω₂ h, ∀ z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target,
      form.coeff x z = c := by
  rcases MDifferentiable.exists_eq_const_of_compactSpace (I := 𝓘(ℂ, ℂ))
      (ellipticCoeffFun_mdifferentiable ω₁ ω₂ h form) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x z hz
  have hpoint := congrArg
    (fun f : Elliptic ω₁ ω₂ h → ℂ => f ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) hc
  calc
    form.coeff x z =
        ellipticCoeffFun ω₁ ω₂ h form ((extChartAt 𝓘(ℂ, ℂ) x).symm z) :=
      (ellipticCoeffFun_eq_local ω₁ ω₂ h form x hz).symm
    _ = c := by simpa [Function.const_apply] using hpoint

/-- Every holomorphic 1-form on `Elliptic` is a scalar multiple of `ellipticDz`.
This uses the `IsZeroOffChartTarget` normalisation: on-target equality extends
to full submodule equality. -/
theorem eq_smul_ellipticDz (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])
    (form : HolomorphicOneForm (Elliptic ω₁ ω₂ h)) :
    ∃ c : ℂ, form = c • ellipticDz ω₁ ω₂ h := by
  rcases ellipticCoeff_eq_const_on_targets ω₁ ω₂ h form with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply HolomorphicOneForm.ext_of_coeff
  funext x z
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target
  · -- on-target: form.coeff x z = c = (c • ellipticDz).coeff x z
    rw [hc x z hz]
    show c = (c • ellipticDz ω₁ ω₂ h).coeff x z
    show c = c • (ellipticDz ω₁ ω₂ h).coeff x z
    show c = c • Set.indicator _ (fun _ => (1 : ℂ)) z
    rw [Set.indicator_of_mem hz]
    simp
  · -- off-target: both sides are zero by IsZeroOffChartTarget
    have hform : form.coeff x z = 0 := form.2.2.2 x z hz
    have hdz : (ellipticDz ω₁ ω₂ h).coeff x z = 0 := (ellipticDz ω₁ ω₂ h).2.2.2 x z hz
    show form.coeff x z = (c • ellipticDz ω₁ ω₂ h).coeff x z
    show form.coeff x z = c • (ellipticDz ω₁ ω₂ h).coeff x z
    rw [hform, hdz]
    simp

/-- **Theorem** (retires `AX_genus_Elliptic_eq_one`). The genus of an
elliptic curve is exactly 1, proved structurally via the explicit `dz`
basis element and the smooth-functions-on-compact-complex-manifolds
Liouville-style theorem. -/
theorem genus_Elliptic_eq_one (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    genus (Elliptic ω₁ ω₂ h) = 1 := by
  refine le_antisymm ?_ (genus_Elliptic_pos ω₁ ω₂ h)
  -- Upper bound: every form is a scalar multiple of ellipticDz
  -- ⇒ span {ellipticDz} = ⊤
  -- ⇒ finrank ≤ 1
  -- Use finrank_le_of_span_eq_top with ι = Unit, v _ = ellipticDz.
  have hspan :
      Submodule.span ℂ (Set.range (fun _ : Unit => ellipticDz ω₁ ω₂ h)) = ⊤ := by
    rw [Set.range_const]
    rw [Submodule.eq_top_iff']
    intro form
    rcases eq_smul_ellipticDz ω₁ ω₂ h form with ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  show Module.finrank ℂ (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) ≤ 1
  simpa using (finrank_le_of_span_eq_top hspan)

end Jacobians.ProjectiveCurve
