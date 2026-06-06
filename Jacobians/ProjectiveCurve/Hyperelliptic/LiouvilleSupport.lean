/-
# Local support lemmas for Liouville L2

This file contains small, axiom-free pieces of the Liouville-L2 pipeline for
even-degree hyperelliptic curves. The global theorem still needs the hard
single-valued entire extension and infinity-growth arguments, but on any
smooth-`Y` projX chart the numerator `ω_x · y` is already a well-defined local
analytic function.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Form
import Jacobians.GeneralResults.EntireGrowth

namespace Jacobians.ProjectiveCurve

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity
open Jacobians.ProjectiveCurve.HyperellipticEvenProj

variable {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]

/-- The affine branch point over a root `x` of `H.f`: `(x, 0)`. -/
def liouvilleBranchPoint (x : ℂ) (hx : H.f.eval x = 0) : HyperellipticAffine H :=
  ⟨(x, 0), by simp [hx]⟩

omit hf in
/-- At a branch point, squarefreeness gives `f'(x) ≠ 0`, so the `w = y`
chart is valid. -/
theorem liouvilleBranchPoint_mem_smoothLocusX {x : ℂ} (hx : H.f.eval x = 0) :
    liouvilleBranchPoint (H := H) x hx ∈ smoothLocusX H := by
  unfold liouvilleBranchPoint smoothLocusX
  exact eval_derivative_ne_zero_of_eval_eq_zero H hx

omit hf in
/-- A branch point has `y = 0`, so it is not in the projX smooth-`Y` locus. -/
theorem liouvilleBranchPoint_not_mem_smoothLocusY {x : ℂ} (hx : H.f.eval x = 0) :
    liouvilleBranchPoint (H := H) x hx ∉ smoothLocusY H := by
  intro hY
  exact hY rfl

/-- The local Liouville numerator on a smooth-`Y` projX chart:
`form.coeff q z * y(z)`, where `y(z)` is the IFT branch of `sqrt (H.f.eval z)`.

The hard Liouville-L2 work is to show that these local numerators glue to a
single entire function of `z` and satisfy the infinity growth bound. -/
noncomputable def liouvilleProjXNumerator
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun z =>
    form.coeff q z *
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)

/-- A form coefficient is analytic on the explicit smooth-`Y` projX target when
`q`'s chosen representative is the corresponding affine point. -/
theorem form_coeff_analyticOn_affineProjX_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (form.coeff q) (affineChartProjX (H := H) a hpY).target := by
  have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
    form.2.1 q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((HyperellipticEvenProj.chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    change
      ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (HyperellipticEvenProj.chartAt H hf.out q).target
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hform
  unfold HyperellipticEvenProj.chartAt at hform
  rw [hQ] at hform
  simp only [HyperellipticEvenProj.affineLiftChart,
    OpenPartialHomeomorph.lift_openEmbedding_target] at hform
  simpa [affineChartAt, hpY] using hform

/-- The local Liouville numerator is analytic on the smooth-`Y` projX target. -/
theorem liouvilleProjXNumerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (liouvilleProjXNumerator (H := H) form a hpY q)
      (affineChartProjX (H := H) a hpY).target := by
  exact (form_coeff_analyticOn_affineProjX_target form a hpY q hQ).mul
    (squareLocalHomeomorph_symm_eval_analyticOn (H := H) a hpY)

omit hf in
/-- The branch-chart factor `w ↦ f'(x(w)) / 2`, where
`x(w) = polynomialLocalHomeomorph.symm (w ^ 2)`, is analytic on a projY chart. -/
theorem polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H) :
    AnalyticOn ℂ
      (fun w : ℂ =>
        H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2)
      (affineChartProjY (H := H) a hpX).target := by
  set e := polynomialLocalHomeomorph (H := H) a hpX with he
  set chartTarget :=
    ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target with htarget
  have hSq : AnalyticOn ℂ (fun w : ℂ => w ^ 2) chartTarget :=
    (analyticOn_id.pow 2).mono (Set.subset_univ _)
  have hSymm : AnalyticOn ℂ e.symm e.target := by
    have hCD : ContDiffOn ℂ ω e.symm e.target :=
      polynomialLocalHomeomorph_contDiffOn_symm (H := H) a hpX
    rw [show (ω : WithTop ℕ∞) = ⊤ from rfl] at hCD
    exact (contDiffOn_omega_iff_analyticOn (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      e.open_target.uniqueDiffOn).mp hCD
  have hMaps : Set.MapsTo (fun w : ℂ => w ^ 2) chartTarget e.target := by
    intro w hw
    change w ^ 2 ∈ e.target
    simpa [chartTarget, affineChartProjY, e] using hw
  have hX : AnalyticOn ℂ (fun w : ℂ => e.symm (w ^ 2)) chartTarget :=
    hSymm.comp hSq hMaps
  have hDer : AnalyticOn ℂ
      (fun w : ℂ => H.f.derivative.eval (e.symm (w ^ 2))) chartTarget :=
    hX.aeval_polynomial H.f.derivative
  have hTwo : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) chartTarget :=
    analyticOn_const
  have hTwo_ne : ∀ w ∈ chartTarget, (2 : ℂ) ≠ 0 := by
    intro _ _
    norm_num
  have hHalf : AnalyticOn ℂ
      (fun w : ℂ => H.f.derivative.eval (e.symm (w ^ 2)) / 2) chartTarget :=
    hDer.div hTwo hTwo_ne
  simpa [chartTarget, e] using hHalf

/-- A form coefficient is analytic on an explicit smooth-`X` projY target when
the preferred affine representative is a branch-chart point (`a ∉ smoothLocusY`). -/
theorem form_coeff_analyticOn_affineProjY_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (form.coeff q) (affineChartProjY (H := H) a hpX).target := by
  have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
    form.2.1 q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((HyperellipticEvenProj.chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    change
      ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (HyperellipticEvenProj.chartAt H hf.out q).target
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hform
  unfold HyperellipticEvenProj.chartAt at hform
  rw [hQ] at hform
  simp only [HyperellipticEvenProj.affineLiftChart,
    OpenPartialHomeomorph.lift_openEmbedding_target] at hform
  simpa [affineChartAt, hpYn] using hform

/-- The local branch-chart Liouville numerator in the `w = y` coordinate:
`form.coeff · f'(x(w))/2`. This is the algebraic cancellation from
`dx = (2w/f'(x)) dw`, and is the bounded expression at branch points. -/
noncomputable def liouvilleProjYNumerator
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (q : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun w =>
    form.coeff q w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2)

/-- The branch-chart Liouville numerator is analytic in the `w = y` coordinate
at branch-chart points. This packages the blueprint's local cancellation:
there is no `1 / w` singularity left. -/
theorem liouvilleProjYNumerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (liouvilleProjYNumerator (H := H) form a hpX q)
      (affineChartProjY (H := H) a hpX).target := by
  exact (form_coeff_analyticOn_affineProjY_target form a hpX hpYn q hQ).mul
    (polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn (H := H) a hpX)

/-- Branch-point specialization of `liouvilleProjYNumerator_analyticOn`.
This is the local bounded/holomorphic expression supplied by the `w = y`
coordinate at a root of `H.f`. -/
theorem liouvilleBranchPoint_numerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {x : ℂ} (hx : H.f.eval x = 0)
    (q : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl (liouvilleBranchPoint (H := H) x hx)) :
    AnalyticOn ℂ
      (liouvilleProjYNumerator (H := H) form
        (liouvilleBranchPoint (H := H) x hx)
        (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx) q)
      (affineChartProjY (H := H) (liouvilleBranchPoint (H := H) x hx)
        (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx)).target := by
  exact liouvilleProjYNumerator_analyticOn form
    (liouvilleBranchPoint (H := H) x hx)
    (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx)
    (liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hx) q hQ

/-- Dividing the local numerator by the nonzero chart branch recovers the chart
coefficient. This is the local algebraic readout used in the final L2 assembly. -/
theorem form_coeff_eq_liouvilleProjXNumerator_div
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff q z =
      liouvilleProjXNumerator (H := H) form a hpY q z /
        (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  unfold liouvilleProjXNumerator
  have hYne := squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
  rw [mul_div_cancel_right₀ _ hYne]

/-- On a same-sheet overlap of two smooth-`Y` affine `x`-charts, the local
Liouville numerator `coeff · y` is independent of the chosen chart centre.

This is the basic gluing fact available directly from the `HolomorphicOneForm`
cotangent cocycle: the `x`-to-`x` transition is locally the identity, so the
coefficient is unchanged, and the two local `y`-branches agree on the overlap. -/
theorem liouvilleProjXNumerator_eq_of_projX_overlap
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (hpY' : a' ∈ smoothLocusY H)
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inl a')
    {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hSrc : ((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H) ∈
      (affineChartProjX (H := H) a' hpY').source) :
    liouvilleProjXNumerator (H := H) form a hpY q z =
      liouvilleProjXNumerator (H := H) form a' hpY' q' z := by
  classical
  set c := affineLiftChart H hf.out a with hc_def
  set c' := affineLiftChart H hf.out a' with hc'_def
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    rw [hc_def]
    unfold HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c' := by
    change HyperellipticEvenProj.chartAt H hf.out q' = c'
    rw [hc'_def]
    unfold HyperellipticEvenProj.chartAt
    rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjX (H := H) a hpY).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [hChQ]
    rw [hc_def]
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    simp [affineLiftChart, affineChartAt, hpY]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (c.symm : ℂ → HyperellipticEvenProj H) := by
    funext w
    change (_root_.chartAt ℂ q).symm w = c.symm w
    rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      (c' : HyperellipticEvenProj H → ℂ) := by
    funext w
    change (_root_.chartAt ℂ q') w = c' w
    rw [hChQ']
  have hExtSrc' : (extChartAt 𝓘(ℂ, ℂ) q').source = c'.source := by
    rw [extChartAt_source, hChQ']
  have hzExt : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcLift : c.symm z ∈ c'.source := by
    rw [hc_def, hc'_def]
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm]
    refine ⟨(affineChartProjX (H := H) a hpY).symm z, ?_, ?_⟩
    · simpa [affineChartAt, hpY, hpY'] using hSrc
    · simp [HyperellipticEvenProj.proj, affineChartAt, hpY]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) q').source := by
    rw [hExtSymm, hExtSrc']
    exact hSrcLift
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) q')
      ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = z := by
    rw [hExtCoe', hExtSymm]
    change (c.symm.trans c') z = z
    rw [hc_def, hc'_def]
    change (((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).symm.trans
        ((affineChartAt (H := H) a').lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out))) z = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := H) a')
        ((affineChartAt (H := H) a).symm z) = z
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a hpY]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a' hpY']
    change (((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H).val.1) = z
    exact affineChartProjX_symm_apply_fst (H := H) a hpY hz
  have hOverlap : z ∈ (c.symm.trans c').source := ⟨by
    rw [hc_def]
    simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY] using hz, hSrcLift⟩
  have hOverlapOpen : IsOpen (c.symm.trans c').source := (c.symm.trans c').open_source
  have hEqId : (fun w : ℂ => c' (c.symm w)) =ᶠ[nhds z] (fun w : ℂ => w) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlap) ?_
    intro w hw
    have hwTarget : w ∈ (affineChartProjX (H := H) a hpY).target := by
      have : w ∈ c.target := hw.1
      rw [hc_def] at this
      simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt, hpY] using this
    change (c.symm.trans c') w = w
    rw [hc_def, hc'_def]
    change (((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).symm.trans
        ((affineChartAt (H := H) a').lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out))) w = w
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := H) a')
        ((affineChartAt (H := H) a).symm w) = w
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a hpY]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a' hpY']
    change (((affineChartProjX (H := H) a hpY).symm w : HyperellipticAffine H).val.1) = w
    exact affineChartProjX_symm_apply_fst (H := H) a hpY hwTarget
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 = 1 := by
    rw [hExtCoe', hExtSymm]
    change fderiv ℂ (fun w : ℂ => c' (c.symm w)) z 1 = 1
    rw [Filter.EventuallyEq.fderiv_eq hEqId]
    simp
  have hCocy := form.2.2.1 q q' z hzExt hSrcExt
  have hCoeff : form.coeff q z = form.coeff q' z := by
    unfold HolomorphicOneForm.coeff
    rw [hCocy, hCoord, hDeriv, mul_one]
  have hSymInY :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) ∈
        (squareLocalHomeomorph (H := H) a' hpY').source := by
    have h2 := affineChartProjX_symm_apply_snd (H := H) a hpY hz
    rw [← h2]
    exact hSrc
  have hAgree :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) =
        (squareLocalHomeomorph (H := H) a' hpY').symm (H.f.eval z) :=
    squareLocalHomeomorph_symm_eq_of_mem (H := H) a a' hpY hpY' hz hSymInY
  unfold liouvilleProjXNumerator
  rw [hCoeff, hAgree]

/-- Sanity check against the existing explicit basis constructor: for
`hyperellipticForm H g`, the local Liouville numerator is exactly `g.eval`. -/
theorem liouvilleProjXNumerator_hyperellipticForm_eq
    {g : Polynomial ℂ} (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    liouvilleProjXNumerator (H := H) (hyperellipticForm H g) a hpY q z =
      g.eval z := by
  unfold liouvilleProjXNumerator
  rw [hyperellipticForm_coeff_projX (H := H) hDeg hpY hQ hz]
  have hYne := squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
  rw [div_mul_cancel₀ _ hYne]

/-- Sanity check in the branch coordinate: for the canonical form
`hyperellipticForm H g`, the cancelled projY numerator is `g(x(w))`. -/
theorem liouvilleProjYNumerator_hyperellipticForm_eq
    {g : Polynomial ℂ} (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {w : ℂ} (hw : w ∈ (affineChartProjY (H := H) a hpX).target) :
    liouvilleProjYNumerator (H := H) (hyperellipticForm H g) a hpX q w =
      g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) := by
  unfold liouvilleProjYNumerator
  rw [hyperellipticForm_coeff_of_lt H hDeg]
  change (hyperellipticEvenCoeff (H := H) g (infReverse H g)) q w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2) =
    g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
  change (match Quotient.out q with
    | Sum.inl a => hyperellipticAffineCoeff (H := H) g a
    | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g) b) w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2) =
    g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
  rw [hQ]
  simp only [hyperellipticAffineCoeff, hpYn, dite_false]
  rw [affineProjYCoeff_eq_on_target g a hpX hw]
  have hFne := polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) a hpX hw
  field_simp [hFne]

/-- In the even-degree case, `H.f.natDegree / 2 ≥ 2`. This is the arithmetic
fact needed to turn `natDegree ≤ N/2 - 2` into `natDegree < N/2 - 1`. -/
theorem even_natDegree_div_two_ge_two : 2 ≤ H.f.natDegree / 2 := by
  have hdeg4 : 4 ≤ H.f.natDegree := by
    have hdeg := H.h_degree
    have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
    obtain ⟨m, hm⟩ := heven
    omega
  omega

/-- **Liouville L2 assembly from the two hard analytic inputs.**

If a global numerator `G : ℂ → ℂ` has already been constructed, is entire, has
the infinity growth bound `N/2 - 2`, and reads out the local coefficients as
`G(z) / y(z)` on every smooth-`Y` projX chart, then Step 4
(`differentiable_eq_polynomial_of_growth`) gives the exact polynomial
decomposition required by Liouville L2. -/
theorem polynomial_decomposition_of_entire_growth
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (G : ℂ → ℂ) (hGdiff : Differentiable ℂ G)
    (C : ℝ)
    (hC : ∀ z, ‖G z‖ ≤ C * (1 + ‖z‖) ^ (H.f.natDegree / 2 - 2))
    (hReadout : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        G z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
        (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
        {z : ℂ}
        (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
        form.coeff q z =
          g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  obtain ⟨g, hgDeg, hgEval⟩ :=
    Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth
      (H.f.natDegree / 2 - 2) G hGdiff C hC
  refine ⟨g, ?_, ?_⟩
  · have htwo : 2 ≤ H.f.natDegree / 2 := even_natDegree_div_two_ge_two (H := H)
    omega
  · intro a hpY q hQ z hz
    rw [← hgEval z]
    exact hReadout a hpY q hQ hz

/-- The L2 chart-local decomposition matches the canonical
`hyperellipticForm` coefficient on every smooth-`Y` projX chart. -/
theorem coeff_eq_hyperellipticForm_on_projX_of_decomposition
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (hDecomp : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff q z = (hyperellipticForm H g).coeff q z := by
  rw [hDecomp a hpY q hQ hz]
  rw [hyperellipticForm_coeff_projX (H := H) hDeg hpY hQ hz]

/-- If an arbitrary holomorphic form and a canonical hyperelliptic form agree
on every preferred chart target, the off-target normalization in
`HolomorphicOneForm` upgrades the chartwise equality to equality of forms. -/
theorem oneForm_eq_hyperellipticForm_of_eqOn_chartTarget
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (g : Polynomial ℂ)
    (hCoeff : ∀ q : HyperellipticEvenProj H, ∀ z : ℂ,
      z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target →
        form.coeff q z = (hyperellipticForm H g).coeff q z) :
    form = hyperellipticForm H g := by
  apply HolomorphicOneForm.ext_of_coeff
  funext q z
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
  · exact hCoeff q z hz
  · show (form : HyperellipticEvenProj H → ℂ → ℂ) q z =
      (hyperellipticForm H g : HyperellipticEvenProj H → ℂ → ℂ) q z
    rw [form.2.2.2 q z hz, (hyperellipticForm H g).2.2.2 q z hz]

end Jacobians.ProjectiveCurve
