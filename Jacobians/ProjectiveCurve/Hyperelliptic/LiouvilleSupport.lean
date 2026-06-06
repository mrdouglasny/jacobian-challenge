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

end Jacobians.ProjectiveCurve
