/-
`HolomorphicOneForm ProjectiveLine` is a subsingleton — **direct proof**.

**Claim.** On the Riemann sphere there are no nonzero holomorphic
1-forms: `Subsingleton (HolomorphicOneForm ProjectiveLine)`.

**Proof (Liouville, no uniformization axiom).** A holomorphic 1-form is a
chart-local coefficient family `coeff : ℙ¹ → ℂ → ℂ`. Because every finite
point uses the same affine chart `chart0` (identity on ℂ), the cotangent
cocycle with trivial (identity) transition forces all finite-point
coefficients to agree with a single entire function `A := coeff ↑0`. Let
`B := coeff ∞`, also entire. The cocycle between the affine chart and the
infinity chart `w = 1/z` gives, for `z ≠ 0`,

    A z = B (z⁻¹) · (-(z²)⁻¹)          (the 1-form law dz = -(1/w²) dw).

As `|z| → ∞`, `z⁻¹ → 0`, so `B(z⁻¹) → B 0` and `(z²)⁻¹ → 0`; hence `A → 0`
at infinity. An entire function tending to `0` at infinity is bounded,
hence constant (Liouville, `Differentiable.exists_const_forall_eq_of_bounded`),
and the constant is the limit `0`. So `A ≡ 0`, whence `B(w) = 0` for all
`w ≠ 0`, and by continuity `B ≡ 0`. Therefore every coefficient vanishes
and the 1-form is `0`.

**This replaces the previous route** (which derived the subsingleton from
`genus_projectiveLine_eq_zero`, itself proved via the uniformization axiom
`AX_genus_eq_zero_iff_homeo`). The dependency is now inverted:
`Line/Genus.lean` derives `genus ℙ¹ = 0` from this axiom-free subsingleton.
See `docs/contracts/genus.md` (the ℙ¹ known-value cell, now
`PROVEN_CORE_AXIOMS`).
-/
import Jacobians.ProjectiveCurve.Line
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology ContDiff
open Jacobians Jacobians.RiemannSurface
open Complex Set Filter

namespace ProjectiveLine

/-! ### Chart evaluation lemmas (top-level forms of the facts used inside
the `ChartedSpace` / `IsManifold` proofs in `Line.lean`). -/

/-- `chart0` (the affine chart) is the identity on the finite part. -/
lemma chart0_coe (w : ℂ) : chart0 ((w : ℂ) : ProjectiveLine) = w :=
  RiemannSphere.chartCoe_apply_coe w

/-- `chart1` (the infinity chart `w = 1/z`) sends `↑z` to `z⁻¹` (for `z ≠ 0`). -/
lemma chart1_coe {z : ℂ} (hz : z ≠ 0) : chart1 ((z : ℂ) : ProjectiveLine) = z⁻¹ :=
  RiemannSphere.chartInfty_apply_coe hz

/-- `chart1` sends `∞` to `0`. -/
lemma chart1_infty : chart1 (OnePoint.infty : ProjectiveLine) = 0 :=
  RiemannSphere.chartInfty_apply_infty

/-- The inverse of the affine chart is the coercion `ℂ → ℙ¹`. -/
lemma chart0_symm (w : ℂ) : chart0.symm w = ((w : ℂ) : ProjectiveLine) :=
  RiemannSphere.chartCoe_symm_apply w

/-! ### `extChartAt` reductions for `ProjectiveLine` (self model `𝓘(ℂ)`). -/

/-- For the self model, the extended chart is just the chart's
`PartialEquiv`. -/
lemma extChartAt_eq (p : ProjectiveLine) :
    (extChartAt 𝓘(ℂ) p) = (_root_.chartAt ℂ p).toPartialEquiv := by
  simp only [extChartAt, modelWithCornersSelf_partialEquiv, OpenPartialHomeomorph.extend,
    PartialEquiv.trans_refl]

lemma chartAt_coe (a : ℂ) : _root_.chartAt ℂ ((a : ProjectiveLine)) = chart0 :=
  RiemannSphere.chartAtRS_coe a

lemma chartAt_infty : _root_.chartAt ℂ (OnePoint.infty : ProjectiveLine) = chart1 :=
  RiemannSphere.chartAtRS_infty

-- Finite chart `↑a`: apply / symm / target / source.
lemma eca_coe_apply (a w : ℂ) :
    (extChartAt 𝓘(ℂ) ((a : ProjectiveLine))) ((w : ℂ) : ProjectiveLine) = w := by
  rw [extChartAt_eq, chartAt_coe]; exact chart0_coe w
lemma eca_coe_symm (a w : ℂ) :
    (extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).symm w = ((w : ℂ) : ProjectiveLine) := by
  rw [extChartAt_eq, chartAt_coe]; exact chart0_symm w
lemma eca_coe_target (a : ℂ) : (extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).target = univ := by
  rw [extChartAt_eq, chartAt_coe]; exact RiemannSphere.chartCoe_target
lemma coe_mem_eca_coe_source (a z : ℂ) :
    ((z : ℂ) : ProjectiveLine) ∈ (extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).source := by
  rw [extChartAt_eq, chartAt_coe]
  change ((z : ℂ) : ProjectiveLine) ∈ RiemannSphere.chartCoe.source
  rw [RiemannSphere.chartCoe_source]
  simp [OnePoint.coe_ne_infty]

-- Infinity chart `∞`: apply (on `↑z`, `z ≠ 0`) / target / source.
lemma eca_infty_coe {z : ℂ} (hz : z ≠ 0) :
    (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)) ((z : ℂ) : ProjectiveLine) = z⁻¹ := by
  rw [extChartAt_eq, chartAt_infty]; exact chart1_coe hz
lemma eca_infty_target : (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)).target = univ := by
  rw [extChartAt_eq, chartAt_infty]
  change RiemannSphere.chartInfty.target = univ
  rw [RiemannSphere.chartInfty, OpenPartialHomeomorph.trans_target]
  simp [RiemannSphere.chartCoe_target]
lemma eca_infty_source :
    (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)).source
      = {p : ProjectiveLine | p ≠ ((0 : ℂ) : ProjectiveLine)} := by
  rw [extChartAt_eq, chartAt_infty]
  change RiemannSphere.chartInfty.source = _
  rw [RiemannSphere.chartInfty_source]
  ext p; simp

end ProjectiveLine

open ProjectiveLine

/-! ### Bounded range from vanishing at infinity (continuous + cocompact). -/

private lemma isBounded_range_of_tendsto_zero {A : ℂ → ℂ} (hc : Continuous A)
    (ht : Tendsto A (Filter.cocompact ℂ) (𝓝 0)) : Bornology.IsBounded (range A) := by
  have hmem : A ⁻¹' (Metric.closedBall (0 : ℂ) 1) ∈ Filter.cocompact ℂ :=
    ht (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)
  rw [mem_cocompact] at hmem
  obtain ⟨K, hK, hKsub⟩ := hmem
  have hbK : Bornology.IsBounded (A '' K) := (hK.image hc).isBounded
  have hsub : range A ⊆ A '' K ∪ Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ K
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr (hKsub hz)
  exact (hbK.union Metric.isBounded_closedBall).subset hsub

/-! ### The vanishing theorem. -/

/-- On `ProjectiveLine`, every holomorphic 1-form is the zero form.
Direct Liouville proof; no uniformization axiom. -/
theorem HolomorphicOneForm_projectiveLine_eq_zero
    (form : HolomorphicOneForm ProjectiveLine) : form = 0 := by
  obtain ⟨han, hcocy, hoff⟩ := form.2
  set c : ProjectiveLine → ℂ → ℂ := form.1 with hc_def
  -- The two entire coefficient functions.
  set A : ℂ → ℂ := c ((0 : ℂ) : ProjectiveLine) with hA_def
  set B : ℂ → ℂ := c (OnePoint.infty : ProjectiveLine) with hB_def
  have hA_an : AnalyticOn ℂ A univ := by
    have := han ((0 : ℂ) : ProjectiveLine); rwa [eca_coe_target] at this
  have hB_an : AnalyticOn ℂ B univ := by
    have := han (OnePoint.infty : ProjectiveLine); rwa [eca_infty_target] at this
  have hA_diff : Differentiable ℂ A := differentiableOn_univ.mp hA_an.differentiableOn
  have hB_diff : Differentiable ℂ B := differentiableOn_univ.mp hB_an.differentiableOn
  -- (1) Finite–finite cocycle: every finite coefficient equals `A`.
  have hfin : ∀ a : ℂ, c ((a : ℂ) : ProjectiveLine) = A := by
    intro a; funext z
    have hsrc : (extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).symm z
        ∈ (extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)).source := by
      rw [eca_coe_symm]; exact coe_mem_eca_coe_source 0 z
    have h := hcocy ((a : ProjectiveLine)) ((0 : ℂ) : ProjectiveLine) z
      (by rw [eca_coe_target]; trivial) hsrc
    -- transition `(extChartAt ↑0) ∘ (extChartAt ↑a).symm = id`, derivative 1
    have htrans : (⇑(extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)) ∘
        ⇑(extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).symm) = id := by
      funext w
      change (extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine))
          ((extChartAt 𝓘(ℂ) ((a : ProjectiveLine))).symm w) = w
      rw [eca_coe_symm, eca_coe_apply]
    rw [show (extChartAt 𝓘(ℂ) ((0:ℂ):ProjectiveLine))
          ((extChartAt 𝓘(ℂ) ((a:ProjectiveLine))).symm z) = z by
        rw [eca_coe_symm, eca_coe_apply]] at h
    rw [htrans, fderiv_id, ContinuousLinearMap.id_apply, mul_one] at h
    exact h
  -- (2) Affine–infinity cocycle: `A z = B z⁻¹ · (-(z²)⁻¹)` for `z ≠ 0`.
  have hrel : ∀ z : ℂ, z ≠ 0 → A z = B z⁻¹ * (-(z ^ 2)⁻¹) := by
    intro z hz
    have hsrc : (extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)).symm z
        ∈ (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)).source := by
      rw [eca_coe_symm, eca_infty_source]
      simp only [mem_setOf_eq, ne_eq, OnePoint.coe_eq_coe]; exact hz
    have h := hcocy ((0 : ℂ) : ProjectiveLine) (OnePoint.infty : ProjectiveLine) z
      (by rw [eca_coe_target]; trivial) hsrc
    rw [show (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine))
          ((extChartAt 𝓘(ℂ) ((0:ℂ):ProjectiveLine)).symm z) = z⁻¹ by
        rw [eca_coe_symm, eca_infty_coe hz]] at h
    -- The transition `(extChartAt ∞) ∘ (extChartAt ↑0).symm` agrees with `(·⁻¹)` on a
    -- neighbourhood of `z` (where `z ≠ 0`); the port's `∞`-chart differs from `(·⁻¹)`
    -- only at the junk point `0`, so we evaluate the derivative via eventual equality.
    have hfd : fderiv ℂ (⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)) ∘
        ⇑(extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)).symm) z 1 = -(z ^ 2)⁻¹ := by
      have heq : (⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine)) ∘
          ⇑(extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)).symm) =ᶠ[𝓝 z] (fun w => w⁻¹) := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        change (extChartAt 𝓘(ℂ) (OnePoint.infty : ProjectiveLine))
            ((extChartAt 𝓘(ℂ) ((0 : ℂ) : ProjectiveLine)).symm w) = w⁻¹
        rw [eca_coe_symm, eca_infty_coe hw]
      rw [heq.fderiv_eq]
      exact deriv_inv
    rw [hfd] at h
    exact h
  -- (3) `A → 0` at infinity, hence `A ≡ 0` by Liouville.
  have hA_tendsto : Tendsto A (Filter.cocompact ℂ) (𝓝 0) := by
    have h_inv : Tendsto (fun z : ℂ => z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
      simpa [← Metric.cobounded_eq_cocompact] using Filter.tendsto_inv₀_cobounded (α := ℂ)
    -- g z := B z⁻¹ · (-(z⁻¹)^2)  tends to  B 0 · 0 = 0
    have hBz : Tendsto (fun z : ℂ => B z⁻¹) (Filter.cocompact ℂ) (𝓝 (B 0)) :=
      (hB_diff.continuous.continuousAt).tendsto.comp h_inv
    have hsq : Tendsto (fun z : ℂ => -((z⁻¹) ^ 2)) (Filter.cocompact ℂ) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => -((z⁻¹) ^ 2)) (Filter.cocompact ℂ) (𝓝 (-(0 ^ 2))) :=
        (h_inv.pow 2).neg
      simpa using h
    have hg : Tendsto (fun z : ℂ => B z⁻¹ * (-((z⁻¹) ^ 2))) (Filter.cocompact ℂ) (𝓝 0) := by
      have := hBz.mul hsq; simpa using this
    refine hg.congr' ?_
    -- A =ᶠ g on the cocompact filter (they agree off `{0}`)
    have hcompl : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ Filter.cocompact ℂ :=
      isCompact_singleton.compl_mem_cocompact
    filter_upwards [hcompl] with z hz
    rw [hrel z (by simpa using hz), inv_pow]
  have hA_bdd : Bornology.IsBounded (range A) :=
    isBounded_range_of_tendsto_zero hA_diff.continuous hA_tendsto
  obtain ⟨c0, hc0⟩ := hA_diff.exists_const_forall_eq_of_bounded hA_bdd
  have hc0_zero : c0 = 0 := by
    have h1 : Tendsto A (Filter.cocompact ℂ) (𝓝 c0) := by
      have : A = fun _ => c0 := funext hc0
      rw [this]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 hA_tendsto
  have hA0 : ∀ z, A z = 0 := fun z => by rw [hc0 z, hc0_zero]
  -- (4) Hence `B ≡ 0`.
  have hB0_ne : ∀ w : ℂ, w ≠ 0 → B w = 0 := by
    intro w hw
    have hz : (w⁻¹ : ℂ) ≠ 0 := inv_ne_zero hw
    have := hrel w⁻¹ hz
    rw [hA0, inv_inv] at this
    have hfac : (-((w⁻¹ : ℂ) ^ 2)⁻¹) ≠ 0 :=
      neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hw)))
    exact (mul_eq_zero.mp this.symm).resolve_right hfac
  have hB0 : B = 0 := by
    have : EqOn B 0 ({(0 : ℂ)}ᶜ) := fun w hw => by simpa using hB0_ne w hw
    exact Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hB_diff.continuous continuous_const this
  -- (5) Assemble: `c p = 0` for every `p`, so `form = 0`.
  have hc0_all : c = 0 := by
    funext p
    induction p using OnePoint.rec with
    | infty => funext z; change B z = 0; rw [hB0]; rfl
    | coe a => funext z; rw [hfin a, hA0]; rfl
  apply HolomorphicOneForm.ext_of_coeff
  rw [HolomorphicOneForm.coeff_zero]
  change form.1 = 0
  rw [← hc_def]; exact hc0_all

/-- On `ProjectiveLine`, the space of holomorphic 1-forms is a subsingleton.
**Axiom-free** (direct Liouville proof in `HolomorphicOneForm_projectiveLine_eq_zero`),
replacing the earlier route through `genus_projectiveLine_eq_zero`. -/
instance instSubsingletonHolomorphicOneFormProjectiveLine :
    Subsingleton (HolomorphicOneForm ProjectiveLine) :=
  subsingleton_of_forall_eq 0 HolomorphicOneForm_projectiveLine_eq_zero

end Jacobians.ProjectiveCurve
