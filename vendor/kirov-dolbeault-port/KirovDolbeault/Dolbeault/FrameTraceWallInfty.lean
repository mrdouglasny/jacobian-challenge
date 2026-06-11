/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FrameTraceWallCluster

/-!
# Lemma 3.2 at infinity for the plain value trace (T lane)

The last analytic field of the residual wall `exists_frameTraceFunctionData_df`: the residue at
infinity of the value trace is the `∞`-fibre `frameRes` sum (the reciprocal-chart cluster
computation at the poles of the cover).

`valueTrace_resAtInfty_df` is currently the **single residual `sorry`** of the T lane; see the
discharge sketch in its docstring.
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FrameTraceWall

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatching
  Jacobians.MultiplicityPatchingConstruct Jacobians.MeromorphicTrace Jacobians.Dolbeault
  Jacobians.TraceResidue

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Engine extensions at an arbitrary centre value -/

/-- The sheet weight is the local degree at ANY centre value (incl. `∞`): the centre's slice of
its own fibre is the singleton of the sheet's fibre point. -/
theorem patch_m_eq_localDeg_w0 {f : MeromorphicFunction X} {w₀ : RiemannSphere}
    (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs) :
    P.m x = localDeg f w₀ x := by
  have h := P.sheetMult_eq x hx w₀ P.w₀_mem_W
  have hsing : P.U x ∩ f.toRiemannSphere ⁻¹' {w₀} = {x} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyU, hyfib⟩
      have hyxs : y ∈ P.xs := by
        have h1 : y ∈ (P.xs : Set X) := by rw [P.xs_coe]; exact hyfib
        exact h1
      by_contra hne
      exact Set.disjoint_iff.mp (P.U_pairwiseDisjoint y hyxs x hx hne)
        (Set.mem_inter (P.mem_U_self y hyxs) hyU)
    · rintro rfl
      have h1 : y ∈ (P.xs : Set X) := hx
      rw [P.xs_coe] at h1
      exact ⟨P.mem_U_self y hx, h1⟩
  rw [hsing] at h
  rw [← h, finsum_mem_singleton]

/-- The reciprocal-chart approach to `∞`: `coe ∘ (·)⁻¹` tends to `∞` along the punctured
neighbourhood of `0`. -/
theorem tendsto_coe_inv_infty :
    Tendsto (fun v : ℂ => (((v⁻¹ : ℂ)) : RiemannSphere)) (𝓝[≠] (0 : ℂ)) (𝓝 OnePoint.infty) :=
  Jacobians.RiemannSphere.tendsto_coe_cobounded_infty.comp tendsto_inv₀_nhdsNE_zero

/-! ## The `∞`-cluster descent

The mirror of `cluster_descent` at a pole `p` of the cover, read in the reciprocal value chart
`v = 1/w`: the slice sum over the fibre of `coe (v⁻¹)` is `−v²·H̃(v)` with `H̃` meromorphic at
`0` and `Res₀ H̃ = frameRes data F p`.  The straightening is the reciprocal normal form
`1/f̂ = ηᵐ` (`exists_reciprocal_NF` + `exists_clusterSplit`), the descended integrand is
`Q̃(u) = −u^{−2m}·Q(u)` (the reciprocal-chart Jacobian weight, constant along the rotated
sheets), and the residue chain matches the descent's `m·a₋ₘ(Q̃) = −m·aₘ(Q)` against the
`ω₀ = df` frame residue via `residueChangeOfVariables` along `η`. -/

/-- **The `∞`-cluster descent at a pole.** -/
theorem infCluster_descent (data : CanonicalForm17Data X) (F f : MeromorphicFunction X)
    (hω : data.ω₀ = differentialForm f) (hdiv : (f.div : Divisor X) ≠ 0)
    (P : MultiplicityPatchingData f OnePoint.infty) {p : X} (hp : p ∈ P.xs) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧
      (∀ᶠ v in 𝓝[≠] (0 : ℂ),
        (∑ y ∈ slice hdiv P p (v⁻¹), F.holoRepr y) = -v ^ 2 * H v) ∧
      resAt H 0 = frameRes data F p := by
  classical
  -- the pole and its order
  have hfib : f.toRiemannSphere p = OnePoint.infty := by
    have h1 : p ∈ (P.xs : Set X) := hp
    rwa [P.xs_coe] at h1
  have hp_pole : f.orderAtPoint p < 0 := by
    have h1 : p ∈ f.toRiemannSphere ⁻¹' {OnePoint.infty} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfib
    rwa [f.toRiemannSphere_preimage_infty] at h1
  -- the reciprocal normal form `1/f̂ = h`, `h = ηᵐ`
  obtain ⟨h, m, hm1, hm_eq, hh_an, hh_eq, hh0, hhord⟩ := exists_reciprocal_NF f hp_pole
  have hmpos : 0 < m := hm1
  have hm0 : m ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * π * Complex.I / m) with hζ_def
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  set pre : ℂ := (chartAt (H := ℂ) p) p with hpre_def
  have hpre_tgt : pre ∈ (chartAt (H := ℂ) p).target :=
    (chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p)
  have hord' : analyticOrderAt (fun w => h w - 0) pre = (m : ℕ∞) := by
    have hfn : (fun w => h w - 0) = h := by funext w; ring
    rw [hfn]; exact hhord
  obtain ⟨η, s, hη_an, hη0, hη', hNF, hs_an, hs0, hs', hηs, _⟩ :=
    exists_clusterSplit hmpos hh_an hh0 hord' hζ
  -- `η` is nonzero off the centre
  have hη_ne : ∀ᶠ ζ' in 𝓝[≠] pre, η ζ' ≠ 0 := by
    rcases hη_an.eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      have hconst : η =ᶠ[𝓝 pre] fun _ => 0 := hcase
      rw [hconst.deriv_eq, deriv_const] at hη'
      exact hη' rfl
    · exact hcase
  -- the straightened junk-free `F`-read and its weighted version
  have hFh_mero : MeromorphicAt (F.holoRepr ∘ (chartAt (H := ℂ) p).symm) pre :=
    (F.meromorphic p).congr (holoRepr_pullback_eventuallyEq_toFun F p hpre_tgt).symm
  set Q : ℂ → ℂ := fun a => F.holoRepr ((chartAt (H := ℂ) p).symm (s a)) with hQ_def
  have hQ_mero : MeromorphicAt Q 0 := by
    have h0 : MeromorphicAt (F.holoRepr ∘ (chartAt (H := ℂ) p).symm) (s 0) := by
      rw [hs0]; exact hFh_mero
    exact h0.comp_analyticAt hs_an
  set Qt : ℂ → ℂ := fun a => -((a - 0) ^ (-(2 * m : ℤ)) * Q a) with hQt_def
  have hQt_mero : MeromorphicAt Qt 0 :=
    ((meromorphicAt_zpow_self 0 (-(2 * m : ℤ))).mul hQ_mero).neg
  -- the descent of the weighted read
  obtain ⟨H, hH_mero, hH_eq, hH_res⟩ := meromorphicAt_plainSymSum_descent 0 hQt_mero hmpos hζ
  refine ⟨H, hH_mero, ?_, ?_⟩
  · -- THE GERM IDENTITY ------------------------------------------------------
    have hζj_ne : ∀ j : ℕ, (ζ : ℂ) ^ j ≠ 0 := fun j => pow_ne_zero j (hζ.ne_zero hm0)
    set yy : ℕ → ℂ → X := fun j u => (chartAt (H := ℂ) p).symm (s (ζ ^ j * u)) with hyy_def
    -- continuity of the sheet maps
    have hsmaps : ∀ j, Tendsto (fun u : ℂ => s (ζ ^ j * u)) (𝓝 0) (𝓝 pre) := by
      intro j
      have hmul : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
      have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
        have := hs_an.continuousAt.tendsto
        rwa [hs0] at this
      exact hs_t.comp hmul
    -- (b) η inverts `s` along each rotated ray
    have hb : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ), η (s (ζ ^ j * u)) = ζ ^ j * u := by
      intro j _
      have hcont : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
      exact hcont.eventually hηs
    -- (c) the reciprocal normal form along each sheet: `h (s (ζʲu)) = η(s(ζʲu))^m`
    have hc : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ),
        h (s (ζ ^ j * u)) = 0 + η (s (ζ ^ j * u)) ^ m := fun j _ =>
      (hsmaps j).eventually hNF
    -- (c') the junk-free read along each sheet: `(G (s (ζʲu)))⁻¹ = h (s (ζʲu))` off the centre
    have hGh : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        (f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u))))⁻¹ = h (s (ζ ^ j * u)) := by
      intro j hj
      -- the sheet value is off the centre for `u ≠ 0` (`η` reads `ζʲu ≠ 0` there)
      have hself : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hu
      have hbu : ∀ᶠ u in 𝓝[≠] (0 : ℂ), η (s (ζ ^ j * u)) = ζ ^ j * u :=
        (hb j hj).filter_mono nhdsWithin_le_nhds
      -- pull the punctured agreement `G⁻¹ =ᶠ h` along the sheet
      have hh_eq' : ∀ᶠ z in 𝓝[≠] pre,
          (f.holoRepr ((chartAt (H := ℂ) p).symm z))⁻¹ = h z := hh_eq
      rw [eventually_nhdsWithin_iff] at hh_eq' ⊢
      have hpull : ∀ᶠ u in 𝓝 (0 : ℂ), s (ζ ^ j * u) ∈ {ζ' | ζ' ∈ ({pre}ᶜ : Set ℂ) →
          (f.holoRepr ((chartAt (H := ℂ) p).symm ζ'))⁻¹ = h ζ'} :=
        (hsmaps j).eventually hh_eq'
      filter_upwards [hpull, hb j hj] with u h1 h2 hu0
      have hu0' : u ≠ 0 := hu0
      have hne_pre : s (ζ ^ j * u) ≠ pre := by
        intro hcontra
        have : η (s (ζ ^ j * u)) = 0 := by rw [hcontra, hη0]
        rw [h2] at this
        exact mul_ne_zero (hζj_ne j) hu0' this
      exact h1 (Set.mem_compl_singleton_iff.mpr hne_pre)
    -- (d) sheet membership / non-pole / chart-target facts
    have hpoles_open : IsOpen ({y : X | f.orderAtPoint y < 0} \ {p})ᶜ := by
      have hfin : ({y : X | f.orderAtPoint y < 0} \ {p}).Finite :=
        f.finite_poles.subset Set.diff_subset
      exact hfin.isClosed.isOpen_compl
    have hd : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ),
        yy j u ∈ P.U p ∧ yy j u ∈ ({y : X | f.orderAtPoint y < 0} \ {p})ᶜ ∧
          s (ζ ^ j * u) ∈ (chartAt (H := ℂ) p).target := by
      intro j _
      have hy_cont : Tendsto (yy j) (𝓝 0) (𝓝 p) := by
        have h2 : Tendsto (chartAt (H := ℂ) p).symm (𝓝 pre)
            (𝓝 ((chartAt (H := ℂ) p).symm pre)) :=
          ((chartAt (H := ℂ) p).continuousAt_symm hpre_tgt).tendsto
        have hcomp := h2.comp (hsmaps j)
        have hval : (chartAt (H := ℂ) p).symm pre = p :=
          (chartAt (H := ℂ) p).left_inv (mem_chart_source ℂ p)
        rw [hval] at hcomp
        exact hcomp
      have h1 : ∀ᶠ u in 𝓝 (0 : ℂ), yy j u ∈ P.U p :=
        hy_cont ((P.U_open p hp).mem_nhds (P.mem_U_self p hp))
      have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), yy j u ∈ ({y : X | f.orderAtPoint y < 0} \ {p})ᶜ := by
        refine hy_cont (hpoles_open.mem_nhds ?_)
        simp
      have h3 : ∀ᶠ u in 𝓝 (0 : ℂ), s (ζ ^ j * u) ∈ (chartAt (H := ℂ) p).target :=
        (hsmaps j).eventually ((chartAt (H := ℂ) p).open_target.mem_nhds hpre_tgt)
      filter_upwards [h1, h2, h3] with u u1 u2 u3
      exact ⟨u1, u2, u3⟩
    -- combine all eventual facts on the punctured `u`-disc
    have hall : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ((∑ j ∈ Finset.range m, Qt (ζ ^ j * u)) = H (0 + u ^ m)) ∧
        (∀ j ∈ Finset.range m, η (s (ζ ^ j * u)) = ζ ^ j * u) ∧
        (∀ j ∈ Finset.range m, h (s (ζ ^ j * u)) = 0 + η (s (ζ ^ j * u)) ^ m) ∧
        (∀ j ∈ Finset.range m,
          (f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u))))⁻¹ = h (s (ζ ^ j * u))) ∧
        (∀ j ∈ Finset.range m, yy j u ∈ P.U p ∧
          yy j u ∈ ({y : X | f.orderAtPoint y < 0} \ {p})ᶜ ∧
          s (ζ ^ j * u) ∈ (chartAt (H := ℂ) p).target) := by
      have h2 := (eventually_all_finset (Finset.range m)).mpr hb
      have h3 := (eventually_all_finset (Finset.range m)).mpr hc
      have h4 := (eventually_all_finset (Finset.range m)).mpr hGh
      have h5 := (eventually_all_finset (Finset.range m)).mpr hd
      filter_upwards [hH_eq, h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono
        nhdsWithin_le_nhds, h4, h5.filter_mono nhdsWithin_le_nhds] with u u1 u2 u3 u4 u5
      exact ⟨u1, u2, u3, u4, u5⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hall
    obtain ⟨δ, hδ0, hδ⟩ := hall
    -- the conclusion, for `v` in the punctured disc of radius `min (δ^m) 1` with the
    -- patching-neighbourhood condition
    have hWev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), (((v⁻¹ : ℂ)) : RiemannSphere) ∈ P.W :=
      tendsto_coe_inv_infty.eventually (P.W_open.mem_nhds P.w₀_mem_W)
    have hsmall : ∀ᶠ v in 𝓝[≠] (0 : ℂ), dist v 0 < δ ^ m :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds (0 : ℂ) (pow_pos hδ0 m))
    filter_upwards [hWev, hsmall, self_mem_nhdsWithin] with v hWv hvd hv0'
    have hv0 : v ≠ 0 := hv0'
    -- pick an `m`-th root `u` of `v`
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq v hmpos
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow hm0] at hu
      exact hv0 hu.symm
    have hud : dist u 0 < δ := by
      rw [dist_zero_right]
      have h1 : ‖u‖ ^ m < δ ^ m := by
        rw [← norm_pow, hu]
        simpa [dist_eq_norm] using hvd
      exact lt_of_pow_lt_pow_left₀ m hδ0.le h1
    obtain ⟨hΨ1, hΨ2, hΨ3, hΨ4, hΨ5⟩ := hδ hud (Set.mem_compl_singleton_iff.mpr hu0)
    -- the sheet points lie on the fibre of `coe (v⁻¹)`
    have hyfib : ∀ j ∈ Finset.range m,
        f.toRiemannSphere (yy j u) = (((v⁻¹ : ℂ)) : RiemannSphere) := by
      intro j hj
      -- the junk-free read takes the value `v⁻¹`
      have hread : f.holoRepr (yy j u) = v⁻¹ := by
        have h1 : (f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u))))⁻¹
            = h (s (ζ ^ j * u)) := hΨ4 j hj
        have h2 : h (s (ζ ^ j * u)) = v := by
          rw [hΨ3 j hj, hΨ2 j hj, zero_add, mul_pow, ← pow_mul, mul_comm j m, pow_mul,
            hζ.pow_eq_one, one_pow, one_mul, hu]
        rw [h2] at h1
        have hG_ne : f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u))) ≠ 0 := by
          intro hzero
          rw [hzero] at h1
          rw [inv_zero] at h1
          exact hv0 h1.symm
        show f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u))) = v⁻¹
        rw [← h1, inv_inv]
      -- the sheet point is a non-pole (off the isolated pole `p` and the other poles)
      have hne_pre : s (ζ ^ j * u) ≠ pre := by
        intro hcontra
        have h1 : η (s (ζ ^ j * u)) = 0 := by rw [hcontra, hη0]
        rw [hΨ2 j hj] at h1
        exact mul_ne_zero (hζj_ne j) hu0 h1
      have hne_p : yy j u ≠ p := by
        intro hcontra
        have h1 := congrArg (chartAt (H := ℂ) p) hcontra
        have h2 : (chartAt (H := ℂ) p) ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u)))
            = s (ζ ^ j * u) := (chartAt (H := ℂ) p).right_inv (hΨ5 j hj).2.2
        rw [h2] at h1
        exact hne_pre h1
      have hnp : 0 ≤ f.orderAtPoint (yy j u) := by
        have h1 := (hΨ5 j hj).2.1
        rw [Set.mem_compl_iff, Set.mem_diff] at h1
        push Not at h1
        by_contra hlt
        exact hne_p (h1 (not_le.mp hlt))
      rw [f.toRiemannSphere_of_nonneg hnp, hread]
    -- the sheet points are distinct
    have hy_inj : Set.InjOn (fun j => yy j u) (Finset.range m : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have hi' : i ∈ Finset.range m := Finset.mem_range.mpr hi
      have hj' : j ∈ Finset.range m := Finset.mem_range.mpr hj
      have hs_eq : s (ζ ^ i * u) = s (ζ ^ j * u) := by
        have h1 := congrArg (chartAt (H := ℂ) p) hij
        have h2 : (chartAt (H := ℂ) p) ((chartAt (H := ℂ) p).symm (s (ζ ^ i * u)))
            = s (ζ ^ i * u) := (chartAt (H := ℂ) p).right_inv (hΨ5 i hi').2.2
        have h3 : (chartAt (H := ℂ) p) ((chartAt (H := ℂ) p).symm (s (ζ ^ j * u)))
            = s (ζ ^ j * u) := (chartAt (H := ℂ) p).right_inv (hΨ5 j hj').2.2
        rwa [h2, h3] at h1
      have hζu : ζ ^ i * u = ζ ^ j * u := by
        rw [← hΨ2 i hi', ← hΨ2 j hj', hs_eq]
      exact hζ.pow_inj hi hj (mul_right_cancel₀ hu0 hζu)
    set cand : Finset X := (Finset.range m).image (fun j => yy j u) with hcand_def
    have hcand_card : cand.card = m := by
      rw [hcand_def, Finset.card_image_of_injOn hy_inj, Finset.card_range]
    have hcand_sub : cand ⊆ slice hdiv P p (v⁻¹) := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact mem_slice.mpr ⟨hyfib j hj, (hΨ5 j hj).1⟩
    have hmP : P.m p = (m : ℤ) := by
      rw [patch_m_eq_localDeg_w0 P hp, localDeg_infty, ← hm_eq]
    have hslice : slice hdiv P p (v⁻¹) = cand :=
      slice_eq_of_exhibited hdiv P hp hWv cand hcand_sub (by rw [hmP, hcand_card])
    -- assemble: the slice sum is `−v²·H(v)` through the weighted descent
    rw [hslice, hcand_def, Finset.sum_image (fun i hi j hj h' => hy_inj hi hj h')]
    have hsum : ∑ j ∈ Finset.range m, F.holoRepr (yy j u)
        = ∑ j ∈ Finset.range m, Q (ζ ^ j * u) := rfl
    -- `Qt (ζʲu) = −u^{−2m}·Q(ζʲu)` (the weight is rotation-invariant)
    have hQt_rot : ∀ j ∈ Finset.range m,
        Qt (ζ ^ j * u) = -((u : ℂ) ^ (-(2 * m : ℤ)) * Q (ζ ^ j * u)) := by
      intro j _
      show -(((ζ ^ j * u) - 0) ^ (-(2 * m : ℤ)) * Q (ζ ^ j * u)) = _
      have hζpow : ((ζ : ℂ) ^ j) ^ (-(2 * m : ℤ)) = 1 := by
        have h1 : ((ζ : ℂ) ^ j) ^ (2 * m) = 1 := by
          rw [← pow_mul, show j * (2 * m) = m * (2 * j) by ring, pow_mul,
            hζ.pow_eq_one, one_pow]
        rw [show (-(2 * m : ℤ)) = -((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast, h1, inv_one]
      rw [sub_zero, mul_zpow, hζpow, one_mul]
    -- collapse the weighted sum
    have hsumQt : ∑ j ∈ Finset.range m, Qt (ζ ^ j * u)
        = -((u : ℂ) ^ (-(2 * m : ℤ)) * ∑ j ∈ Finset.range m, Q (ζ ^ j * u)) := by
      rw [Finset.sum_congr rfl hQt_rot, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
    have hHval : H (u ^ m)
        = -((u : ℂ) ^ (-(2 * m : ℤ)) * ∑ j ∈ Finset.range m, Q (ζ ^ j * u)) := by
      rw [← hsumQt, hΨ1, zero_add]
    rw [hsum, ← hu]
    -- goal: `∑ Q = -(u^m)^2 * H (u^m)`
    rw [hHval]
    rw [neg_mul_neg, ← pow_mul]
    rw [show (u : ℂ) ^ (m * 2) = (u : ℂ) ^ ((2 * m : ℕ) : ℤ) from by
      rw [zpow_natCast]; ring_nf]
    rw [← mul_assoc, ← zpow_add₀ hu0]
    rw [show ((2 * m : ℕ) : ℤ) + (-(2 * m : ℤ)) = 0 from by push_cast; ring, zpow_zero, one_mul]
  · -- THE RESIDUE IDENTIFICATION ---------------------------------------------
    -- trace side: `Res₀ H = m·a₋ₘ(Q̃) = −m·aₘ(Q)`
    have hQt_coeff : planarCoeff (-(m : ℤ)) Qt 0 = -planarCoeff ((m : ℤ)) Q 0 := by
      have hmono_mero : MeromorphicAt (fun a => (a - 0) ^ (-(2 * m : ℤ)) * Q a) 0 :=
        (meromorphicAt_zpow_self 0 _).mul hQ_mero
      have hneg : Qt = (-1 : ℂ) • (fun a => (a - 0) ^ (-(2 * m : ℤ)) * Q a) := by
        funext a
        simp [hQt_def]
      rw [hneg, planarCoeff_smul (-1) hmono_mero,
        planarCoeff_monomial_mul (-(2 * m : ℤ)) (-(m : ℤ)) hQ_mero,
        show (-(m : ℤ)) - (-(2 * m : ℤ)) = (m : ℤ) by ring]
      ring
    have htrace_res : resAt H 0 = -((m : ℂ) * planarCoeff ((m : ℤ)) Q 0) := by
      rw [resAt_eq_planarCoeff_neg_one hH_mero, hH_res, hQt_coeff]
      ring
    -- the local left inverse of `η` certifies `s ∘ η = id` near `pre`
    have hsd : HasStrictDerivAt η (deriv η pre) pre := hη_an.hasStrictDerivAt
    have hlinv : ∀ᶠ ζ' in 𝓝 pre, hsd.localInverse η (deriv η pre) pre hη' (η ζ') = ζ' :=
      hsd.eventually_left_inverse hη'
    obtain ⟨V, hV_mem, hV⟩ := Filter.eventually_iff_exists_mem.mp hlinv
    have hηt : Tendsto η (𝓝 pre) (𝓝 0) := by
      have := hη_an.continuousAt.tendsto
      rwa [hη0] at this
    have hsη : ∀ᶠ ζ' in 𝓝 pre, s (η ζ') = ζ' := by
      have h1 : ∀ᶠ ζ' in 𝓝 pre, η (s (η ζ')) = η ζ' := hηt.eventually hηs
      have h2 : ∀ᶠ ζ' in 𝓝 pre, s (η ζ') ∈ V := by
        have hst : Tendsto (fun ζ' => s (η ζ')) (𝓝 pre) (𝓝 pre) := by
          have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
            have := hs_an.continuousAt.tendsto
            rwa [hs0] at this
          exact hs_t.comp hηt
        exact hst.eventually hV_mem
      filter_upwards [h1, h2, hlinv] with ζ' h1' h2' h3'
      have ha := hV _ h2'
      rw [h1'] at ha
      rw [← ha]
      exact h3'
    -- the straightened branch integrand at the pole: `At(u) = Q(u)·(−m)·u^{−m−1}`
    set At : ℂ → ℂ := fun a => Q a * ((-(m : ℂ)) * (a - 0) ^ (-(m : ℤ) - 1)) with hAt_def
    have hAt_mero : MeromorphicAt At 0 :=
      hQ_mero.mul ((MeromorphicAt.const _ 0).mul (meromorphicAt_zpow_self 0 (-(m : ℤ) - 1)))
    -- the integrand chain
    have hev : (fun ζ' => F.toFun ((chartAt (H := ℂ) p).symm ζ')
          * deriv (f.toFun ∘ (chartAt (H := ℂ) p).symm) ζ')
        =ᶠ[𝓝[≠] pre] (fun ζ' => At (η ζ') * deriv η ζ') := by
      -- (R1) junk-free `F` read
      have hR1 : (fun ζ' => F.toFun ((chartAt (H := ℂ) p).symm ζ'))
          =ᶠ[𝓝[≠] pre] (fun ζ' => F.holoRepr ((chartAt (H := ℂ) p).symm ζ')) :=
        (holoRepr_pullback_eventuallyEq_toFun F p hpre_tgt).symm
      -- (R2') the `f`-read is the reciprocal of the repaired normal form
      have hGinv : (fun ζ' => f.holoRepr ((chartAt (H := ℂ) p).symm ζ'))
          =ᶠ[𝓝[≠] pre] (fun ζ' => (h ζ')⁻¹) := by
        filter_upwards [hh_eq] with ζ' h1
        rw [← h1, inv_inv]
      have hR2 : deriv (f.toFun ∘ (chartAt (H := ℂ) p).symm)
          =ᶠ[𝓝[≠] pre] deriv (fun ζ' => (h ζ')⁻¹) := by
        refine Jacobians.Dolbeault.deriv_eventuallyEq_punctured ?_
        exact ((holoRepr_pullback_eventuallyEq_toFun f p hpre_tgt).symm).trans hGinv
      -- (R3') the reciprocal normal-form derivative
      have hR3 : deriv (fun ζ' => (h ζ')⁻¹)
          =ᶠ[𝓝[≠] pre] (fun ζ' => (-(m : ℂ)) * η ζ' ^ (-(m : ℤ) - 1) * deriv η ζ') := by
        have hNFinv : (fun ζ' => (h ζ')⁻¹) =ᶠ[𝓝 pre] (fun w => ((0 : ℂ) + η w ^ m)⁻¹) := by
          filter_upwards [hNF] with w hw
          rw [hw]
        have hd := hNFinv.deriv
        have hcalc : ∀ᶠ ζ' in 𝓝[≠] pre,
            deriv (fun w => ((0 : ℂ) + η w ^ m)⁻¹) ζ'
              = (-(m : ℂ)) * η ζ' ^ (-(m : ℤ) - 1) * deriv η ζ' := by
          filter_upwards [(hη_an.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
            hη_ne] with ζ' hζ'an hζ'ne
          have hpow : HasDerivAt (fun w => η w ^ m)
              ((m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ') ζ' :=
            hζ'an.differentiableAt.hasDerivAt.pow m
          have hpm_ne : η ζ' ^ m ≠ 0 := pow_ne_zero m hζ'ne
          have hinv : HasDerivAt (fun w => ((0 : ℂ) + η w ^ m)⁻¹)
              (-((m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ') / ((0 : ℂ) + η ζ' ^ m) ^ 2) ζ' := by
            have h0 : HasDerivAt (fun w => (0 : ℂ) + η w ^ m)
                ((m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ') ζ' := by
              simpa using hpow.const_add (0 : ℂ)
            exact h0.inv (by simpa using hpm_ne)
          rw [hinv.deriv]
          rw [zero_add]
          -- `−(m·η^{m−1}·η′)/(η^m)² = −m·η^{−m−1}·η′`
          have hzp : (η ζ' : ℂ) ^ (-(m : ℤ) - 1)
              = η ζ' ^ (m - 1) / (η ζ' ^ m) ^ 2 := by
            rw [← pow_mul]
            rw [show (η ζ' : ℂ) ^ (m - 1) = η ζ' ^ (((m - 1 : ℕ) : ℤ)) from
              (zpow_natCast _ _).symm,
              show (η ζ' : ℂ) ^ (m * 2) = η ζ' ^ ((m * 2 : ℕ) : ℤ) from
              (zpow_natCast _ _).symm,
              ← zpow_sub₀ hζ'ne]
            congr 1
            push_cast
            omega
          rw [hzp]
          ring
        filter_upwards [hd.filter_mono nhdsWithin_le_nhds, hcalc] with ζ' h1 h2
        rw [h1, h2]
      -- (R4') the `F`-read through the straightening
      have hR4 : (fun ζ' => F.holoRepr ((chartAt (H := ℂ) p).symm ζ'))
          =ᶠ[𝓝 pre] (fun ζ' => Q (η ζ')) := by
        filter_upwards [hsη] with ζ' hζ'
        show F.holoRepr ((chartAt (H := ℂ) p).symm ζ')
          = F.holoRepr ((chartAt (H := ℂ) p).symm (s (η ζ')))
        rw [hζ']
      filter_upwards [hR1, hR2, hR3, hR4.filter_mono nhdsWithin_le_nhds]
        with ζ' h1 h2 h3 h4
      show F.toFun ((chartAt (H := ℂ) p).symm ζ')
          * deriv (f.toFun ∘ (chartAt (H := ℂ) p).symm) ζ' = At (η ζ') * deriv η ζ'
      rw [show F.toFun ((chartAt (H := ℂ) p).symm ζ')
          = F.holoRepr ((chartAt (H := ℂ) p).symm ζ') from h1, h2, h3, h4]
      show Q (η ζ') * ((-(m : ℂ)) * η ζ' ^ (-(m : ℤ) - 1) * deriv η ζ')
          = Q (η ζ') * ((-(m : ℂ)) * (η ζ' - 0) ^ (-(m : ℤ) - 1)) * deriv η ζ'
      rw [sub_zero]
      ring
    -- chain the bridges
    have hAη_mero : MeromorphicAt (fun ζ' => At (η ζ') * deriv η ζ') pre := by
      have h1 : MeromorphicAt (At ∘ η) pre := by
        have hA0 : MeromorphicAt At (η pre) := by rw [hη0]; exact hAt_mero
        exact hA0.comp_analyticAt hη_an
      exact h1.mul hη_an.deriv.meromorphicAt
    have hCoV : resAt (fun ζ' => At (η ζ') * deriv η ζ') pre = resAt At (η pre) :=
      Jacobians.MeromorphicTrace.residueChangeOfVariables η At pre hη_an hη'
        (by rw [hη0]; exact hAt_mero)
    -- the branch read of `At`
    have hbranch : planarCoeff (-1) At 0 = -((m : ℂ) * planarCoeff ((m : ℤ)) Q 0) := by
      have hswap : At = (-(m : ℂ)) • (fun a => (a - 0) ^ (-(m : ℤ) - 1) * Q a) := by
        funext a
        simp only [hAt_def, Pi.smul_apply, smul_eq_mul]
        ring
      have hmono : MeromorphicAt (fun a => (a - 0) ^ (-(m : ℤ) - 1) * Q a) 0 :=
        (meromorphicAt_zpow_self 0 (-(m : ℤ) - 1)).mul hQ_mero
      rw [hswap, planarCoeff_smul (-(m : ℂ)) hmono,
        planarCoeff_monomial_mul (-(m : ℤ) - 1) (-1) hQ_mero,
        show (-1 : ℤ) - (-(m : ℤ) - 1) = (m : ℤ) by ring]
      ring
    -- assemble
    rw [htrace_res, frameRes_df_read data f F hω p, planarCoeff_congr hev (-1),
      ← resAt_eq_planarCoeff_neg_one hAη_mero, hCoV, hη0,
      resAt_eq_planarCoeff_neg_one hAt_mero, hbranch]

/-- **[RESIDUAL — single named `sorry`] Lemma 3.2 at `∞` for the plain value trace.**  On a
contour enclosing all exceptional values of the `ω₀ = df` value trace, the residue at infinity
is the `∞`-fibre `frameRes` sum (over the poles of the cover).  (NOT VERIFIED — Miranda
§VIII.3, the reciprocal-chart cluster computation: over `w` large the fibre clusters at the
poles of `f`; per pole of order `e`, the reciprocal normal form `1/f̂ = ηᵉ`
(`exists_reciprocal_NF`) and the unweighted symmetric descent give `T(w) = H(1/w)` with `H`
meromorphic at `0`; the contour integral picks out `−a₁(H)`, which the branch normalization
identifies with the `frameRes` sum.) -/
theorem valueTrace_resAtInfty_df (data : CanonicalForm17Data X) (F f : MeromorphicFunction X)
    (hω : data.ω₀ = differentialForm f) (hdiv : (f.div : Divisor X) ≠ 0)
    (C : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (hoff : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ (valueTrace F f) z) :
    resAtInfty (valueTrace F f) ρ
      = ∑ y ∈ fibreFinset f hdiv OnePoint.infty, frameRes data F y := by
  sorry

end Jacobians.Dolbeault.FrameTraceWall

end
