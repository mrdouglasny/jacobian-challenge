/-
Concrete witnesses for `AX_AnalyticCycleBasis` on `Elliptic ω₁ ω₂ h`.

## What this module provides

Given `genus (Elliptic ω₁ ω₂ h) = 1` (from `AX_genus_Elliptic_eq_one`)
the classical construction of a symplectic basis of `H_1` uses the
two generators of the lattice `Λ = ℤω₁ + ℤω₂`, projected down to the
torus:

* **A-cycle**: `A(r) := [r · ω₁]` in `ℂ / Λ`. Closed because
  `[0] = [ω₁]` (both in the identity class modulo `Λ`).
* **B-cycle**: `B(r) := [r · ω₂]`, analogous.

These are piecewise-real-analytic (in fact linear) in `r`. Their
homology classes form a ℤ-basis of `H_1(Elliptic, ℤ)` symplectic with
respect to the intersection form: `⟨A, A⟩ = ⟨B, B⟩ = 0`, `⟨A, B⟩ = 1`.

## What this module axiomatizes

Three Elliptic-specific axioms wrap the detailed classical facts that
would require substantial covering-space / fundamental-group
infrastructure to prove:

* `AX_Elliptic_aLoop_analytic`: the A-cycle is `IsAnalyticArcStrong`.
* `AX_Elliptic_bLoop_analytic`: the B-cycle is `IsAnalyticArcStrong`.
* `AX_Elliptic_H1_symplectic`: their classes form a symplectic
  `Module.Basis (Fin 2) ℤ (H_1 (Elliptic _) _)` with the desired
  α/β pairing.

Each axiom retires when (a) analyticity is verified against
ComplexTorus's chart atlas (chart transitions are translations, fderiv
is 1), and (b) the deck-transformation / covering-space description of
`π₁(ℂ/Λ) = Λ ≃ ℤ²` is available.

## The witness

`ellipticCycleBasis` assembles the three axioms into a concrete
`AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0` term. Non-vacuous and
traceable — axiom dependencies auditable via `lean_verify`.

See `docs/completion-plan.md` workstream C2.
-/
import Jacobians.ProjectiveCurve.Elliptic.Genus
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.Axioms.AnalyticCycleBasis

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.Axioms Jacobians.AbelianVariety

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

/-- The A-cycle of an elliptic curve, as a real-parameter path:
`A(r) = [r · ω₁]` in `ℂ / Λ`. Linear in `r`, hence trivially continuous.
Uses complex multiplication `(r : ℂ) * ω₁` to sidestep
`ContinuousSMul ℝ ℂ` synthesis. -/
noncomputable def aLoopExtend : ℝ → Elliptic ω₁ ω₂ h :=
  fun r => (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup) ((r : ℂ) * ω₁)

/-- The B-cycle: `B(r) = [r · ω₂]`. -/
noncomputable def bLoopExtend : ℝ → Elliptic ω₁ ω₂ h :=
  fun r => (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup) ((r : ℂ) * ω₂)

lemma continuous_aLoopExtend : Continuous (aLoopExtend ω₁ ω₂ h) := by
  unfold aLoopExtend
  exact continuous_quotient_mk'.comp
    (Complex.continuous_ofReal.mul continuous_const)

lemma continuous_bLoopExtend : Continuous (bLoopExtend ω₁ ω₂ h) := by
  unfold bLoopExtend
  exact continuous_quotient_mk'.comp
    (Complex.continuous_ofReal.mul continuous_const)

private lemma extChartAt_trans_analyticAt_aux {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hmem : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
  have : z ∈ ((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) p).source := by
    simp_all
  have : ContDiffWithinAt ℂ ω (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm)
      (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) _ _ this
  have : ContDiffAt ℂ ω (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
    simp_all [contDiffWithinAt_univ]
  exact this.analyticAt.restrictScalars

private lemma aLoopExtend_fixedChart_analyticAt
    {p : Elliptic ω₁ ω₂ h} {r : ℝ}
    (hr : aLoopExtend ω₁ ω₂ h r ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (aLoopExtend ω₁ ω₂ h u)) r := by
  let q := aLoopExtend ω₁ ω₂ h r
  have h₁ : AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (aLoopExtend ω₁ ω₂ h u)) r := by
    simpa [q, aLoopExtend, Elliptic, QuotientAddGroup.mk'_apply] using
      (ComplexTorus.extChartAt_quotient_mk_line_analyticAt
        (L := ellipticLattice ω₁ ω₂ h)
        (p := q) (v := ω₁) (r := r) (by
          simp [q, aLoopExtend, QuotientAddGroup.mk'_apply]))
  have h₂ : q ∈ (extChartAt 𝓘(ℂ) q).source := mem_extChartAt_source q
  have h₃ : (extChartAt 𝓘(ℂ) q) q ∈ (extChartAt 𝓘(ℂ) q).target :=
    (extChartAt 𝓘(ℂ) q).map_source h₂
  have :
      (extChartAt 𝓘(ℂ) q).symm ((extChartAt 𝓘(ℂ) q) q) ∈
        (extChartAt 𝓘(ℂ) p).source := by
    rwa [(extChartAt 𝓘(ℂ) q).left_inv h₂]
  have : AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm)
        ((extChartAt 𝓘(ℂ) q) q) :=
    extChartAt_trans_analyticAt_aux h₃ this
  have : AnalyticAt ℝ
      (((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) ∘
        (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (aLoopExtend ω₁ ω₂ h u))) r :=
    this.comp_of_eq h₁ (by simp [q])
  refine this.congr ?_
  have :
      ∀ᶠ u in 𝓝 r, aLoopExtend ω₁ ω₂ h u ∈ (extChartAt 𝓘(ℂ) q).source := by
    exact (continuous_aLoopExtend ω₁ ω₂ h).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℂ)) q).mem_nhds h₂)
  filter_upwards [this] with u hu
  simp_all

private lemma bLoopExtend_fixedChart_analyticAt
    {p : Elliptic ω₁ ω₂ h} {r : ℝ}
    (hr : bLoopExtend ω₁ ω₂ h r ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (bLoopExtend ω₁ ω₂ h u)) r := by
  let q := bLoopExtend ω₁ ω₂ h r
  have h₁ : AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (bLoopExtend ω₁ ω₂ h u)) r := by
    simpa [q, bLoopExtend, Elliptic, QuotientAddGroup.mk'_apply] using
      (ComplexTorus.extChartAt_quotient_mk_line_analyticAt
        (L := ellipticLattice ω₁ ω₂ h)
        (p := q) (v := ω₂) (r := r) (by
          simp [q, bLoopExtend, QuotientAddGroup.mk'_apply]))
  have h₂ : q ∈ (extChartAt 𝓘(ℂ) q).source := mem_extChartAt_source q
  have h₃ : (extChartAt 𝓘(ℂ) q) q ∈ (extChartAt 𝓘(ℂ) q).target :=
    (extChartAt 𝓘(ℂ) q).map_source h₂
  have :
      (extChartAt 𝓘(ℂ) q).symm ((extChartAt 𝓘(ℂ) q) q) ∈
        (extChartAt 𝓘(ℂ) p).source := by
    rwa [(extChartAt 𝓘(ℂ) q).left_inv h₂]
  have : AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm)
        ((extChartAt 𝓘(ℂ) q) q) :=
    extChartAt_trans_analyticAt_aux h₃ this
  have : AnalyticAt ℝ
      (((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) ∘
        (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (bLoopExtend ω₁ ω₂ h u))) r :=
    this.comp_of_eq h₁ (by simp [q])
  refine this.congr ?_
  have :
      ∀ᶠ u in 𝓝 r, bLoopExtend ω₁ ω₂ h u ∈ (extChartAt 𝓘(ℂ) q).source := by
    exact (continuous_bLoopExtend ω₁ ω₂ h).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℂ)) q).mem_nhds h₂)
  filter_upwards [this] with u hu
  simp_all

private lemma no_mem_between_orderEmb_succ (Pset : Finset ℝ) {m : ℕ}
    (hcard : Pset.card = m + 1) (i : Fin m) {x : ℝ}
    (hx : x ∈ Pset)
    (hbetween : Pset.orderEmbOfFin hcard i.castSucc < x ∧
      x < Pset.orderEmbOfFin hcard i.succ) : False := by
  have : x ∈ Set.range (Pset.orderEmbOfFin hcard) := by simp_all
  obtain ⟨j, rfl⟩ := this
  have := ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.1
  have := ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.2
  grind

private lemma exists_l0_cell_of_refined_cell {n0 m : ℕ}
    {t : Fin (n0 + 1) → ℝ} {Pset : Finset ℝ} (hzero : t 0 = 0)
    (hlast : t (Fin.last n0) = 1)
    (hPbase : ∀ j : Fin (n0 + 1), t j ∈ Pset)
    (hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1)
    (hcard : Pset.card = m + 1) (i : Fin m) :
    ∃ j : Fin n0,
      Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (t j.castSucc) (t j.succ) := by
  classical
  let a := Pset.orderEmbOfFin hcard i.castSucc
  let b := Pset.orderEmbOfFin hcard i.succ
  have : a ∈ Pset := by simp [a]
  have h₀ : 0 ≤ a := (hPsubset this).1
  have : b ∈ Pset := by simp [b]
  have h₁ : b ≤ 1 := (hPsubset this).2
  have : i.castSucc < i.succ := by
    simp
  have : a < b := (Pset.orderEmbOfFin hcard).strictMono this
  have : ∀ {x : ℝ}, x ∈ Pset → ¬ (a < x ∧ x < b) := by
    intro x hx hxbetween
    exact no_mem_between_orderEmb_succ Pset hcard i hx (by grind)
  let J : Finset (Fin (n0 + 1)) := Finset.univ.filter (fun k => t k ≤ a)
  have : J.Nonempty := ⟨0, by simp [J, hzero, h₀]⟩
  let k : Fin (n0 + 1) := J.max' this
  have : k ∈ J := Finset.max'_mem J this
  have : t k ≤ a := (Finset.mem_filter.mp this).2
  have : k ≠ Fin.last n0 := by grind
  have : k.val < n0 := by grind
  let j : Fin n0 := ⟨k.val, this⟩
  have : j.castSucc = k := by grind
  have : t j.castSucc ≤ a := by simp_all
  have : b ≤ t j.succ := by
    have : ¬ t j.succ ≤ a := by
      intro hsucc_le_a
      have : j.succ ∈ J := by simp [J, hsucc_le_a]
      have : j.succ ≤ k := Finset.le_max' J (j.succ) this
      grind
    grind
  grind

private lemma exists_adjacent_index_of_no_between {Pset : Finset ℝ} {n : ℕ}
    (hcard : Pset.card = n + 1) {s t : ℝ}
    (hs : s ∈ Pset) (ht : t ∈ Pset) (hst : s < t)
    (hno : ∀ r ∈ Pset, r ∉ Set.Ioo s t) :
    ∃ i : Fin n,
      s = Pset.orderEmbOfFin hcard i.castSucc ∧
      t = Pset.orderEmbOfFin hcard i.succ := by
  have : s ∈ Set.range (Pset.orderEmbOfFin hcard) := by simp_all
  obtain ⟨is, rfl⟩ := this
  have : t ∈ Set.range (Pset.orderEmbOfFin hcard) := by simp_all
  obtain ⟨it, rfl⟩ := this
  have := ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hst
  have : is.val < it.val := by simp_all
  have hsucc_eq : it.val = is.val + 1 := by
    by_contra
    have hgap : is.val + 1 < it.val := by grind
    have : is.val + 1 < n + 1 := lt_of_lt_of_le hgap (le_of_lt it.2)
    let k : Fin (n + 1) := ⟨is.val + 1, this⟩
    have his_k : is < k := by
      simp [Fin.lt_def, k]
    have hk_it : k < it := by
      simp [Fin.lt_def, k, hgap]
    have :
        Pset.orderEmbOfFin hcard is < Pset.orderEmbOfFin hcard k ∧
          Pset.orderEmbOfFin hcard k < Pset.orderEmbOfFin hcard it :=
      ⟨(Pset.orderEmbOfFin hcard).strictMono his_k,
        (Pset.orderEmbOfFin hcard).strictMono hk_it⟩
    have : Pset.orderEmbOfFin hcard k ∈ Pset := by simp
    grind
  have : is.val < n := by grind
  let i : Fin n := ⟨is.val, this⟩
  have : is = i.castSucc := Fin.ext (by simp [i])
  grind

/-- **Axiom.** The A-cycle is strongly piecewise-real-analytic.

Classical: linear in `r`, hence real-analytic after refining the base cell
`[0, 1]` into sufficiently short chart-local subsegments. For the corrected
refinement-based `IsAnalyticArcStrong`, the `{0, 1}` base partition asks only for
some finite refinement `τ`; each refined cell fits inside one ComplexTorus chart,
where the chart-pullback of `r ↦ [r • ω₁]` is affine in `r`.

(NOT VERIFIED — refinement form, discharge to theorem is a follow-up.) -/
theorem AX_Elliptic_aLoop_analytic :
    IsAnalyticArcStrong (Elliptic ω₁ ω₂ h) (aLoopExtend ω₁ ω₂ h) {0, 1} := by
  intro _ ha _ hb _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with hb | rfl
    · simp_all
    · let c : Elliptic ω₁ ω₂ h → Set unitInterval :=
        fun x ↦ {u | aLoopExtend ω₁ ω₂ h u ∈ (chartAt ℂ x).source}
      have hc_open : ∀ x, IsOpen (c x) := by
        intro x
        exact (chartAt ℂ x).open_source.preimage
          ((continuous_aLoopExtend ω₁ ω₂ h).comp continuous_subtype_val)
      have : Set.univ ⊆ ⋃ x, c x := by
        intro u _
        exact Set.mem_iUnion.2
          ⟨aLoopExtend ω₁ ω₂ h (u : ℝ),
            mem_chart_source ℂ (aLoopExtend ω₁ ω₂ h (u : ℝ))⟩
      obtain ⟨t0, ht_zero, ht_mono, ⟨m, ht_eventually_one⟩, ht_sub⟩ :=
        exists_monotone_Icc_subset_open_cover_unitInterval hc_open this
      let n0 : ℕ := m + 1
      let tau0 : Fin (n0 + 1) → ℝ := fun i ↦ (t0 i.val : ℝ)
      let p0 : Fin n0 → Elliptic ω₁ ω₂ h := fun i ↦ Classical.choose (ht_sub i.val)
      have ht0_zero : tau0 0 = 0 := by
        simpa [tau0] using congrArg Subtype.val ht_zero
      have ht0_last : tau0 (Fin.last n0) = 1 := by
        have hlast := ht_eventually_one (m + 1) (Nat.le_succ m)
        simpa [tau0, n0, Fin.val_last] using congrArg Subtype.val hlast
      have : Monotone tau0 := by
        intro i j hij
        exact (ht_mono (Fin.val_le_of_le hij) : (t0 i.val : ℝ) ≤ (t0 j.val : ℝ))
      have hmem : ∀ i : Fin n0, ∀ u ∈ Set.Icc (tau0 i.castSucc) (tau0 i.succ),
          aLoopExtend ω₁ ω₂ h u ∈ (chartAt ℂ (p0 i)).source := by
        intro i u hu
        have hleft : (t0 i.val : ℝ) ≤ u := by simpa [tau0, Fin.val_castSucc] using hu.1
        have : u ≤ (t0 (i.val + 1) : ℝ) := by simpa [tau0, Fin.val_succ] using hu.2
        let uI : unitInterval :=
          ⟨u, ⟨(t0 i.val).2.1.trans hleft, this.trans (t0 (i.val + 1)).2.2⟩⟩
        have : uI ∈ Set.Icc (t0 i.val) (t0 (i.val + 1)) := ⟨hleft, this⟩
        grind
      let base := Finset.image tau0 Finset.univ
      let Pset := base
      have hbase_mem : ∀ j : Fin (n0 + 1), tau0 j ∈ Pset := by grind
      have hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1 := by grind
      have hzeroP : (0 : ℝ) ∈ Pset := by grind
      have honeP : (1 : ℝ) ∈ Pset := by grind
      have : Pset.Nonempty := ⟨0, hzeroP⟩
      have := Finset.card_pos.mpr this
      let n := Pset.card - 1
      have hcard : Pset.card = n + 1 :=
        (Nat.sub_one_add_one_eq_of_pos this).symm
      have : ∀ i : Fin n,
          ∃ j : Fin n0,
            Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
                (Pset.orderEmbOfFin hcard i.succ) ⊆
              Set.Icc (tau0 j.castSucc) (tau0 j.succ) :=
        (exists_l0_cell_of_refined_cell ht0_zero ht0_last hbase_mem hPsubset _ ·)
      refine ⟨Pset, hzeroP, honeP, hPsubset, ?_⟩
      intro s hs t ht hst hno
      rcases exists_adjacent_index_of_no_between hcard hs ht hst hno with
        ⟨i, rfl, rfl⟩
      let cell := Classical.choose (this i)
      let p := p0 cell
      let U := {r | aLoopExtend ω₁ ω₂ h r ∈ (extChartAt 𝓘(ℂ) p).source}
      let f := fun r ↦ (extChartAt 𝓘(ℂ) p) (aLoopExtend ω₁ ω₂ h r)
      refine ⟨p, U, f, ?_, ?_, ?_, ?_, ?_⟩
      · exact (isOpen_extChartAt_source p).preimage (continuous_aLoopExtend ω₁ ω₂ h)
      · intro r hr
        have : Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
            (Pset.orderEmbOfFin hcard i.succ) ⊆
            Set.Icc (tau0 cell.castSucc) (tau0 cell.succ) :=
          Classical.choose_spec (this i)
        simpa [U, extChartAt_source] using hmem _ _ (this hr)
      · intro _ hr
        exact aLoopExtend_fixedChart_analyticAt _ _ _ hr
      · grind
      · grind
  · grind

/-- The B-cycle is strongly piecewise-real-analytic.

Same refinement-based strengthening as `AX_Elliptic_aLoop_analytic`: refine the
base cell `[0, 1]` into chart-local subsegments. On each refined cell, the
ComplexTorus chart-pullback of `r ↦ [r • ω₂]` is affine in `r`, hence analytic. -/
theorem AX_Elliptic_bLoop_analytic :
    IsAnalyticArcStrong (Elliptic ω₁ ω₂ h) (bLoopExtend ω₁ ω₂ h) {0, 1} := by
  intro _ ha _ hb _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with hb | rfl
    · simp_all
    · let c : Elliptic ω₁ ω₂ h → Set unitInterval :=
        fun x ↦ {u | bLoopExtend ω₁ ω₂ h u ∈ (chartAt ℂ x).source}
      have hc_open : ∀ x, IsOpen (c x) := by
        intro x
        exact (chartAt ℂ x).open_source.preimage
          ((continuous_bLoopExtend ω₁ ω₂ h).comp continuous_subtype_val)
      have : Set.univ ⊆ ⋃ x, c x := by
        intro u _
        exact Set.mem_iUnion.2
          ⟨bLoopExtend ω₁ ω₂ h (u : ℝ),
            mem_chart_source ℂ (bLoopExtend ω₁ ω₂ h (u : ℝ))⟩
      obtain ⟨t0, ht_zero, ht_mono, ⟨m, ht_eventually_one⟩, ht_sub⟩ :=
        exists_monotone_Icc_subset_open_cover_unitInterval hc_open this
      let n0 : ℕ := m + 1
      let tau0 : Fin (n0 + 1) → ℝ := fun i ↦ (t0 i.val : ℝ)
      let p0 : Fin n0 → Elliptic ω₁ ω₂ h := fun i ↦ Classical.choose (ht_sub i.val)
      have ht0_zero : tau0 0 = 0 := by
        simpa [tau0] using congrArg Subtype.val ht_zero
      have ht0_last : tau0 (Fin.last n0) = 1 := by
        have hlast := ht_eventually_one (m + 1) (Nat.le_succ m)
        simpa [tau0, n0, Fin.val_last] using congrArg Subtype.val hlast
      have : Monotone tau0 := by
        intro i j hij
        exact (ht_mono (Fin.val_le_of_le hij) : (t0 i.val : ℝ) ≤ (t0 j.val : ℝ))
      have hmem : ∀ i : Fin n0, ∀ u ∈ Set.Icc (tau0 i.castSucc) (tau0 i.succ),
          bLoopExtend ω₁ ω₂ h u ∈ (chartAt ℂ (p0 i)).source := by
        intro i u hu
        have hleft : (t0 i.val : ℝ) ≤ u := by simpa [tau0, Fin.val_castSucc] using hu.1
        have : u ≤ (t0 (i.val + 1) : ℝ) := by simpa [tau0, Fin.val_succ] using hu.2
        let uI : unitInterval :=
          ⟨u, ⟨(t0 i.val).2.1.trans hleft, this.trans (t0 (i.val + 1)).2.2⟩⟩
        have : uI ∈ Set.Icc (t0 i.val) (t0 (i.val + 1)) := ⟨hleft, this⟩
        grind
      let base := Finset.image tau0 Finset.univ
      let Pset := base
      have hbase_mem : ∀ j : Fin (n0 + 1), tau0 j ∈ Pset := by grind
      have hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1 := by grind
      have hzeroP : (0 : ℝ) ∈ Pset := by grind
      have honeP : (1 : ℝ) ∈ Pset := by grind
      have : Pset.Nonempty := ⟨0, hzeroP⟩
      have := Finset.card_pos.mpr this
      let n := Pset.card - 1
      have hcard : Pset.card = n + 1 :=
        (Nat.sub_one_add_one_eq_of_pos this).symm
      have : ∀ i : Fin n,
          ∃ j : Fin n0,
            Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
                (Pset.orderEmbOfFin hcard i.succ) ⊆
              Set.Icc (tau0 j.castSucc) (tau0 j.succ) :=
        (exists_l0_cell_of_refined_cell ht0_zero ht0_last hbase_mem hPsubset _ ·)
      refine ⟨Pset, hzeroP, honeP, hPsubset, ?_⟩
      intro s hs t ht hst hno
      rcases exists_adjacent_index_of_no_between hcard hs ht hst hno with
        ⟨i, rfl, rfl⟩
      let cell := Classical.choose (this i)
      let p := p0 cell
      let U := {r | bLoopExtend ω₁ ω₂ h r ∈ (extChartAt 𝓘(ℂ) p).source}
      let f := fun r ↦ (extChartAt 𝓘(ℂ) p) (bLoopExtend ω₁ ω₂ h r)
      refine ⟨p, U, f, ?_, ?_, ?_, ?_, ?_⟩
      · exact (isOpen_extChartAt_source p).preimage (continuous_bLoopExtend ω₁ ω₂ h)
      · intro r hr
        have : Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
            (Pset.orderEmbOfFin hcard i.succ) ⊆
            Set.Icc (tau0 cell.castSucc) (tau0 cell.succ) :=
          Classical.choose_spec (this i)
        simpa [U, extChartAt_source] using hmem _ _ (this hr)
      · intro _ hr
        exact bLoopExtend_fixedChart_analyticAt _ _ _ hr
      · grind
      · grind
  · grind

/-- The A-cycle as an `AnalyticArc`. -/
noncomputable def aArc : AnalyticArc (Elliptic ω₁ ω₂ h) where
  extend := aLoopExtend ω₁ ω₂ h
  continuous' := continuous_aLoopExtend ω₁ ω₂ h
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := AX_Elliptic_aLoop_analytic ω₁ ω₂ h

/-- The B-cycle as an `AnalyticArc`. -/
noncomputable def bArc : AnalyticArc (Elliptic ω₁ ω₂ h) where
  extend := bLoopExtend ω₁ ω₂ h
  continuous' := continuous_bLoopExtend ω₁ ω₂ h
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := AX_Elliptic_bLoop_analytic ω₁ ω₂ h

/-- The A-cycle as an `AnalyticLoop` based at `0 : Elliptic`. Closed
because `A(0) = [0] = 0 = [ω₁] = A(1)` (since `ω₁ ∈ Λ`). -/
noncomputable def aLoop : AnalyticLoop (Elliptic ω₁ ω₂ h) 0 where
  arc := aArc ω₁ ω₂ h
  start_eq := by
    change aLoopExtend ω₁ ω₂ h 0 = 0
    unfold aLoopExtend
    push_cast
    rw [zero_mul]
    rfl
  end_eq := by
    change aLoopExtend ω₁ ω₂ h 1 = 0
    unfold aLoopExtend
    push_cast
    rw [one_mul, QuotientAddGroup.mk'_apply]
    change (↑ω₁ : ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change ω₁ ∈ ellipticLattice ω₁ ω₂ h
    unfold ellipticLattice
    exact Submodule.subset_span ⟨0, by simp [ellipticRealBasis]⟩

/-- The B-cycle as an `AnalyticLoop` based at `0`. -/
noncomputable def bLoop : AnalyticLoop (Elliptic ω₁ ω₂ h) 0 where
  arc := bArc ω₁ ω₂ h
  start_eq := by
    change bLoopExtend ω₁ ω₂ h 0 = 0
    unfold bLoopExtend
    push_cast
    rw [zero_mul]
    rfl
  end_eq := by
    change bLoopExtend ω₁ ω₂ h 1 = 0
    unfold bLoopExtend
    push_cast
    rw [one_mul, QuotientAddGroup.mk'_apply]
    change (↑ω₂ : ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change ω₂ ∈ ellipticLattice ω₁ ω₂ h
    unfold ellipticLattice
    exact Submodule.subset_span ⟨1, by simp [ellipticRealBasis]⟩

/-- **Axiom.** Symplectic basis of `H_1` from A- and B-cycles. Provides
the `Module.Basis (Fin 2) ℤ (H_1 _ _)` structure together with a
specialization to `Fin (2 * genus (Elliptic _)) = Fin 2` (after the
`genus_Elliptic_eq_one` rewrite) and the symplectic matrix condition. -/
axiom AX_Elliptic_H1_symplectic :
    AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0

/-- **Concrete witness** for `AX_AnalyticCycleBasis` on `Elliptic`.
Axiom-wrapped at this level — genuine non-vacuity would come from
discharging `AX_Elliptic_H1_symplectic` via covering-space theory +
concrete A/B cycle constructions. -/
noncomputable def ellipticCycleBasis : AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0 :=
  AX_Elliptic_H1_symplectic ω₁ ω₂ h

end Jacobians.ProjectiveCurve
