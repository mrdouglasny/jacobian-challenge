/-
# Generic strong-analyticity constructor from moving-chart analyticity

A continuous curve `γ : ℝ → X` into a complex 1-manifold that is real-analytic
**in the moving chart** — i.e. for every `r` the chart-readout
`u ↦ extChartAt 𝓘(ℂ) (γ r) (γ u)` is `AnalyticAt ℝ` at `r` — is a strong
piecewise-real-analytic arc over the trivial base partition `{0, 1}`
(`IsAnalyticArcStrong`).

This factors the chart-cover/refinement argument out of the elliptic A/B-cycle
witnesses (`Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`,
`AX_Elliptic_aLoop_analytic`), where it was proved twice inline for the two
specific torus loops. The hyperelliptic branch-cut loop constructions
(`Jacobians/ProjectiveCurve/Hyperelliptic/CycleLoops.lean`) consume it
directly: a square-root lift of an analytic x-plane loop reads off in every
moving chart as the x-plane loop itself, so this lemma turns base-loop
analyticity into the strong arc predicate in one step.

## Main results

* `analyticAt_extChartAt_comp_of_movingChart` — moving-chart analyticity
  transports to any fixed chart whose source contains the point (via
  analytic chart transitions).
* `isAnalyticArcStrong_of_movingChart` — the constructor.
* `AnalyticArc.ofMovingChart` / `AnalyticLoop.ofMovingChart` — packaging.
-/
import Jacobians.RiemannSurface.AnalyticArc

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/- Chart transitions between two `extChartAt` charts are real-analytic on their
overlap. (Local copy of the private lemma in `AnalyticArc.lean`; the public
`Jacobians.Bridge.extChartAt_trans_analyticAt` lives downstream of this file's
consumers.) -/
private lemma extChartAt_trans_analyticAt_aux {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hmem : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
  have htrans_source :
      z ∈ ((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) p).source := by
    rw [PartialEquiv.trans_source]; exact ⟨hz, hmem⟩
  have hcont : ContDiffWithinAt ℂ ω
      (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm)
      (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) p q htrans_source
  have hcontAt : ContDiffAt ℂ ω
      (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
    rw [← contDiffWithinAt_univ]; simpa [modelWithCornersSelf_coe] using hcont
  exact hcontAt.analyticAt.restrictScalars (𝕜 := ℝ)

/-- **Fixed-chart analyticity from moving-chart analyticity.** If the
chart-readout of `γ` in the moving chart is analytic at every parameter, then
its readout in *any* fixed chart `extChartAt 𝓘(ℂ) p` is analytic at every `r`
with `γ r` in that chart's source. (Chart transitions on a complex-analytic
manifold are analytic.) -/
theorem analyticAt_extChartAt_comp_of_movingChart {γ : ℝ → X}
    (hcont : Continuous γ)
    (hmov : ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r)
    {p : X} {r : ℝ} (hr : γ r ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ u)) r := by
  let q := γ r
  have h₁ : AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ u)) r := hmov r
  have h₂ : q ∈ (extChartAt 𝓘(ℂ) q).source := mem_extChartAt_source q
  have h₃ : (extChartAt 𝓘(ℂ) q) q ∈ (extChartAt 𝓘(ℂ) q).target :=
    (extChartAt 𝓘(ℂ) q).map_source h₂
  have hsymm_mem :
      (extChartAt 𝓘(ℂ) q).symm ((extChartAt 𝓘(ℂ) q) q) ∈
        (extChartAt 𝓘(ℂ) p).source := by
    rwa [(extChartAt 𝓘(ℂ) q).left_inv h₂]
  have htrans : AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm)
        ((extChartAt 𝓘(ℂ) q) q) :=
    extChartAt_trans_analyticAt_aux h₃ hsymm_mem
  have hcomp : AnalyticAt ℝ
      (((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) ∘
        (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ u))) r :=
    htrans.comp_of_eq h₁ (by simp [q])
  refine hcomp.congr ?_
  have hnhds :
      ∀ᶠ u in 𝓝 r, γ u ∈ (extChartAt 𝓘(ℂ) q).source :=
    hcont.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℂ)) q).mem_nhds h₂)
  filter_upwards [hnhds] with u hu
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

/-- **Strong-arc constructor.** A continuous `γ : ℝ → X` whose moving-chart
readout `u ↦ extChartAt 𝓘(ℂ) (γ r) (γ u)` is real-analytic at every `r` is a
strong piecewise-real-analytic arc over the trivial base partition `{0, 1}`:
the chart-source cover of `γ '' [0, 1]` refines `[0, 1]` into finitely many
chart-local cells, on each of which the fixed-chart readout is the analytic
witness. -/
theorem isAnalyticArcStrong_of_movingChart {γ : ℝ → X}
    (hcont : Continuous γ)
    (hmov : ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r) :
    IsAnalyticArcStrong X γ {0, 1} := by
  intro _ ha _ hb _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with hb | rfl
    · simp_all
    · let c : X → Set unitInterval :=
        fun x ↦ {u | γ (u : ℝ) ∈ (chartAt ℂ x).source}
      have hc_open : ∀ x, IsOpen (c x) := by
        intro x
        exact (chartAt ℂ x).open_source.preimage
          (hcont.comp continuous_subtype_val)
      have hc_cover : Set.univ ⊆ ⋃ x, c x := by
        intro u _
        exact Set.mem_iUnion.2
          ⟨γ (u : ℝ), mem_chart_source ℂ (γ (u : ℝ))⟩
      obtain ⟨t0, ht_zero, ht_mono, ⟨m, ht_eventually_one⟩, ht_sub⟩ :=
        exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
      let n0 : ℕ := m + 1
      let tau0 : Fin (n0 + 1) → ℝ := fun i ↦ (t0 i.val : ℝ)
      let p0 : Fin n0 → X := fun i ↦ Classical.choose (ht_sub i.val)
      have ht0_zero : tau0 0 = 0 := by
        simpa [tau0] using congrArg Subtype.val ht_zero
      have ht0_last : tau0 (Fin.last n0) = 1 := by
        have hlast := ht_eventually_one (m + 1) (Nat.le_succ m)
        simpa [tau0, n0, Fin.val_last] using congrArg Subtype.val hlast
      have : Monotone tau0 := by
        intro i j hij
        exact (ht_mono (Fin.val_le_of_le hij) : (t0 i.val : ℝ) ≤ (t0 j.val : ℝ))
      have hmem : ∀ i : Fin n0, ∀ u ∈ Set.Icc (tau0 i.castSucc) (tau0 i.succ),
          γ u ∈ (chartAt ℂ (p0 i)).source := by
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
      let U := {r | γ r ∈ (extChartAt 𝓘(ℂ) p).source}
      let f := fun r ↦ (extChartAt 𝓘(ℂ) p) (γ r)
      refine ⟨p, U, f, ?_, ?_, ?_, ?_, ?_⟩
      · exact (isOpen_extChartAt_source p).preimage hcont
      · intro r hr
        have : Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
            (Pset.orderEmbOfFin hcard i.succ) ⊆
            Set.Icc (tau0 cell.castSucc) (tau0 cell.succ) :=
          Classical.choose_spec (this i)
        simpa [U, extChartAt_source] using hmem _ _ (this hr)
      · intro _ hr
        exact analyticAt_extChartAt_comp_of_movingChart hcont hmov hr
      · grind
      · grind
  · grind

/-- Package a continuous, globally moving-chart-analytic curve as an
`AnalyticArc` with the trivial base partition `{0, 1}`. -/
noncomputable def AnalyticArc.ofMovingChart (γ : ℝ → X) (hcont : Continuous γ)
    (hmov : ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r) :
    AnalyticArc X where
  extend := γ
  continuous' := hcont
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := isAnalyticArcStrong_of_movingChart hcont hmov

@[simp] theorem AnalyticArc.ofMovingChart_extend (γ : ℝ → X) (hcont : Continuous γ)
    (hmov : ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r) :
    (AnalyticArc.ofMovingChart γ hcont hmov).extend = γ :=
  rfl

/-- Package a continuous, globally moving-chart-analytic closed curve as an
`AnalyticLoop` based at `γ 0`. -/
noncomputable def AnalyticLoop.ofMovingChart (γ : ℝ → X) (hcont : Continuous γ)
    (hmov : ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r)
    (hclosed : γ 1 = γ 0) :
    AnalyticLoop X (γ 0) where
  arc := AnalyticArc.ofMovingChart γ hcont hmov
  start_eq := rfl
  end_eq := hclosed

end Jacobians.RiemannSurface
