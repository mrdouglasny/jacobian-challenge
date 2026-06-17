/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.AbelSupsetSections

/-!
# Abel ⊇ pencil analysis (SUP lane, rung S5 of `docs/planning/SUP_ROUTE.md`)

The load-bearing removability rung: the Jacobi pencil map
`Φ = fiberAJ f hf : ℙ¹ → Jacobian X` is continuous everywhere and
holomorphic across the branch values.

* **Sumset-neighborhood brick.** `exists_nhds_zero_finsetSum_mem`: in a
  topological additive commutative group, for every `0`-neighborhood `W`
  and bound `d` there is a `0`-neighborhood `W₀` with
  `∑_{i ∈ t} g i ∈ W` whenever `#t ≤ d` and all `g i ∈ W₀`.

* **S5a (fiber clustering & continuity).**
  `eventually_fiberDivisor_cluster`: near ANY `y₀` (branch value or not)
  the fiber divisor decomposes into clusters
  `fiberDivisor f hf y = ∑_{p ∈ f⁻¹(y₀)} ∑_{q ∈ t_p(y)} of q` with
  `t_p(y)` of cardinality `e_p = mapAnalyticOrderAt (toP1 f) p` inside a
  prescribed neighborhood of `p` (Wallace local-kfold + properness).
  `continuousAt_fiberAJ`: hence `Φ` is continuous at every point — the
  cluster terms `AJ(q) − AJ(p)` are small by continuity of the
  Abel–Jacobi map and there are at most `deg` of them.

* **S5b (removable singularity, manifold-valued).**
  `mdifferentiableAt_of_continuousAt_of_eventually_mdifferentiableAt`:
  a map from a 1-dimensional complex manifold to a complex manifold
  modeled on a complete normed space that is continuous at `x₀` and
  `MDifferentiableAt` on a punctured neighborhood of `x₀` is
  `MDifferentiableAt` at `x₀` (Mathlib removable singularity in the
  target chart — no explicit universal-cover lift needed).

* **S5 (assembly).** `mdifferentiable_fiberAJ`: `Φ` is `MDifferentiable`
  on all of `ℙ¹` — `ContMDiffAt` off the (finite) branch locus by S4c,
  and across each branch value by S5a + S5b.

This file sits BELOW `Jacobians/Axioms/AbelTheorem.lean` in the import
graph (Phase-C in-place conversion pattern) and does not touch
`AX_AbelSupset`. Conditionality: standard-3 + `AX_PeriodCycleBasis`
(inherited from `ofCurveImpl`), as for the rest of the Jacobian layer.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.Vendor.Wallace.HolomorphicForms
open Filter Set

/-! ## The sumset-neighborhood brick -/

/-- In a topological additive commutative group, sums of at most `d` terms
all lying in a small enough `0`-neighborhood lie in a prescribed
`0`-neighborhood. -/
theorem exists_nhds_zero_finsetSum_mem {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [ContinuousAdd G] {ι : Type*} (d : ℕ) {W : Set G}
    (hW : W ∈ 𝓝 (0 : G)) :
    ∃ W₀ ∈ 𝓝 (0 : G), ∀ (t : Finset ι) (g : ι → G), t.card ≤ d →
      (∀ i ∈ t, g i ∈ W₀) → (∑ i ∈ t, g i) ∈ W := by
  classical
  induction d generalizing W with
  | zero =>
      refine ⟨W, hW, fun t g hcard _ => ?_⟩
      have ht : t = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst ht
      simpa using mem_of_mem_nhds hW
  | succ d ih =>
      obtain ⟨V, hV, hVadd⟩ := exists_nhds_zero_half hW
      obtain ⟨W₀, hW₀, hsum⟩ := ih hV
      refine ⟨W₀ ∩ V, Filter.inter_mem hW₀ hV, fun t g hcard hmem => ?_⟩
      rcases Finset.eq_empty_or_nonempty t with rfl | ⟨i, hi⟩
      · simpa using mem_of_mem_nhds hW
      · rw [← Finset.add_sum_erase _ _ hi]
        refine hVadd _ (hmem i hi).2 _ ?_
        refine hsum _ _ ?_ fun j hj => (hmem j (Finset.erase_subset _ _ hj)).1
        rw [Finset.card_erase_of_mem hi]
        omega

/-! ## S5b: removable singularity for manifold-valued maps -/

/-- **Removable singularity, manifold-valued.** A map from a 1-dimensional
complex manifold to a complex manifold modeled on a complete normed space
that is continuous at `x₀` and `MDifferentiableAt` on a punctured
neighborhood of `x₀` is `MDifferentiableAt` at `x₀`. (Mathlib's removable
singularity theorem applied in the fixed source/target charts at
`x₀` / `Φ x₀`.) -/
theorem mdifferentiableAt_of_continuousAt_of_eventually_mdifferentiableAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℂ, F) ω N]
    {Φ : M → N} {x₀ : M} (hcont : ContinuousAt Φ x₀)
    (hev : ∀ᶠ x in 𝓝[≠] x₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, F) Φ x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, F) Φ x₀ := by
  haveI : IsManifold 𝓘(ℂ) 1 M :=
    IsManifold.of_le (I := 𝓘(ℂ)) (M := M) (n := ω) (m := 1) (by simp)
  haveI : IsManifold 𝓘(ℂ, F) 1 N :=
    IsManifold.of_le (I := 𝓘(ℂ, F)) (M := N) (n := ω) (m := 1) (by simp)
  set e : PartialEquiv M ℂ := extChartAt 𝓘(ℂ) x₀ with he
  set e' : PartialEquiv N F := extChartAt 𝓘(ℂ, F) (Φ x₀) with he'
  have hsymm_self : e.symm (e x₀) = x₀ := extChartAt_to_inv x₀
  have hesymm_cont : ContinuousAt e.symm (e x₀) := continuousAt_extChartAt_symm x₀
  -- continuity of the chart presentation at the center
  have htendΦ : Tendsto (fun z => Φ (e.symm z)) (𝓝 (e x₀)) (𝓝 (Φ x₀)) := by
    have hΦ' : ContinuousAt Φ (e.symm (e x₀)) := by
      rw [hsymm_self]
      exact hcont
    have h2 : Tendsto (fun z => Φ (e.symm z)) (𝓝 (e x₀))
        (𝓝 (Φ (e.symm (e x₀)))) := hΦ'.comp hesymm_cont
    rwa [hsymm_self] at h2
  have hGc : ContinuousAt (e' ∘ Φ ∘ e.symm) (e x₀) := by
    have h := (continuousAt_extChartAt (I := 𝓘(ℂ, F)) (Φ x₀)).tendsto.comp htendΦ
    change Tendsto (e' ∘ Φ ∘ e.symm) (𝓝 (e x₀)) (𝓝 ((e' ∘ Φ ∘ e.symm) (e x₀)))
    have hval : (e' ∘ Φ ∘ e.symm) (e x₀) = e' (Φ x₀) := by
      simp only [Function.comp_apply, hsymm_self]
    rw [hval]
    exact h
  -- eventual differentiability of the chart presentation off the center
  have htarget : ∀ᶠ z in 𝓝 (e x₀), z ∈ e.target :=
    Filter.eventually_of_mem
      ((isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀))
      fun _ hz => hz
  have hsource' : ∀ᶠ z in 𝓝 (e x₀), Φ (e.symm z) ∈ (chartAt F (Φ x₀)).source :=
    htendΦ.eventually (Filter.eventually_of_mem
      ((chartAt F (Φ x₀)).open_source.mem_nhds (mem_chart_source F (Φ x₀)))
      fun _ hq => hq)
  have hne : ∀ᶠ z in 𝓝[≠] (e x₀), e.symm z ≠ x₀ := by
    filter_upwards [htarget.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hzt (hzne : z ≠ e x₀)
    intro hzx
    apply hzne
    rw [← e.right_inv hzt, hzx]
  have htendsymm : Tendsto e.symm (𝓝[≠] (e x₀)) (𝓝[≠] x₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have := hesymm_cont.tendsto
      rw [hsymm_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact hne
  have hevd : ∀ᶠ z in 𝓝[≠] (e x₀),
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, F) Φ (e.symm z) :=
    htendsymm.eventually hev
  have hGd : ∀ᶠ z in 𝓝[≠] (e x₀), DifferentiableAt ℂ (e' ∘ Φ ∘ e.symm) z := by
    filter_upwards [htarget.filter_mono nhdsWithin_le_nhds,
      hsource'.filter_mono nhdsWithin_le_nhds, hevd] with z hzt hzsrc' hzd
    have hzsrc : e.symm z ∈ (chartAt ℂ x₀).source := by
      have := e.map_target hzt
      rwa [he, extChartAt_source] at this
    have hiff := (mdifferentiableAt_iff_of_mem_source (I := 𝓘(ℂ))
      (I' := 𝓘(ℂ, F)) (x := x₀) (y := Φ x₀) hzsrc hzsrc').mp hzd
    have hdiff := hiff.2
    rw [e.right_inv hzt] at hdiff
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at hdiff
    exact hdiff
  -- removable singularity in the chart, then back to the manifold statement
  have hG_an : AnalyticAt ℂ (e' ∘ Φ ∘ e.symm) (e x₀) :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hGd hGc
  refine (mdifferentiableAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ, F))
    (x := x₀) (y := Φ x₀) (mem_chart_source ℂ x₀)
    (mem_chart_source F (Φ x₀))).mpr ⟨hcont, ?_⟩
  exact hG_an.differentiableAt.differentiableWithinAt

/-! ## S5a: fiber clustering and continuity of the pencil map -/

namespace MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Fiber clustering at an arbitrary value.** Near any `y₀` (branch value
or not), the fiber divisor decomposes into clusters: one finset `t p` of
simple fiber points per fiber point `p` over `y₀`, of cardinality the local
mapping degree `e_p`, contained in any prescribed neighborhood `U' p` of
`p`, with `fiberDivisor f hf y = ∑_p ∑_{q ∈ t p} of q`. -/
theorem eventually_fiberDivisor_cluster (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) (y₀ : ProjectiveLine) (U' : X → Set X)
    (hU'open : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset, IsOpen (U' p))
    (hU'mem : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset, p ∈ U' p) :
    ∀ᶠ y in 𝓝 y₀, y ≠ y₀ → ∃ t : X → Finset X,
      (∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ↑(t p) ⊆ U' p ∧ (t p).card = mapAnalyticOrderAt (toP1 f) p ∧
          ∀ q ∈ t p, toP1 f q = y ∧ mapAnalyticOrderAt (toP1 f) q = 1) ∧
      fiberDivisor f hf y =
        ∑ p ∈ (toP1_fiber_finite hf y₀).toFinset,
          ∑ q ∈ t p, FreeAbelianGroup.of q := by
  classical
  have hmem : ∀ p : X, p ∈ (toP1_fiber_finite hf y₀).toFinset ↔ toP1 f p = y₀ := by
    intro p
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  have hpos : ∀ p : X, 0 < mapAnalyticOrderAt (toP1 f) p := fun p =>
    mapAnalyticOrderAt_pos_of_contMDiff (toP1_contMDiff f) (toP1_nonconst hf) p
  obtain ⟨U₀, hU₀mem, hU₀disj⟩ :=
    Set.Finite.exists_pairwiseDisjoint_open_nhds (toP1_fiber_finite hf y₀)
  -- Wallace local-kfold data inside `U₀ p ∩ U' p`
  have hkdata : ∀ p : X, ∃ U : Set X, ∃ V : Set ProjectiveLine,
      p ∈ (toP1_fiber_finite hf y₀).toFinset →
        IsOpen U ∧ p ∈ U ∧ U ⊆ U₀ p ∧ U ⊆ U' p ∧ IsOpen V ∧ y₀ ∈ V ∧
        ∀ y ∈ V, y ≠ y₀ → ∃ t : Finset X,
          t.card = mapAnalyticOrderAt (toP1 f) p ∧ ↑t ⊆ U ∧
          (∀ q ∈ t, toP1 f q = y ∧ mapAnalyticOrderAt (toP1 f) q = 1) ∧
          (∀ q ∈ U, toP1 f q = y → q ∈ t) := by
    intro p
    by_cases hp : p ∈ (toP1_fiber_finite hf y₀).toFinset
    · have hpfib : p ∈ toP1 f ⁻¹' {y₀} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact (hmem p).mp hp
      obtain ⟨hU₀open, hpU₀⟩ := hU₀mem p hpfib
      have hOopen : IsOpen (U₀ p ∩ U' p) := hU₀open.inter (hU'open p hp)
      have hpO : p ∈ U₀ p ∩ U' p := ⟨hpU₀, hU'mem p hp⟩
      obtain ⟨U, hUo, hpU, hUsub, V, hVo, hyV, hk⟩ :=
        local_kfold_ramified_of_contMDiff_within (toP1_contMDiff f)
          hOopen hpO (hpos p) rfl
      rw [(hmem p).mp hp] at hyV hk
      exact ⟨U, V, fun _ => ⟨hUo, hpU,
        hUsub.trans Set.inter_subset_left,
        hUsub.trans Set.inter_subset_right, hVo, hyV, hk⟩⟩
    · exact ⟨Set.univ, Set.univ, fun h => absurd h hp⟩
  choose U V hUV using hkdata
  -- properness
  have hUnion_open : IsOpen (⋃ p ∈ (toP1_fiber_finite hf y₀).toFinset, U p) :=
    isOpen_biUnion fun p hp => (hUV p hp).1
  have hfib_sub : toP1 f ⁻¹' {y₀} ⊆
      ⋃ p ∈ (toP1_fiber_finite hf y₀).toFinset, U p := by
    intro q hq
    have hqS : q ∈ (toP1_fiber_finite hf y₀).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hq
    exact Set.mem_biUnion hqS (hUV q hqS).2.1
  have hprop : ∀ᶠ y in 𝓝 y₀,
      toP1 f ⁻¹' {y} ⊆ ⋃ p ∈ (toP1_fiber_finite hf y₀).toFinset, U p :=
    eventually_fiber_subset_of_compact_T2 (toP1_contMDiff f).continuous
      hUnion_open hfib_sub
  have hVev : ∀ᶠ y in 𝓝 y₀, ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
      y ∈ V p :=
    (Filter.eventually_all_finset _).mpr fun p hp =>
      Filter.eventually_of_mem
        ((hUV p hp).2.2.2.2.1.mem_nhds (hUV p hp).2.2.2.2.2.1)
        fun _ hy => hy
  filter_upwards [hprop, hVev] with y hyprop hyV
  intro hyy
  -- pick the kfold finset for this `y` at each fiber point
  have hkf : ∀ p : X, ∃ tp : Finset X,
      p ∈ (toP1_fiber_finite hf y₀).toFinset →
        tp.card = mapAnalyticOrderAt (toP1 f) p ∧ ↑tp ⊆ U p ∧
        (∀ q ∈ tp, toP1 f q = y ∧ mapAnalyticOrderAt (toP1 f) q = 1) ∧
        (∀ q ∈ U p, toP1 f q = y → q ∈ tp) := by
    intro p
    by_cases hp : p ∈ (toP1_fiber_finite hf y₀).toFinset
    · obtain ⟨tp, h⟩ := (hUV p hp).2.2.2.2.2.2 y (hyV p hp) hyy
      exact ⟨tp, fun _ => h⟩
    · exact ⟨∅, fun h => absurd h hp⟩
  choose t ht using hkf
  refine ⟨t, fun p hp => ⟨Set.Subset.trans (ht p hp).2.1 (hUV p hp).2.2.2.1,
    (ht p hp).1, (ht p hp).2.2.1⟩, ?_⟩
  -- the fiber finset is the disjoint union of the clusters
  have hfib_eq : (toP1_fiber_finite hf y).toFinset =
      (toP1_fiber_finite hf y₀).toFinset.biUnion t := by
    ext q
    constructor
    · intro hq
      have hq' : toP1 f q = y := by
        rw [Set.Finite.mem_toFinset, Set.mem_preimage,
          Set.mem_singleton_iff] at hq
        exact hq
      have hqfib : q ∈ toP1 f ⁻¹' {y} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact hq'
      obtain ⟨p, hpS, hqUp⟩ := Set.mem_iUnion₂.mp (hyprop hqfib)
      exact Finset.mem_biUnion.mpr ⟨p, hpS, (ht p hpS).2.2.2 q hqUp hq'⟩
    · intro hq
      obtain ⟨p, hpS, hqt⟩ := Finset.mem_biUnion.mp hq
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
      exact ((ht p hpS).2.2.1 q hqt).1
  have hdisj_t : Set.PairwiseDisjoint
      ↑(toP1_fiber_finite hf y₀).toFinset t := by
    intro p hp p' hp' hne
    have hpS : p ∈ (toP1_fiber_finite hf y₀).toFinset := hp
    have hpS' : p' ∈ (toP1_fiber_finite hf y₀).toFinset := hp'
    have hpfib : p ∈ toP1 f ⁻¹' {y₀} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (hmem p).mp hpS
    have hpfib' : p' ∈ toP1 f ⁻¹' {y₀} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (hmem p').mp hpS'
    have hdisj := hU₀disj hpfib hpfib' hne
    change Disjoint (t p) (t p')
    rw [Finset.disjoint_left]
    intro q hq hq'
    have h1 : q ∈ U₀ p := (hUV p hpS).2.2.1 ((ht p hpS).2.1 hq)
    have h2 : q ∈ U₀ p' := (hUV p' hpS').2.2.1 ((ht p' hpS').2.1 hq')
    exact Set.disjoint_left.mp hdisj h1 h2
  rw [fiberDivisor, hfib_eq, Finset.sum_biUnion hdisj_t]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  rw [((ht p hp).2.2.1 q hq).2]
  simp

/-- **S5a (continuity of the pencil map).** The Jacobi pencil map
`Φ = fiberAJ f hf : ℙ¹ → Jacobian X` is continuous at every point —
including the branch values. Cluster decomposition + continuity of the
Abel–Jacobi map + the sumset-neighborhood brick. -/
theorem continuousAt_fiberAJ (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) (y₀ : ProjectiveLine) :
    ContinuousAt (fiberAJ f hf) y₀ := by
  classical
  haveI : IsTopologicalAddGroup (Jacobian X) :=
    topologicalAddGroup_of_lieAddGroup
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
  refine Filter.tendsto_def.mpr fun W hW => ?_
  set AJ : X → Jacobian X := ofCurveImpl X (Classical.arbitrary X) with hAJ
  have hAJcont : Continuous AJ :=
    (AX_ofCurve_contMDiff (Classical.arbitrary X)).continuous
  set S₀ := (toP1_fiber_finite hf y₀).toFinset with hS₀
  set d := S₀.sum (mapAnalyticOrderAt (toP1 f)) with hd
  have hpos : ∀ p : X, 0 < mapAnalyticOrderAt (toP1 f) p := fun p =>
    mapAnalyticOrderAt_pos_of_contMDiff (toP1_contMDiff f) (toP1_nonconst hf) p
  -- translate `W` to a 0-neighborhood and split it `d`-fold twice
  have hVtrans : {g : Jacobian X | fiberAJ f hf y₀ + g ∈ W} ∈ 𝓝 (0 : Jacobian X) := by
    have hadd : ContinuousAt (fun g : Jacobian X => fiberAJ f hf y₀ + g) 0 :=
      (continuous_const_add (fiberAJ f hf y₀)).continuousAt
    have h0 : fiberAJ f hf y₀ + (0 : Jacobian X) = fiberAJ f hf y₀ := add_zero _
    exact hadd.preimage_mem_nhds (by rwa [h0])
  obtain ⟨V₁, hV₁, hsum1⟩ :=
    exists_nhds_zero_finsetSum_mem (ι := X) d hVtrans
  obtain ⟨W₀, hW₀, hsum0⟩ :=
    exists_nhds_zero_finsetSum_mem (ι := X) d hV₁
  -- prescribed cluster neighborhoods: `AJ q − AJ p` small
  set U' : X → Set X := fun p => (fun q => AJ q - AJ p) ⁻¹' interior W₀
    with hU'
  have hU'open : ∀ p ∈ S₀, IsOpen (U' p) := fun p _ =>
    (hAJcont.sub continuous_const).isOpen_preimage _ isOpen_interior
  have hU'mem : ∀ p ∈ S₀, p ∈ U' p := by
    intro p _
    change AJ p - AJ p ∈ interior W₀
    rw [sub_self]
    exact mem_interior_iff_mem_nhds.mpr hW₀
  -- cardinality bounds
  have hcard_le : S₀.card ≤ d := by
    rw [hd, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p _ => hpos p
  have he_le : ∀ p ∈ S₀, mapAnalyticOrderAt (toP1 f) p ≤ d := fun p hp =>
    Finset.single_le_sum (fun q _ => Nat.zero_le _) hp
  filter_upwards [eventually_fiberDivisor_cluster f hf y₀ U' hU'open hU'mem]
    with y hclus
  change fiberAJ f hf y ∈ W
  by_cases hyy : y = y₀
  · subst hyy
    exact mem_of_mem_nhds hW
  obtain ⟨t, ht, hdecomp⟩ := hclus hyy
  -- the pencil values on both sides
  have hΦy : fiberAJ f hf y = ∑ p ∈ S₀, ∑ q ∈ t p, AJ q := by
    change abelJacobiDiv X (fiberDivisor f hf y) = _
    rw [hdecomp, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => FreeAbelianGroup.lift_apply_of _ _
  have hΦy₀ : fiberAJ f hf y₀ =
      ∑ p ∈ S₀, (mapAnalyticOrderAt (toP1 f) p : ℤ) • AJ p := by
    change abelJacobiDiv X (fiberDivisor f hf y₀) = _
    rw [fiberDivisor, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [map_zsmul]
    congr 1
    exact FreeAbelianGroup.lift_apply_of _ _
  -- the difference is a double sum of small cluster increments
  have hper : ∀ p ∈ S₀, ∑ q ∈ t p, (AJ q - AJ p) =
      (∑ q ∈ t p, AJ q) - (mapAnalyticOrderAt (toP1 f) p : ℤ) • AJ p := by
    intro p hp
    rw [Finset.sum_sub_distrib, Finset.sum_const, (ht p hp).2.1,
      natCast_zsmul]
  have hD : ∑ p ∈ S₀, ∑ q ∈ t p, (AJ q - AJ p) =
      (∑ p ∈ S₀, ∑ q ∈ t p, AJ q) -
        ∑ p ∈ S₀, (mapAnalyticOrderAt (toP1 f) p : ℤ) • AJ p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hper
  have hkey : fiberAJ f hf y =
      fiberAJ f hf y₀ + ∑ p ∈ S₀, ∑ q ∈ t p, (AJ q - AJ p) := by
    rw [hΦy, hΦy₀, hD]
    abel
  -- membership chain
  have hmemW : (∑ p ∈ S₀, ∑ q ∈ t p, (AJ q - AJ p)) ∈
      {g : Jacobian X | fiberAJ f hf y₀ + g ∈ W} := by
    refine hsum1 S₀ _ hcard_le fun p hp => ?_
    refine hsum0 (t p) _ ((ht p hp).2.1 ▸ he_le p hp) fun q hq => ?_
    have hqU' : q ∈ U' p := (ht p hp).1 hq
    exact interior_subset hqU'
  rw [hkey]
  exact hmemW

/-! ## S5: the pencil map is holomorphic on all of `ℙ¹` -/

/-- **S5 (the load-bearing removability).** The Jacobi pencil map
`Φ = fiberAJ f hf : ℙ¹ → Jacobian X` is `MDifferentiable` everywhere:
`ContMDiffAt` off the finite branch locus (S4c), and across each branch
value by continuity (S5a) + the manifold-valued removable singularity
(S5b). -/
theorem mdifferentiable_fiberAJ (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) :
    MDifferentiable 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (fiberAJ f hf) := by
  intro y₀
  by_cases hy₀ : y₀ ∈ branchValues f
  · -- branch value: remove the singularity
    refine mdifferentiableAt_of_continuousAt_of_eventually_mdifferentiableAt
      (continuousAt_fiberAJ f hf y₀) ?_
    have hfin : (branchValues f).Finite := branchValues_finite f hf
    have hclosed : IsClosed (branchValues f \ {y₀}) :=
      (hfin.subset Set.diff_subset).isClosed
    have hy₀notin : y₀ ∉ branchValues f \ {y₀} := fun h => h.2 rfl
    have hcompl : (branchValues f \ {y₀})ᶜ ∈ 𝓝 y₀ :=
      hclosed.isOpen_compl.mem_nhds hy₀notin
    have hev : ∀ᶠ y in 𝓝[≠] y₀, y ∉ branchValues f := by
      filter_upwards [nhdsWithin_le_nhds hcompl, self_mem_nhdsWithin]
        with y hyc hyne
      intro hyb
      exact hyc ⟨hyb, hyne⟩
    filter_upwards [hev] with y hy
    exact (contMDiffAt_fiberAJ f hf hy).mdifferentiableAt (by simp)
  · exact (contMDiffAt_fiberAJ f hf hy₀).mdifferentiableAt (by simp)

end MeromorphicFunctionField

end Jacobians.RiemannSurface
