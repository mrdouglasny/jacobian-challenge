/-
Piecewise-real-analytic arcs and loops on a complex 1-manifold.

## Why this exists

The period map `H_1(X, ℤ) → (HolomorphicOneForm X)^*` is classically
defined by contour integration `[γ] ↦ (ω ↦ ∫_γ ω)`. Formalizing the
integral for a *general* smooth path requires substantial infrastructure
(chart-additivity, Cauchy + Stokes on chart disks, homotopy invariance).
By restricting to **piecewise-real-analytic** paths we can reuse
Mathlib's `curveIntegral` (on normed spaces) chart-locally and appeal to
analytic continuation for homotopy arguments.

**Classical fact (axiomatized as `AX_AnalyticCycleBasis`):** every
homology class `[γ] ∈ H_1(X, ℤ)` has a piecewise-real-analytic
representative, and there exists a ℤ-basis of `H_1` consisting of such
representatives.

## Design (refined 2026-04-23)

`AnalyticArc X` carries:
  - `extend : ℝ → X` — the arc as a function of a real parameter,
    defined for all `r : ℝ` but only meaningful on `[0, 1]`.
  - `continuous'` — continuity of `extend`.
  - `partition : Finset ℝ` — partition points in `[0, 1]` including
    `0` and `1`.
  - `is_analytic` — a real predicate (no longer `True`): on the
    open interior of each partition interval, the chart-pullback
    `(extChartAt p) ∘ extend` is real-analytic, where `p` is the
    image point.

Using `extend : ℝ → X` (as opposed to `toFun : unitInterval → X`) lets
us state analyticity via Mathlib's `AnalyticAt ℝ` on ordinary
`ℝ → ℂ` functions without subtype gymnastics.

Compatibility: `toFun : unitInterval → X` is provided as
`fun t => extend t.val`, with a coe via `AnalyticArc.toPath`-style
helpers (TODO as needed).
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- **Predicate.** "`γ` is real-analytic when read in any chart on the
open interior of each partition subinterval."

For each partition pair `s < t` and each interior point `u ∈ Ioo s t`,
the composite `(extChartAt 𝓘(ℂ) (γ u)) ∘ γ : ℝ → ℂ` is real-analytic at
`u`. Analyticity at `u` is purely local, so the chart-pullback is
guaranteed to be well-defined in a neighborhood of `u`. -/
def IsAnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (extend : ℝ → X) (partition : Finset ℝ) :
    Prop :=
  ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∉ (partition : Set ℝ) →
    AnalyticAt ℝ (fun r : ℝ => (extChartAt 𝓘(ℂ) (extend u)) (extend r)) u

/-- **Strong predicate** (`IsAnalyticArcStrong`). On each *closed* cell `[s, t]`
between consecutive partition points there is a fixed chart centre `p`, an open
`U ⊇ Icc s t`, and a function `f` real-analytic on `U` that *coincides with* the
chart-pullback `(extChartAt p) ∘ extend` on the closed cell.

The witness `f` is **decoupled** from the global `extend`: at a concatenation
junction `extend` turns a corner, so `(extChartAt p) ∘ extend` is not itself
analytic across the junction — but `f` analytically continues one piece's
trajectory past it, and we only ask for agreement on the closed cell. This is
strong enough that the period integrand is continuous on each compact cell, hence
interval-integrable (no `r²sin(1/r²)` pathology), while still implying the weak
`IsAnalyticArc` (see `IsAnalyticArcStrong.toWeak`). -/
def IsAnalyticArcStrong (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (extend : ℝ → X) (partition : Finset ℝ) :
    Prop :=
  ∀ s ∈ partition, ∀ t ∈ partition, s < t →
    (∀ r ∈ partition, r ∉ Set.Ioo s t) →
    ∃ (p : X) (U : Set ℝ) (f : ℝ → ℂ),
      IsOpen U ∧ Set.Icc s t ⊆ U ∧ AnalyticOnNhd ℝ f U ∧
      (∀ r ∈ Set.Icc s t, extend r ∈ (extChartAt 𝓘(ℂ) p).source) ∧
      (∀ r ∈ Set.Icc s t, (extChartAt 𝓘(ℂ) p) (extend r) = f r)

/-- Chart transitions between two `extChartAt` charts are real-analytic on their
overlap. (Local copy of `Jacobians.Bridge.extChartAt_trans_analyticAt`, which is
unavailable here because that file imports this one.) -/
private lemma extChartAt_trans_analyticAt_aux {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hmem : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
  have htransition_source :
      z ∈ ((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) p).source := by
    rw [PartialEquiv.trans_source]; exact ⟨hz, hmem⟩
  have hcont : ContDiffWithinAt ℂ ω
      (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm)
      (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) p q htransition_source
  have hcontAt : ContDiffAt ℂ ω
      (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
    rw [← contDiffWithinAt_univ]; simpa [modelWithCornersSelf_coe] using hcont
  exact hcontAt.analyticAt.restrictScalars (𝕜 := ℝ)

/-- Between consecutive partition points (a partition of `[0,1]` containing `0`
and `1`), every interior non-partition point `u` sits in a unique open cell
`Ioo s t` with `s, t ∈ partition` and no partition point strictly between. -/
lemma exists_consecutive_partition_pair {partition : Finset ℝ}
    (h0 : (0 : ℝ) ∈ partition) (h1 : (1 : ℝ) ∈ partition)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hup : u ∉ (partition : Set ℝ)) :
    ∃ s ∈ partition, ∃ t ∈ partition, s < t ∧ u ∈ Set.Ioo s t ∧
      (∀ r ∈ partition, r ∉ Set.Ioo s t) := by
  classical
  have hlow_ne : (partition.filter (· < u)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨h0, hu.1⟩⟩
  have hhigh_ne : (partition.filter (u < ·)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨h1, hu.2⟩⟩
  set s := (partition.filter (· < u)).max' hlow_ne with hs_def
  set t := (partition.filter (u < ·)).min' hhigh_ne with ht_def
  have hs_mem_filter : s ∈ partition.filter (· < u) := Finset.max'_mem _ _
  have ht_mem_filter : t ∈ partition.filter (u < ·) := Finset.min'_mem _ _
  have hs_mem : s ∈ partition := (Finset.mem_filter.1 hs_mem_filter).1
  have ht_mem : t ∈ partition := (Finset.mem_filter.1 ht_mem_filter).1
  have hs_lt : s < u := (Finset.mem_filter.1 hs_mem_filter).2
  have ht_gt : u < t := (Finset.mem_filter.1 ht_mem_filter).2
  refine ⟨s, hs_mem, t, ht_mem, hs_lt.trans ht_gt, ⟨hs_lt, ht_gt⟩, ?_⟩
  rintro r hr ⟨hsr, hrt⟩
  rcases lt_trichotomy r u with hlt | heq | hgt
  · have : r ≤ s := Finset.le_max' _ r (Finset.mem_filter.2 ⟨hr, hlt⟩)
    exact absurd hsr (not_lt.2 this)
  · exact hup (heq ▸ hr)
  · have : t ≤ r := Finset.min'_le _ r (Finset.mem_filter.2 ⟨hr, hgt⟩)
    exact absurd hrt (not_lt.2 this)

/-- The strong predicate implies the weak one. -/
lemma IsAnalyticArcStrong.toWeak {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {extend : ℝ → X}
    {partition : Finset ℝ} (h0 : (0 : ℝ) ∈ partition) (h1 : (1 : ℝ) ∈ partition)
    (hstrong : IsAnalyticArcStrong X extend partition) :
    IsAnalyticArc X extend partition := by
  intro u hu hup
  obtain ⟨s, hs, t, ht, hst, hu_cell, hcons⟩ :=
    exists_consecutive_partition_pair h0 h1 hu hup
  obtain ⟨p, U, f, hUopen, hIccU, hfU, hsource, hcoinc⟩ := hstrong s hs t ht hst hcons
  -- `Ioo s t` is an open neighbourhood of `u` on which the chart-pullback = `f`.
  have hIoo_mem : Set.Ioo s t ∈ nhds u := IsOpen.mem_nhds isOpen_Ioo hu_cell
  have hIcc_sub : Set.Ioo s t ⊆ Set.Icc s t := Set.Ioo_subset_Icc_self
  -- `f` is analytic at `u`.
  have hfu : AnalyticAt ℝ f u := hfU u (hIccU (hIcc_sub hu_cell))
  -- the transition map `extChartAt (extend u) ∘ (extChartAt p).symm` is analytic at `f u`.
  have hu_src : extend u ∈ (extChartAt 𝓘(ℂ) p).source := hsource u (hIcc_sub hu_cell)
  have hfu_eq : f u = (extChartAt 𝓘(ℂ) p) (extend u) := (hcoinc u (hIcc_sub hu_cell)).symm
  have hz_tgt : f u ∈ (extChartAt 𝓘(ℂ) p).target := by
    rw [hfu_eq]; exact (extChartAt 𝓘(ℂ) p).map_source hu_src
  have hsymm_src : (extChartAt 𝓘(ℂ) p).symm (f u) ∈ (extChartAt 𝓘(ℂ) (extend u)).source := by
    rw [hfu_eq, (extChartAt 𝓘(ℂ) p).left_inv hu_src]
    exact mem_extChartAt_source (extend u)
  have htrans : AnalyticAt ℝ
      ((extChartAt 𝓘(ℂ) (extend u)) ∘ (extChartAt 𝓘(ℂ) p).symm) (f u) :=
    extChartAt_trans_analyticAt_aux hz_tgt hsymm_src
  -- compose, then transport along the eventual equality on `Ioo s t`.
  have hcomp : AnalyticAt ℝ
      (((extChartAt 𝓘(ℂ) (extend u)) ∘ (extChartAt 𝓘(ℂ) p).symm) ∘ f) u :=
    htrans.comp hfu
  refine hcomp.congr ?_
  filter_upwards [hIoo_mem] with r hr
  have hr_icc : r ∈ Set.Icc s t := hIcc_sub hr
  simp only [Function.comp_apply]
  rw [← hcoinc r hr_icc, (extChartAt 𝓘(ℂ) p).left_inv (hsource r hr_icc)]

/-- A piecewise-real-analytic arc in a complex 1-manifold `X`.

Data:
* `extend : ℝ → X` — continuous extension of the arc to the whole real
  line. Only values on `[0, 1]` are mathematically meaningful;
  outside, `extend` is a dummy continuation.
* `partition : Finset ℝ` — partition of `[0, 1]` including endpoints.
* `is_analytic` — real analyticity on each open partition interior
  (see `IsAnalyticArc`). -/
structure AnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  extend : ℝ → X
  continuous' : Continuous extend
  partition : Finset ℝ
  partition_subset : ↑partition ⊆ Set.Icc (0 : ℝ) 1
  zero_mem : (0 : ℝ) ∈ partition
  one_mem : (1 : ℝ) ∈ partition
  is_analytic : IsAnalyticArc X extend partition

namespace AnalyticArc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Evaluation of the arc at a point in `unitInterval`, ignoring the
extension's out-of-range values. -/
def toFun (γ : AnalyticArc X) (t : unitInterval) : X := γ.extend t.val

lemma continuous_toFun (γ : AnalyticArc X) : Continuous γ.toFun :=
  γ.continuous'.comp continuous_subtype_val

end AnalyticArc

/-- A piecewise-real-analytic loop based at `x₀`. -/
structure AnalyticLoop (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) where
  arc : AnalyticArc X
  start_eq : arc.extend 0 = x₀
  end_eq   : arc.extend 1 = x₀

-- TODO (concat): concatenation of two analytic arcs `γ ++ δ` with
-- matching endpoints. Partition becomes a scaled union. Piecewise-
-- analytic is closed under concatenation.

-- TODO (reverse): `reverse γ (r) := γ (1 - r)`, partition reflected.

-- TODO (Path interop): convert `AnalyticArc` to/from `Path a b` in
-- Mathlib — `Path.extend` is the standard `ℝ → X` extension of a
-- Path.

end Jacobians.RiemannSurface
