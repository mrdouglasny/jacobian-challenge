/-
`AX_BranchLocus`: properness, discrete fibers, and degree invariance
for non-constant holomorphic maps between compact Riemann surfaces.

**Statement (Lean, refined 2026-04-23).** For `f : X → Y` a non-constant
holomorphic map between compact Riemann surfaces, there exists a
common fiber degree `d > 0` such that:

1. `∀ q : Y, (∑' p : X, localOrder f p q) = d` — the weighted fiber
   count is `d` for every `q`.
2. `{ q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite` —
   only finitely many `q` have branch points above them.

`localOrder f p q : ℕ` is the local multiplicity: `0` if `f p ≠ q`,
otherwise the degree of zero of `f(·) - q` at `p` (≥ 1).

## Consequences

* `ContMDiff.degree f` is well-defined as this common `d`; via
  `Classical.choose` on the existential.
* `pushforward_pullback = deg • id` reduces to fiber-counting using (1).
* The locus `{q : Y | ramified at q}` being finite lets us do "generic
  Hurwitz-style" analyses.

## Why axiomatized

The proof uses: non-constant holomorphic maps are open (Open Mapping
Theorem for 1-dim), combined with compactness of `X` and connectedness
of `Y`. All standard, but Mathlib's open-mapping-for-holomorphic-maps
infrastructure is specific to `ℂ`-valued maps, not maps between
manifolds.

## History

- 2026-04-22 (Gemini review #1): flagged — replace `toFinset`-based
  statement with `tsum` + `¬ ∃ c, ∀ x, f x = c` (non-constant in
  standard form).
- 2026-04-23 (A7 in completion plan): promoted from doc-only to real
  Lean statement via opaque `localOrder`.

See `docs/formalization-plan.md` §7, discharge priority #6;
`docs/completion-plan.md` workstream A7.
Reference: Forster Ch. I §4; Mumford Vol I §II.2.
-/
import Jacobians.RiemannSurface.OneForm
import Jacobians.Vendor.Wallace.HolomorphicForms.HolomorphicMap

set_option linter.style.openClassical false

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff Classical BigOperators

open Jacobians.Vendor.Wallace.HolomorphicForms
open Filter Set

/-- The local order (ramification multiplicity) of the holomorphic map `f` at
point `p` above `q`:

    localOrder f p q = 0                 if f p ≠ q,
    localOrder f p q = k ≥ 1             if f p = q and f locally looks
                                         like `z ↦ q + c·(z-p)^k` with
                                         `c ≠ 0`.

**Discharged (2026-06-03)** from an opaque axiom to a real definition: when
`f p = q` it is the analytic order of `f` at `p`,
`Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt f p` (the chart-local
`analyticOrderNatAt` of `f`, sorry-free in the adopted Wallace `HolomorphicMap`
module — Forster Ch. I §4, Mumford Vol I §II.2). Well-defined because non-constant
holomorphic maps in dimension 1 have isolated zeros of their Taylor series. -/
noncomputable def localOrder {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (p : X) (q : Y) : ℕ :=
  if f p = q then Jacobians.Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt f p else 0

private theorem analyticOrderNatAt_pow_zero (k : ℕ) :
    analyticOrderNatAt (fun z : ℂ => z ^ k) 0 = k := by
  have heq : ((· - (0 : ℂ)) ^ k) = (fun z : ℂ => z ^ k) := by funext z; simp
  have key : analyticOrderAt (fun z : ℂ => z ^ k) 0 = (k : ℕ∞) :=
    heq ▸ analyticOrderAt_centeredMonomial
  simp [analyticOrderNatAt, key]

/-- **Faithfulness witness for `localOrder`.** The canonical `k`-fold cover
`z ↦ zᵏ` has local order exactly `k` at the origin (`1` for an unramified `k = 1`,
`≥ 2` for genuine ramification). This pins the discharged `def` to the intended
ramification index on a concrete absolute case — the kind of non-vacuity check the
kernel cannot supply for a definition. -/
theorem localOrder_pow {k : ℕ} (hk : 0 < k) :
    localOrder (fun z : ℂ => z ^ k) 0 0 = k := by
  have hf0 : (fun z : ℂ => z ^ k) 0 = 0 := by simp [zero_pow hk.ne']
  rw [localOrder, if_pos hf0]
  have hmap : mapAnalyticOrderAt (fun z : ℂ => z ^ k) 0
      = analyticOrderNatAt (fun z : ℂ => z ^ k) 0 := by
    unfold mapAnalyticOrderAt chartLocalAt
    simp [zero_pow hk.ne']
  rw [hmap, analyticOrderNatAt_pow_zero]

theorem localOrder_eq_mapAnalyticOrderAt_of_mem_fiber {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} {p : X} {q : Y} (hpq : f p = q) :
    localOrder f p q = mapAnalyticOrderAt f p := by
  simp [localOrder, hpq]

theorem localOrder_eq_zero_of_not_mem_fiber {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} {p : X} {q : Y} (hpq : f p ≠ q) :
    localOrder f p q = 0 := by
  simp [localOrder, hpq]

private theorem weightedFiberSum_constant_of_contMDiff {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite) :
    ∃ d : ℕ, ∀ y : Y,
      (finite_fiber y).toFinset.sum (mapAnalyticOrderAt f) = d := by
  classical
  let Φ : Y → ℕ := fun y => (finite_fiber y).toFinset.sum (mapAnalyticOrderAt f)
  have hloc : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y₀
    have hev : ∀ᶠ y in 𝓝 y₀, Φ y = Φ y₀ := by
      simpa [Φ] using
        weightedFiberConservation_of_contMDiff (f := f) hf hnonconst finite_fiber y₀
    rcases mem_nhds_iff.mp (Filter.eventually_iff.mp hev) with
      ⟨U, hUsub, hUopen, hy₀U⟩
    exact ⟨U, hUopen, hy₀U, fun y hyU => hUsub hyU⟩
  by_cases hY : Nonempty Y
  · let Φlc : LocallyConstant Y ℕ := ⟨Φ, hloc⟩
    let y₀ : Y := Classical.choice hY
    refine ⟨Φ y₀, ?_⟩
    intro y
    exact LocallyConstant.apply_eq_of_preconnectedSpace Φlc y y₀
  · exact ⟨0, fun y => (hY ⟨y⟩).elim⟩

private theorem mapAnalyticOrderAt_gt_one_finite {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite) :
    {p : X | mapAnalyticOrderAt f p > 1}.Finite := by
  classical
  let R : Set X := {p : X | mapAnalyticOrderAt f p > 1}
  have hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ R ⊆ ({x} : Set X) := by
    intro x
    let other : Set X := (f ⁻¹' {f x}) \ ({x} : Set X)
    have hother_finite : other.Finite :=
      (finite_fiber (f x)).subset (by intro z hz; exact hz.1)
    let O : Set X := otherᶜ
    have hO_open : IsOpen O := hother_finite.isClosed.isOpen_compl
    have hxO : x ∈ O := by
      intro hxother
      exact hxother.2 rfl
    obtain ⟨U₀, hU₀_open, hxU₀, hU₀_sub, V, hV_open, hfxV, hkfold⟩ :=
      local_kfold_ramified_of_contMDiff_within (f := f) hf hO_open hxO
        (mapAnalyticOrderAt_pos_of_contMDiff hf hnonconst x) rfl
    let U : Set X := U₀ ∩ f ⁻¹' V
    refine ⟨U, hU₀_open.inter (hf.continuous.isOpen_preimage _ hV_open), ⟨hxU₀, hfxV⟩, ?_⟩
    intro z hz
    have hzU₀ : z ∈ U₀ := hz.1.1
    have hzfV : f z ∈ V := hz.1.2
    have hzR : mapAnalyticOrderAt f z > 1 := hz.2
    by_cases hfxz : f z = f x
    · have hzO : z ∈ O := hU₀_sub hzU₀
      have hz_not_other : z ∉ other := hzO
      have hzx : z = x := by
        by_contra hzx
        exact hz_not_other ⟨hfxz, hzx⟩
      simp [hzx]
    · obtain ⟨s, _hcard, _hsU, hsimple, hcomplete⟩ := hkfold (f z) hzfV hfxz
      have hz_s : z ∈ s := hcomplete z hzU₀ rfl
      have hz_order : mapAnalyticOrderAt f z = 1 := (hsimple z hz_s).2
      omega
  choose U hU_open hxU hU_ram using hlocal
  obtain ⟨t, htcover⟩ :=
    isCompact_univ.elim_finite_subcover U hU_open (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, hxU x⟩)
  have hR_sub_t : R ⊆ (t : Set X) := by
    intro r hrR
    have hr_cover : r ∈ ⋃ x ∈ t, U x := htcover (mem_univ r)
    rcases mem_iUnion₂.mp hr_cover with ⟨x, hxt, hrUx⟩
    have hrx : r = x := by
      have : r ∈ ({x} : Set X) := hU_ram x ⟨hrUx, hrR⟩
      simpa using this
    simpa [hrx] using hxt
  exact (Finset.finite_toSet t).subset hR_sub_t

/-- **Branch-locus theorem.** For a non-constant holomorphic map between
compact Riemann surfaces, there's a common degree `d` such that
fiber-sums of `localOrder` all equal `d`, and the branch locus is
finite. -/
theorem AX_BranchLocus {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (_hnc : ¬ ∃ c : Y, ∀ x : X, f x = c) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
      { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite := by
  classical
  have hfTop : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f := by
    simpa using _hf.of_le le_top
  have hhol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hfTop (hasLocalKfoldRamification_of_contMDiff hfTop)
  let finite_fiber : ∀ q : Y, (f ⁻¹' {q}).Finite :=
    fun q => isHolomorphic_finite_fiber hhol _hnc q
  obtain ⟨d, hd⟩ :=
    weightedFiberSum_constant_of_contMDiff (f := f) hfTop _hnc finite_fiber
  refine ⟨d, ?_, ?_, ?_⟩
  · let x₀ : X := Classical.arbitrary X
    have hx₀_mem : x₀ ∈ (finite_fiber (f x₀)).toFinset := by
      rw [Set.Finite.mem_toFinset]
      rfl
    have hsum_pos :
        0 < (finite_fiber (f x₀)).toFinset.sum (mapAnalyticOrderAt f) := by
      exact Finset.sum_pos
        (fun x _hx => mapAnalyticOrderAt_pos_of_contMDiff hfTop _hnc x)
        ⟨x₀, hx₀_mem⟩
    rw [hd (f x₀)] at hsum_pos
    exact hsum_pos
  · intro q
    have hzero : ∀ p ∉ (finite_fiber q).toFinset, localOrder f p q = 0 := by
      intro p hp
      apply localOrder_eq_zero_of_not_mem_fiber
      intro hpq
      exact hp ((Set.Finite.mem_toFinset (finite_fiber q)).mpr hpq)
    calc
      (∑' p : X, localOrder f p q)
          = ∑ p ∈ (finite_fiber q).toFinset, localOrder f p q := by
              exact tsum_eq_sum hzero
      _ = (finite_fiber q).toFinset.sum (mapAnalyticOrderAt f) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              exact localOrder_eq_mapAnalyticOrderAt_of_mem_fiber
                ((Set.Finite.mem_toFinset (finite_fiber q)).mp hp)
      _ = d := hd q
  · have hR_finite :
        {p : X | mapAnalyticOrderAt f p > 1}.Finite :=
      mapAnalyticOrderAt_gt_one_finite (f := f) hfTop _hnc finite_fiber
    refine (hR_finite.image f).subset ?_
    intro q hq
    rcases hq with ⟨p, hfp, hporder⟩
    exact ⟨p, by
      rw [localOrder_eq_mapAnalyticOrderAt_of_mem_fiber hfp] at hporder
      exact hporder, hfp⟩

end Jacobians.Axioms
