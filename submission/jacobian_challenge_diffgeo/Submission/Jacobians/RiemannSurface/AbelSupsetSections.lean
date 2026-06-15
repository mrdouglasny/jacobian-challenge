/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.RiemannSurface.AbelSupsetPlumbing
import Submission.Jacobians.RiemannSurface.DegreeOneGenusZero

universe u v w

/-!
# Abel ⊇ local sections (SUP lane, rung S4b of `docs/planning/SUP_ROUTE.md`)

Local holomorphic sections of the pencil `toP1 f` over a regular value, and
the resulting local trivialization of the fiber divisor.

* **Local-inverse upgrades.** `IsHolomorphicAt.localInverse_apply_self` /
  `localInverse_tendsto` complete the API of the Wallace manifold-level
  local inverse (`Jacobians.Vendor.Wallace…IsHolomorphicAt.localInverse`),
  and `contMDiffAt_of_isHolomorphicAt_of_continuousAt` is the pointwise
  form of Wallace's `ContMDiff.of_isHolomorphic_and_continuous`.

* **S4b (local sections over a regular value).**
  `exists_fiberDivisor_sections`: over `y₀ ∉ branchValues f` the fiber
  `f⁻¹(y₀) = {p₁, …, p_d}` is unramified (S4a), so through each `pᵢ` the
  pencil has a local holomorphic section `sᵢ` (`sᵢ y₀ = pᵢ`,
  `toP1 f (sᵢ y) = y` near `y₀`, `ContMDiffAt` at `y₀`), and near `y₀`
  the whole fiber divisor trivializes as
  `fiberDivisor f hf y = ∑ᵢ of (sᵢ y)`
  (Wallace local-kfold uniqueness + properness of the compact-source map).

This file sits BELOW `Jacobians/Axioms/AbelTheorem.lean` in the import
graph (Phase-C in-place conversion pattern) and does not touch
`AX_AbelSupset`. Conditionality: no axioms beyond the ambient layer (the
S4b theorems themselves use none).
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.Vendor.Wallace.HolomorphicForms
open Filter Set

/-! ## Local-inverse API upgrades (generic charted spaces) -/

section LocalInverse

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

/-- The Wallace manifold-level local inverse sends `F p` back to `p`. -/
theorem IsHolomorphicAt.localInverse_apply_self
    {F : M → N} {p : M} (hF : IsHolomorphicAt F p)
    (hderiv : deriv (chartLocalAt F p) (chartAt ℂ p p) ≠ 0) :
    hF.localInverse hderiv (F p) = p := by
  let r : ℂ → ℂ :=
    hF.hasStrictDerivAt.localInverse (chartLocalAt F p)
      (deriv (chartLocalAt F p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
  have hFp : chartLocalAt F p (chartAt ℂ p p) = chartAt ℂ (F p) (F p) := by
    simp [chartLocalAt]
  have hleft_r : r (chartAt ℂ (F p) (F p)) = chartAt ℂ p p := by
    dsimp only [r]
    rw [← hFp]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := chartLocalAt F p)
      (f' := deriv (chartLocalAt F p) (chartAt ℂ p p))
      (a := chartAt ℂ p p) (hf := hF.hasStrictDerivAt)
      (hf' := hderiv)).self_of_nhds
  show (chartAt ℂ p).symm (r (chartAt ℂ (F p) (F p))) = p
  rw [hleft_r]
  exact (chartAt ℂ p).left_inv (mem_chart_source ℂ p)

/-- The Wallace manifold-level local inverse tends to `p` at `F p`. -/
theorem IsHolomorphicAt.localInverse_tendsto
    {F : M → N} {p : M} (hF : IsHolomorphicAt F p)
    (hderiv : deriv (chartLocalAt F p) (chartAt ℂ p p) ≠ 0) :
    Tendsto (hF.localInverse hderiv) (𝓝 (F p)) (𝓝 p) := by
  let r : ℂ → ℂ :=
    hF.hasStrictDerivAt.localInverse (chartLocalAt F p)
      (deriv (chartLocalAt F p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
  have hFp : chartLocalAt F p (chartAt ℂ p p) = chartAt ℂ (F p) (F p) := by
    simp [chartLocalAt]
  have hleft_r : r (chartAt ℂ (F p) (F p)) = chartAt ℂ p p := by
    dsimp only [r]
    rw [← hFp]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := chartLocalAt F p)
      (f' := deriv (chartLocalAt F p) (chartAt ℂ p p))
      (a := chartAt ℂ p p) (hf := hF.hasStrictDerivAt)
      (hf' := hderiv)).self_of_nhds
  have hr_an : AnalyticAt ℂ r (chartAt ℂ (F p) (F p)) := by
    have h := hF.analyticAt_localInverse hderiv
    simpa [r, hFp] using h
  have hr_tendsto : Tendsto r (𝓝 (chartAt ℂ (F p) (F p))) (𝓝 (chartAt ℂ p p)) := by
    have hcont_r := hr_an.continuousAt
    change Tendsto r (𝓝 (chartAt ℂ (F p) (F p))) (𝓝 (r (chartAt ℂ (F p) (F p)))) at hcont_r
    simpa [hleft_r] using hcont_r
  have hchartN_tendsto :
      Tendsto (fun y : N => chartAt ℂ (F p) y) (𝓝 (F p))
        (𝓝 (chartAt ℂ (F p) (F p))) :=
    (chartAt ℂ (F p)).continuousAt (mem_chart_source ℂ (F p))
  have hsymm_tendsto :
      Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p)) (𝓝 p) := by
    have hcont_symm := (chartAt ℂ p).continuousAt_symm
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
      (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont_symm
    simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont_symm
  exact hsymm_tendsto.comp (hr_tendsto.comp hchartN_tendsto)

/-- Pointwise form of Wallace's `ContMDiff.of_isHolomorphic_and_continuous`:
chart-local analyticity plus continuity at a point give `ContMDiffAt` there. -/
theorem contMDiffAt_of_isHolomorphicAt_of_continuousAt
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N]
    {F : M → N} {p : M} (hholo : IsHolomorphicAt F p)
    (hcont : ContinuousAt F p) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) F p := by
  rw [contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (x := p) (y := F p) (f := F) (n := (⊤ : WithTop ℕ∞))
        (mem_chart_source ℂ p) (mem_chart_source ℂ (F p))]
  refine ⟨hcont, ?_⟩
  have hAA : AnalyticAt ℂ
      (chartAt ℂ (F p) ∘ F ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := hholo
  have hCD : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (chartAt ℂ (F p) ∘ F ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    hAA.contDiffAt
  simpa [contDiffWithinAt_univ, ModelWithCorners.range_eq_target] using hCD

end LocalInverse

/-! ## S4b: local sections of the pencil over a regular value -/

namespace MeromorphicFunctionField


variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

open Jacobians.RiemannSurface.MeromorphicFunctionField

/-- **A single local holomorphic section through an unramified fiber point.**
At `p` with `toP1 f p = y₀` and local mapping degree `1`, the pencil has a
local section `s` through `p`: `s y₀ = p`, `s` is `ContMDiffAt` at `y₀`,
`s` tends to `p`, and `toP1 f (s y) = y` near `y₀` (the Wallace local
inverse). -/
theorem exists_section_at (f : MeromorphicFunctionField X)
    {y₀ : ProjectiveLine} {p : X} (hp : toP1 f p = y₀)
    (horder : mapAnalyticOrderAt (toP1 f) p = 1) :
    ∃ s : ProjectiveLine → X, s y₀ = p ∧
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) s y₀ ∧
      Tendsto s (𝓝 y₀) (𝓝 p) ∧
      ∀ᶠ y in 𝓝 y₀, toP1 f (s y) = y := by
  subst hp
  have hF : IsHolomorphicAt (toP1 f) p :=
    IsHolomorphicAt.of_contMDiff (toP1_contMDiff f) p
  have hderiv : deriv (chartLocalAt (toP1 f) p) (chartAt ℂ p p) ≠ 0 :=
    deriv_ne_zero_of_mapAnalyticOrderAt_eq_one hF horder
  have happ : hF.localInverse hderiv (toP1 f p) = p :=
    IsHolomorphicAt.localInverse_apply_self hF hderiv
  have htendsto : Tendsto (hF.localInverse hderiv) (𝓝 (toP1 f p)) (𝓝 p) :=
    IsHolomorphicAt.localInverse_tendsto hF hderiv
  have hcont : ContinuousAt (hF.localInverse hderiv) (toP1 f p) := by
    show Tendsto (hF.localInverse hderiv) (𝓝 (toP1 f p))
      (𝓝 (hF.localInverse hderiv (toP1 f p)))
    rw [happ]
    exact htendsto
  have hsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞)
      (hF.localInverse hderiv) (toP1 f p) :=
    contMDiffAt_of_isHolomorphicAt_of_continuousAt
      (hF.localInverse_isHolomorphicAt hderiv) hcont
  have hright : ∀ᶠ y in 𝓝 (toP1 f p), toP1 f (hF.localInverse hderiv y) = y := by
    have h := IsHolomorphicAt.localInverse_eventually_right_inverse hF
      (toP1_contMDiff f).continuous.continuousAt hderiv
    filter_upwards [h] with y hy using hy
  exact ⟨hF.localInverse hderiv, happ, hsmooth, htendsto, hright⟩

/-- **S4b (local sections over a regular value).** Over `y₀ ∉ branchValues f`
the pencil `toP1 f` admits a family of local holomorphic sections through the
fiber points: `s p y₀ = p`, each `s p` is `ContMDiffAt` at `y₀` and tends to
`p`, `toP1 f (s p y) = y` near `y₀`, and the fiber divisor trivializes near
`y₀` as the section sum `fiberDivisor f hf y = ∑_{p ∈ f⁻¹(y₀)} of (s p y)`. -/
theorem exists_fiberDivisor_sections (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) {y₀ : ProjectiveLine} (hy₀ : y₀ ∉ branchValues f) :
    ∃ s : X → ProjectiveLine → X,
      (∀ p ∈ (toP1_fiber_finite hf y₀).toFinset, s p y₀ = p) ∧
      (∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (s p) y₀) ∧
      (∀ p ∈ (toP1_fiber_finite hf y₀).toFinset, Tendsto (s p) (𝓝 y₀) (𝓝 p)) ∧
      (∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ∀ᶠ y in 𝓝 y₀, toP1 f (s p y) = y) ∧
      (∀ᶠ y in 𝓝 y₀, fiberDivisor f hf y =
        ∑ p ∈ (toP1_fiber_finite hf y₀).toFinset,
          FreeAbelianGroup.of (s p y)) := by
  classical
  have hmem : ∀ p : X, p ∈ (toP1_fiber_finite hf y₀).toFinset ↔ toP1 f p = y₀ := by
    intro p
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  -- regular fiber: all local degrees are 1 (S4a)
  have horder1 : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
      mapAnalyticOrderAt (toP1 f) p = 1 := fun p hp =>
    mapAnalyticOrderAt_eq_one_of_not_branchValue f hf hy₀ ((hmem p).mp hp)
  -- one section through each fiber point
  have hsec : ∀ p : X, ∃ sp : ProjectiveLine → X,
      p ∈ (toP1_fiber_finite hf y₀).toFinset →
        sp y₀ = p ∧ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) sp y₀ ∧
        Tendsto sp (𝓝 y₀) (𝓝 p) ∧ ∀ᶠ y in 𝓝 y₀, toP1 f (sp y) = y := by
    intro p
    by_cases hp : p ∈ (toP1_fiber_finite hf y₀).toFinset
    · obtain ⟨sp, h1, h2, h3, h4⟩ :=
        exists_section_at f ((hmem p).mp hp) (horder1 p hp)
      exact ⟨sp, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨fun _ => p, fun h => absurd h hp⟩
  choose s hs using hsec
  -- pairwise-disjoint opens around the fiber points
  obtain ⟨U₀, hU₀mem, hU₀disj⟩ :=
    Set.Finite.exists_pairwiseDisjoint_open_nhds (toP1_fiber_finite hf y₀)
  -- Wallace local-kfold data (k = 1) inside the disjoint opens
  have hkdata : ∀ p : X, ∃ U : Set X, ∃ V : Set ProjectiveLine,
      p ∈ (toP1_fiber_finite hf y₀).toFinset →
        IsOpen U ∧ p ∈ U ∧ U ⊆ U₀ p ∧ IsOpen V ∧ y₀ ∈ V ∧
        ∀ y ∈ V, y ≠ y₀ →
          ∃ t : Finset X, t.card = 1 ∧ ↑t ⊆ U ∧
            (∀ q ∈ t, toP1 f q = y ∧ mapAnalyticOrderAt (toP1 f) q = 1) ∧
            (∀ q ∈ U, toP1 f q = y → q ∈ t) := by
    intro p
    by_cases hp : p ∈ (toP1_fiber_finite hf y₀).toFinset
    · have hpfib : p ∈ toP1 f ⁻¹' {y₀} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact (hmem p).mp hp
      obtain ⟨hU₀open, hpU₀⟩ := hU₀mem p hpfib
      obtain ⟨U, hUo, hpU, hUsub, V, hVo, hyV, hk⟩ :=
        local_kfold_ramified_of_contMDiff_within (toP1_contMDiff f)
          hU₀open hpU₀ one_pos (horder1 p hp)
      rw [(hmem p).mp hp] at hyV hk
      exact ⟨U, V, fun _ => ⟨hUo, hpU, hUsub, hVo, hyV, hk⟩⟩
    · exact ⟨Set.univ, Set.univ, fun h => absurd h hp⟩
  choose U V hUV using hkdata
  -- properness: nearby fibers stay inside the union of the section opens
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
  -- eventual conjunctions over the (finite) fiber
  have hVev : ∀ᶠ y in 𝓝 y₀, ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
      y ∈ V p :=
    (Filter.eventually_all_finset _).mpr fun p hp =>
      Filter.eventually_of_mem ((hUV p hp).2.2.2.1.mem_nhds (hUV p hp).2.2.2.2.1)
        fun _ hy => hy
  have hsUev : ∀ᶠ y in 𝓝 y₀, ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
      s p y ∈ U p :=
    (Filter.eventually_all_finset _).mpr fun p hp =>
      ((hs p hp).2.2.1).eventually
        (Filter.eventually_of_mem ((hUV p hp).1.mem_nhds (hUV p hp).2.1)
          fun _ hq => hq)
  have hsecev : ∀ᶠ y in 𝓝 y₀, ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
      toP1 f (s p y) = y :=
    (Filter.eventually_all_finset _).mpr fun p hp => (hs p hp).2.2.2
  refine ⟨s, fun p hp => (hs p hp).1, fun p hp => (hs p hp).2.1,
    fun p hp => (hs p hp).2.2.1, fun p hp => (hs p hp).2.2.2, ?_⟩
  filter_upwards [hprop, hVev, hsUev, hsecev] with y hyprop hyV hysU hysec
  by_cases hyy : y = y₀
  · -- at the center: the sections pass through the fiber points
    subst hyy
    rw [fiberDivisor]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(hs p hp).1, horder1 p hp]
    simp
  · -- off-center: the kfold singletons are exactly the section values
    have hsingle : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ∀ q ∈ U p, toP1 f q = y → q = s p y := by
      intro p hp q hqU hqy
      obtain ⟨t, htcard, -, -, htcomplete⟩ :=
        (hUV p hp).2.2.2.2.2 y (hyV p hp) hyy
      have hq : q ∈ t := htcomplete q hqU hqy
      have hsp : s p y ∈ t := htcomplete (s p y) (hysU p hp) (hysec p hp)
      rw [Finset.card_eq_one] at htcard
      obtain ⟨a, rfl⟩ := htcard
      rw [Finset.mem_singleton] at hq hsp
      rw [hq, hsp]
    have hord_s : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        mapAnalyticOrderAt (toP1 f) (s p y) = 1 := by
      intro p hp
      obtain ⟨t, -, -, htord, htcomplete⟩ :=
        (hUV p hp).2.2.2.2.2 y (hyV p hp) hyy
      exact (htord (s p y) (htcomplete (s p y) (hysU p hp) (hysec p hp))).2
    -- the fiber over `y` is exactly the (injective) section image
    have hfib_eq : (toP1_fiber_finite hf y).toFinset =
        (toP1_fiber_finite hf y₀).toFinset.image fun p => s p y := by
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
        exact Finset.mem_image.mpr ⟨p, hpS, (hsingle p hpS q hqUp hq').symm⟩
      · intro hq
        obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hq
        rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
        exact hysec p hpS
    have hinj : ∀ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ∀ p' ∈ (toP1_fiber_finite hf y₀).toFinset, s p y = s p' y → p = p' := by
      intro p hp p' hp' hss
      by_contra hne
      have hpfib : p ∈ toP1 f ⁻¹' {y₀} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact (hmem p).mp hp
      have hpfib' : p' ∈ toP1 f ⁻¹' {y₀} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact (hmem p').mp hp'
      have hdisj := hU₀disj hpfib hpfib' hne
      have h1 : s p y ∈ U₀ p := (hUV p hp).2.2.1 (hysU p hp)
      have h2 : s p y ∈ U₀ p' := by
        rw [hss]
        exact (hUV p' hp').2.2.1 (hysU p' hp')
      exact Set.disjoint_left.mp hdisj h1 h2
    rw [fiberDivisor, hfib_eq, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hord_s p hp]
    simp

/-! ## S4c: smoothness of the Jacobi pencil map at regular values

With `AX_ofCurve_contMDiff` a THEOREM (the Abel–Jacobi map `ofCurveImpl` is
`ContMDiff ω` into the Jacobian), the pencil map `fiberAJ` is smooth at every
regular value directly in the Jacobian: near `y₀ ∉ branchValues f` the fiber
divisor trivializes along the S4b sections, so
`fiberAJ f hf y = ∑ᵢ ofCurveImpl x₀ (sᵢ y)` — a finite sum of compositions
of `ContMDiff` maps, smooth by the `LieAddGroup` structure of the Jacobian.
No ambient chart-lift is needed at this rung. -/

/-- **S4c (pencil smoothness at regular values).** The Jacobi pencil map
`Φ = fiberAJ f hf : ℙ¹ → Jacobian X` is `ContMDiffAt` at every non-branch
value: along the S4b sections, `Φ(y) = ∑ᵢ AJ(sᵢ y)` near `y₀`. -/
theorem contMDiffAt_fiberAJ (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) {y₀ : ProjectiveLine} (hy₀ : y₀ ∉ branchValues f) :
    ContMDiffAt 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (⊤ : WithTop ℕ∞) (fiberAJ f hf) y₀ := by
  obtain ⟨s, hs0, hsmooth, -, -, hdiv⟩ :=
    exists_fiberDivisor_sections f hf hy₀
  have hev : fiberAJ f hf =ᶠ[𝓝 y₀]
      fun y => ∑ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ofCurveImpl X (Classical.arbitrary X) (s p y) := by
    filter_upwards [hdiv] with y hy
    show abelJacobiDiv X (fiberDivisor f hf y) = _
    rw [hy, map_sum]
    exact Finset.sum_congr rfl fun p hp =>
      FreeAbelianGroup.lift_apply_of _ _
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  refine ContMDiffAt.sum fun p hp => ?_
  exact ((AX_ofCurve_contMDiff (Classical.arbitrary X)).contMDiffAt).comp
    y₀ (hsmooth p hp)

end MeromorphicFunctionField

end Jacobians.RiemannSurface
