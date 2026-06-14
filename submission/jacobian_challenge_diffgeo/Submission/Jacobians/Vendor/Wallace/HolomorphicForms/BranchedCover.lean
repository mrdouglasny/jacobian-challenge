/-
Copyright (c) 2026 Michal J Wallace. All rights reserved.
Released under the MIT license (the upstream repository LICENSE; © Michal J Wallace).
Original source: https://github.com/tangentstorm/JacobianChallenge
                 Jacobian/HolomorphicForms/BranchedCover.lean (commit 82349bc8, 2026-06-01).
Note: the upstream repo LICENSE is MIT; on full adoption, vendor the upstream
LICENSE under `vendor/wallace-jacobian-challenge/`.

Vendored (trial) into this repository on 2026-06-02 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced under `Jacobians.Vendor.Wallace.*`.
- Internal imports retargeted to the vendored module paths.
- Removed the unused vacuous helper `ramificationIndexStub (_f) (_x) := 1`
  (argument-ignoring constant; not used by the real branched-degree machinery).
No other mathematical content was altered.
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Connected.Basic
import Submission.Jacobians.Vendor.Wallace.HolomorphicForms.HolomorphicMap

/-!
# Production API promoted from blueprint `def:branched-degree` (TRIVIAL/SHORT/MEDIUM/HARD leaves)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Concrete proof-bearing realisations of the eight sub-leaves catalogued in the
ChatGPT plan `ref/plans/branched-degree.md`:

Imports are narrow (no `import Mathlib`): `Set.Finite` /
`Set.Finite.toFinset`, `Finset.sum` and `Finset.card`, and the
`TopologicalSpace` / `ConnectedSpace` typeclasses needed for the
constancy-on-connected-target story.

Downstream nodes (degree-one bijection, Riemann-Hurwitz, push-pull)
should depend on `branchedDegree_eq_weightedFiberCard` and
`branchedDegree_one_fiber_unique`, **not** on the unfolded
`Classical.arbitrary` choice. The analytic constructor (leaf 8) is
where the open-mapping theorem and isolated-zeros enter the project.

## Compatibility predicate

* `BranchedCoverData.RamificationIndexCompatible` : the explicit
  hypothesis linking the combinatorial index to the chart-local
  analytic order.  It is not automatic for arbitrary
  `BranchedCoverData`; analytic constructors should prove it by
  construction.
-/

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.flexible false
set_option linter.unusedSectionVars false

namespace Jacobians.Vendor.Wallace.HolomorphicForms



/--
**Plan leaf 2 (SHORT).** Packaged data for a branched cover
`f : X → Y`: the local ramification indices, finiteness of every fibre,
and the constancy theorem for the weighted fibre count. Bundling the
constancy hypothesis as a structure field is the load-bearing trick
that lets `branchedDegree` exist before the analytic open-mapping
theorem is in place.

`weightedFiberCard` is provided as a derived definition (not a
structure field), so consumers can rely on the formula
`((finite_fiber y).toFinset).sum ramificationIndex` without worrying
about user overrides. The constancy field is stated directly in terms
of the formula.
-/
structure BranchedCoverData
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) where
  /-- Local ramification / mapping multiplicity at each point. -/
  ramificationIndex : X → ℕ
  /-- Multiplicities are positive. -/
  ramificationIndex_pos : ∀ x, 0 < ramificationIndex x
  /--
Every fibre is finite (a deep fact for nonconstant holomorphic
  maps between compact Riemann surfaces).
-/
  finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite
  /--
The weighted fibre count is constant on `Y` (the genuinely
  nontrivial part of the definition); stated directly via the fibre
  sum so that `branchedDegree_eq_weightedFiberCard` is unconditional.
-/
  fiberSum_const :
    ∀ y₁ y₂ : Y,
      ((finite_fiber y₁).toFinset).sum ramificationIndex
        = ((finite_fiber y₂).toFinset).sum ramificationIndex
  /-- The source-side branch locus is finite. -/
  ramified_finite : {x : X | ramificationIndex x ≠ 1}.Finite
  /-- At an unramified point, the cover is locally bijective. -/
  local_bijective_unramified :
    ∀ x : X, ramificationIndex x = 1 →
      ∃ U : Set X, ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧ Set.BijOn f U V

/--
Compatibility between the combinatorial ramification index and the
chart-local analytic order.  This is deliberately a hypothesis/predicate,
not a theorem about arbitrary `BranchedCoverData`: non-analytic or
hand-built data can otherwise choose an unrelated index function.
-/
def BranchedCoverData.RamificationIndexCompatible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    {f : X → Y} (h : BranchedCoverData X Y f) : Prop :=
  ∀ x : X, IsHolomorphicAt f x → h.ramificationIndex x = mapAnalyticOrderAt f x

/--
Convenience projection for an explicit ramification/order
compatibility hypothesis.
-/
theorem BranchedCoverData.ramificationIndex_eq_mapAnalyticOrderAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    {f : X → Y} {h : BranchedCoverData X Y f}
    (hcompat : h.RamificationIndexCompatible)
    {x : X} (hf : IsHolomorphicAt f x) :
    h.ramificationIndex x = mapAnalyticOrderAt f x :=
  hcompat x hf

/--
**Plan leaf 9 (NEW).** The local inverse of `f` near an unramified
point `x`. Defined using `Function.invFunOn` from the local bijection
witness.
-/
noncomputable def BranchedCoverData.localInverseAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f) (x : X)
    (hx : h.ramificationIndex x = 1) : Y → X :=
  Function.invFunOn f (h.local_bijective_unramified x hx).choose

/--
**Plan leaf 10 (NEW).** The local inverse at an unramified point
is a genuine inverse on some neighborhood. This "compatibility lemma"
packages the `Function.invFunOn` properties with the `BranchedCoverData`
topology fields.
-/
theorem BranchedCoverData.localInverse_is_inverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f) {x : X}
    (hx : h.ramificationIndex x = 1) :
    ∃ U : Set X, ∃ V : Set Y,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧
      Set.BijOn f U V ∧
      (∀ y' ∈ V, f (h.localInverseAt x hx y') = y') ∧
      (∀ x' ∈ U, h.localInverseAt x hx (f x') = x') := by
  set U := (h.local_bijective_unramified x hx).choose
  set V := (h.local_bijective_unramified x hx).choose_spec.choose
  have hspec := (h.local_bijective_unramified x hx).choose_spec.choose_spec
  refine ⟨U, V, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2, ?_, ?_⟩
  · intro y' hy'
    unfold localInverseAt
    exact hspec.2.2.2.2.surjOn.rightInvOn_invFunOn hy'
  · intro x' hx'
    unfold localInverseAt
    exact hspec.2.2.2.2.injOn.leftInvOn_invFunOn hx'


/--
Derived: the weighted cardinality of the fibre over `y`, i.e. the
sum of ramification indices of all preimages of `y`.
-/
noncomputable def BranchedCoverData.weightedFiberCard
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : BranchedCoverData X Y f) (y : Y) : ℕ :=
  ((h.finite_fiber y).toFinset).sum h.ramificationIndex

/--
**Plan leaf 3 (SHORT).** The branched degree of a packaged cover:
the weighted fibre cardinality at any base point. We pick the base
point via `Classical.arbitrary`; independence of the choice is
expressed by `branchedDegree_eq_weightedFiberCard`.
-/
noncomputable def branchedDegree
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) : ℕ :=
  h.weightedFiberCard (Classical.arbitrary Y)

/--
**Plan leaf 4 (SHORT).** Main downstream rewrite: `branchedDegree`
agrees with the weighted fibre count at **any** chosen base point
`y : Y`. Direct corollary of `fiberSum_const`.
-/
theorem branchedDegree_eq_weightedFiberCard
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y) :
    branchedDegree h = h.weightedFiberCard y := by
  unfold branchedDegree BranchedCoverData.weightedFiberCard
  exact h.fiberSum_const _ y

/--
The weighted fibre count is constant on `Y`: the formula version
of `branchedDegree_eq_weightedFiberCard` that does not route through
`branchedDegree`.
-/
theorem BranchedCoverData.weightedFiberCard_const
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : BranchedCoverData X Y f) (y₁ y₂ : Y) :
    h.weightedFiberCard y₁ = h.weightedFiberCard y₂ :=
  h.fiberSum_const y₁ y₂

/--
**Plan leaf 5 (MEDIUM).** Surjective covers have positive degree:
pick any `y : Y`, pick a preimage `x` over `y`, observe
`ramificationIndex x ≥ 1` is a positive summand in the finite
weighted-fibre sum.
-/
theorem branchedDegree_pos
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (hsurj : Function.Surjective f) :
    0 < branchedDegree h := by
  set y : Y := Classical.arbitrary Y with hy
  rw [branchedDegree_eq_weightedFiberCard h y]
  show 0 < ((h.finite_fiber y).toFinset).sum h.ramificationIndex
  obtain ⟨x, hx⟩ := hsurj y
  refine Finset.sum_pos (fun z _ => h.ramificationIndex_pos z) ⟨x, ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact hx

/--
**Plan leaf 6 (MEDIUM).** On a fibre with no ramification, the
branched degree equals the (finite) cardinality of the fibre. We state
the fibre cardinality via `(h.finite_fiber y).toFinset.card` so the
file remains free of `Nat.card`/`SetTheory.Cardinal` imports.
-/
theorem branchedDegree_eq_card_toFinset_of_unramified_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hunram : ∀ x ∈ f ⁻¹' {y}, h.ramificationIndex x = 1) :
    branchedDegree h = (h.finite_fiber y).toFinset.card := by
  rw [branchedDegree_eq_weightedFiberCard h y]
  show ((h.finite_fiber y).toFinset).sum h.ramificationIndex
      = (h.finite_fiber y).toFinset.card
  have hcongr : ((h.finite_fiber y).toFinset).sum h.ramificationIndex
      = ((h.finite_fiber y).toFinset).sum (fun _ : X => (1 : ℕ)) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    exact hunram x hx
  rw [hcongr]
  simp

/--
Helper for leaf 7: when `branchedDegree h = 1`, the fibre `Finset`
over any `y : Y` is a singleton `{x}` and the unique element has
ramification index `1`.  This is the load-bearing combinatorial fact
behind both `branchedDegree_one_fiber_unique` and the downstream
`degree_one_bijective`.
-/
theorem branchedDegree_one_fiber_singleton
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hdeg : branchedDegree h = 1) :
    ∃ x, (h.finite_fiber y).toFinset = {x} ∧ h.ramificationIndex x = 1 := by
  have hsum : ((h.finite_fiber y).toFinset).sum h.ramificationIndex = 1 := by
    show h.weightedFiberCard y = 1
    rw [← branchedDegree_eq_weightedFiberCard h y]
    exact hdeg
  set s := (h.finite_fiber y).toFinset with hs
  have hcard_le_sum : s.card ≤ s.sum h.ramificationIndex := by
    have hconst : s.card = s.sum (fun _ : X => (1 : ℕ)) := by simp
    rw [hconst]
    exact Finset.sum_le_sum (fun x _ => h.ramificationIndex_pos x)
  rw [hsum] at hcard_le_sum
  have hne : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hcard : s.card = 1 :=
    le_antisymm hcard_le_sum hne.card_pos
  rw [Finset.card_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  refine ⟨x, hx, ?_⟩
  rw [hx, Finset.sum_singleton] at hsum
  exact hsum

/--
**Plan leaf 7 (HARD).** A degree-one branched cover has a unique
preimage of every base point, and that preimage is unramified. The
combinatorial heart of the degree-one ⇒ bijective chain.
-/
theorem branchedDegree_one_fiber_unique
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hdeg : branchedDegree h = 1) :
    ∃! x : X, f x = y ∧ h.ramificationIndex x = 1 := by
  obtain ⟨x, hxs, hrx⟩ := branchedDegree_one_fiber_singleton h y hdeg
  have hx_mem : x ∈ (h.finite_fiber y).toFinset := by
    rw [hxs]; exact Finset.mem_singleton_self x
  rw [Set.Finite.mem_toFinset] at hx_mem
  refine ⟨x, ⟨hx_mem, hrx⟩, ?_⟩
  rintro x' ⟨hfx', _⟩
  have hx'_mem : x' ∈ (h.finite_fiber y).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hfx'
  rw [hxs, Finset.mem_singleton] at hx'_mem
  exact hx'_mem

/-!
# Production API promoted from blueprint `thm:degree-one-bijective`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A degree-one holomorphic map between compact connected Riemann
surfaces is bijective: degree one forces every fibre to have a single
sheet (injectivity), and the same singleton fibre witness gives
surjectivity.

The analytic hypothesis "non-constant holomorphic between compact
connected Riemann surfaces" is absorbed into the existence of a
`BranchedCoverData X Y f`; the analytic constructor producing such
data from the holomorphic input is the still-open
`branchedCoverData_of_nonconstant_holomorphic` (leaf 8 in
the branched-degree story). Once that lands, the
hypothesis here is fed by the constructor and this theorem becomes a
direct consequence of the combinatorial leaf 7.
-/


/--
**`thm:degree-one-bijective`.** A degree-one branched cover is
bijective.  Surjectivity comes from the singleton fibre over any
target point; injectivity follows because two distinct preimages of
the same point would each contribute a positive summand to a weighted
fibre sum already equal to one.
-/
theorem degree_one_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (hdeg : branchedDegree h = 1) :
    Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ heq
    obtain ⟨x, hxs, _⟩ := branchedDegree_one_fiber_singleton h (f x₁) hdeg
    have hx₁ : x₁ = x := by
      have hmem : x₁ ∈ (h.finite_fiber (f x₁)).toFinset := by
        rw [Set.Finite.mem_toFinset]; rfl
      rw [hxs, Finset.mem_singleton] at hmem
      exact hmem
    have hx₂ : x₂ = x := by
      have hmem : x₂ ∈ (h.finite_fiber (f x₁)).toFinset := by
        rw [Set.Finite.mem_toFinset]; exact heq.symm
      rw [hxs, Finset.mem_singleton] at hmem
      exact hmem
    rw [hx₁, hx₂]
  · intro y
    obtain ⟨x, hxs, _⟩ := branchedDegree_one_fiber_singleton h y hdeg
    have hmem : x ∈ (h.finite_fiber y).toFinset := by
      rw [hxs]; exact Finset.mem_singleton_self x
    rw [Set.Finite.mem_toFinset] at hmem
    exact ⟨x, hmem⟩


end Jacobians.Vendor.Wallace.HolomorphicForms
