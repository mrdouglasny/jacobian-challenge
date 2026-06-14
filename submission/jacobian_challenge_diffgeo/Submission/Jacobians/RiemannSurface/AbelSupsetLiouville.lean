/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- IMPORT ORDER MATTERS: `KirovDolbeault.VanKampen` transitively imports
-- `KirovDolbeault.ProjectiveLine`, whose `RiemannSphere := OnePoint ℂ`
-- carries its own `ChartedSpace ℂ (OnePoint ℂ)` instance. Importing the
-- vendor package FIRST lets the main package's `ProjectiveLine` instances
-- (declared later) win instance resolution, so the manifold statements
-- below elaborate against the same instances as the rest of the SUP lane.
import Submission.KirovDolbeault.VanKampen
import Submission.Jacobians.RiemannSurface.AbelSupsetPencil

/-!
# Abel ⊇ lift and Liouville (SUP lane, rung S6 of `docs/planning/SUP_ROUTE.md`)

The pencil map `Φ = fiberAJ f hf : ℙ¹ → Jacobian X` is `MDifferentiable`
everywhere (S5). Here:

* **`ℙ¹` is simply connected** — `simplyConnectedSpace_projectiveLine`,
  from the Kirov two-open van Kampen port
  (`KirovDolbeault.SphereSimplyConnected` capstone + the proven
  `twoOpenVanKampen_holds` engine).

* **The lift is holomorphic** —
  `ComplexTorus.mdifferentiable_lift_of_mdifferentiable`: a continuous
  lift through the lattice covering `mk : V → V/L` of an
  `MDifferentiable` torus-valued map is itself `MDifferentiable`
  (locally the lift differs from the torus chart composite by a single
  lattice element: the difference is a continuous map into the discrete
  subgroup, hence eventually constant — no connectivity needed).

* **S6 (Liouville constancy)** — `fiberAJ_eq` / `fiberAJConstancy`: lift
  `Φ` through `ℂ^g → ℂ^g/Λ` over the simply connected `ℙ¹` (Mathlib's
  covering-lifting criterion `IsCoveringMap.existsUnique_continuousMap_lifts`
  + the Kirov-style quotient covering map), conclude the lift is constant
  on the compact connected `ℙ¹` (`MDifferentiable.apply_eq_of_compactSpace`),
  hence `Φ` is constant: the named hypothesis `FiberAJConstancy X` of the
  S3 reduction `abel_supset_of_fiberAJConstancy` HOLDS.

This file sits BELOW `Jacobians/Axioms/AbelTheorem.lean` in the import
graph (Phase-C in-place conversion pattern) and does not touch
`AX_AbelSupset`. Conditionality: standard-3 + `AX_PeriodCycleBasis`
(inherited from `ofCurveImpl`), as for the rest of the Jacobian layer.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians
open Jacobians.AbelianVariety
open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Filter Set OnePoint

/-! ## `ℙ¹` is simply connected -/

/-- **`ℙ¹` is simply connected**: the Kirov two-open van Kampen capstone for
`OnePoint ℂ` (`ProjectiveLine` is an `abbrev` for `OnePoint ℂ`). -/
theorem simplyConnectedSpace_projectiveLine :
    SimplyConnectedSpace ProjectiveLine :=
  Jacobians.RiemannSphere.simplyConnectedSpace_onePoint_of_vanKampen
    Jacobians.RiemannSphere.VanKampen.twoOpenVanKampen_holds

/-! ## Holomorphy of continuous lifts through the lattice covering -/


/-- **A continuous lift of a holomorphic torus-valued map is holomorphic.**
If `Φ : M → V/L` is `MDifferentiable` on a complex manifold `M` and
`F : M → V` is a continuous pointwise lift (`mk ∘ F = Φ`), then `F` is
`MDifferentiable`: near any point, `F` differs from the torus-chart
composite `extChartAt (Φ y₀) ∘ Φ` by a single lattice element (the
difference is continuous with values in the discrete subgroup `L`, hence
eventually constant). -/
theorem _root_.Jacobians.AbelianVariety.ComplexTorus.mdifferentiable_lift_of_mdifferentiable
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
    {Φ : M → ComplexTorus V L} (hΦ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, V) Φ)
    {F : M → V} (hFc : Continuous F)
    (hlift : ∀ x, (QuotientAddGroup.mk' L.toAddSubgroup (F x) :
      ComplexTorus V L) = Φ x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, V) F := by
  intro y₀
  set q : ComplexTorus V L := Φ y₀ with hq
  -- the torus-chart composite is `MDifferentiableAt`
  have hw_md : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, V)
      (fun y => extChartAt 𝓘(ℂ, V) q (Φ y)) y₀ := by
    have hext : ContMDiffAt 𝓘(ℂ, V) 𝓘(ℂ, V) ω (extChartAt 𝓘(ℂ, V) q) q :=
      contMDiffAt_extChartAt (n := ω)
    exact (hext.mdifferentiableAt (by simp)).comp y₀ (hΦ y₀)
  -- the chart composite is itself a pointwise lift near `y₀`
  have hsrc : ∀ᶠ y in 𝓝 y₀, Φ y ∈ (extChartAt 𝓘(ℂ, V) q).source :=
    (hΦ y₀).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source q).mem_nhds (mem_extChartAt_source q))
  have hmkw : ∀ᶠ y in 𝓝 y₀,
      (QuotientAddGroup.mk' L.toAddSubgroup (extChartAt 𝓘(ℂ, V) q (Φ y)) :
        ComplexTorus V L) = Φ y := by
    filter_upwards [hsrc] with y hy
    have hwt : extChartAt 𝓘(ℂ, V) q (Φ y) ∈ (extChartAt 𝓘(ℂ, V) q).target :=
      (extChartAt 𝓘(ℂ, V) q).map_source hy
    have hsymm := ComplexTorus.extChartAt_symm_eq_quotient_mk q
      ((ComplexTorus.mem_extChartAt_target_iff q).mp hwt)
    have hleft := (extChartAt 𝓘(ℂ, V) q).left_inv hy
    rw [hsymm] at hleft
    exact hleft
  -- the difference is a continuous map into the discrete lattice
  have hgΛ : ∀ᶠ y in 𝓝 y₀,
      F y - extChartAt 𝓘(ℂ, V) q (Φ y) ∈ L.toAddSubgroup := by
    filter_upwards [hmkw] with y hy
    have hzero : (QuotientAddGroup.mk' L.toAddSubgroup
        (F y - extChartAt 𝓘(ℂ, V) q (Φ y)) : ComplexTorus V L) = 0 := by
      rw [map_sub, hlift y, hy, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp hzero
  have hgc : ContinuousAt (fun y => F y - extChartAt 𝓘(ℂ, V) q (Φ y)) y₀ :=
    hFc.continuousAt.sub
      ((continuousAt_extChartAt q).comp (hΦ y₀).continuousAt)
  -- the lattice value at the center is isolated
  set lam0 : V := F y₀ - extChartAt 𝓘(ℂ, V) q (Φ y₀) with hlam0
  have hlam0Λ : lam0 ∈ L.toAddSubgroup := hgΛ.self_of_nhds
  haveI : DiscreteTopology L.toAddSubgroup :=
    (inferInstance : DiscreteTopology L)
  obtain ⟨U, hUopen, hUeq⟩ : ∃ U : Set V, IsOpen U ∧
      (Subtype.val ⁻¹' U : Set L.toAddSubgroup) = {⟨lam0, hlam0Λ⟩} := by
    have h := isOpen_discrete ({⟨lam0, hlam0Λ⟩} : Set L.toAddSubgroup)
    rwa [isOpen_induced_iff] at h
  have hlam0U : lam0 ∈ U := by
    have h : (⟨lam0, hlam0Λ⟩ : L.toAddSubgroup) ∈
        (Subtype.val ⁻¹' U : Set L.toAddSubgroup) := by
      rw [hUeq]
      rfl
    exact h
  -- hence the difference is eventually the constant `lam0`
  have hev : ∀ᶠ y in 𝓝 y₀, F y = extChartAt 𝓘(ℂ, V) q (Φ y) + lam0 := by
    have hUev : ∀ᶠ y in 𝓝 y₀,
        F y - extChartAt 𝓘(ℂ, V) q (Φ y) ∈ U :=
      hgc (hUopen.mem_nhds hlam0U)
    filter_upwards [hUev, hgΛ] with y hyU hyΛ
    have hmem : (⟨F y - extChartAt 𝓘(ℂ, V) q (Φ y), hyΛ⟩ :
        L.toAddSubgroup) ∈ (Subtype.val ⁻¹' U : Set L.toAddSubgroup) := hyU
    rw [hUeq, Set.mem_singleton_iff] at hmem
    have heq : F y - extChartAt 𝓘(ℂ, V) q (Φ y) = lam0 :=
      congrArg Subtype.val hmem
    exact sub_eq_iff_eq_add'.mp heq
  exact (hw_md.add (mdifferentiableAt_const (c := lam0))).congr_of_eventuallyEq
    hev

/-! ## S6: Liouville constancy of the pencil map -/

namespace MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **S6 (Liouville constancy).** The Jacobi pencil map is constant on
`ℙ¹`: it is `MDifferentiable` (S5), lifts through the lattice covering
`ℂ^g → ℂ^g/Λ` over the simply connected `ℙ¹`, the lift is holomorphic
(`mdifferentiable_lift_of_mdifferentiable`) hence constant on the compact
connected `ℙ¹`. -/
theorem fiberAJ_eq (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    (y y' : ProjectiveLine) : fiberAJ f hf y = fiberAJ f hf y' := by
  classical
  haveI : SimplyConnectedSpace ProjectiveLine :=
    simplyConnectedSpace_projectiveLine
  haveI : LocPathConnectedSpace ProjectiveLine :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := ProjectiveLine)
  -- the ambient (un-ULifted) pencil map
  set Φd : ProjectiveLine → JacobianAmbient X :=
    fun z => (fiberAJ f hf z).down with hΦd
  have hdown : MDifferentiable (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (ULift.down : Jacobian X → JacobianAmbient X) :=
    (Jacobian.contMDiff_ulift_down (X := X)).mdifferentiable (by simp)
  have hΦd_md : MDifferentiable 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) Φd :=
    hdown.comp (mdifferentiable_fiberAJ f hf)
  have hΦd_cont : Continuous Φd :=
    continuous_iff_continuousAt.mpr fun z => (hΦd_md z).continuousAt
  -- the lattice covering
  set L := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
    with hL
  haveI : DiscreteTopology L.toAddSubgroup :=
    (inferInstance : DiscreteTopology L)
  have cov : IsCoveringMap (QuotientAddGroup.mk' L.toAddSubgroup :
      (Fin (genus X) → ℂ) → JacobianAmbient X) :=
    (AddSubgroup.isAddQuotientCoveringMap_of_comm L.toAddSubgroup
      DiscreteTopology.isDiscrete).isCoveringMap
  -- lift the pencil map over the simply connected `ℙ¹`
  obtain ⟨e₀, he₀⟩ :=
    QuotientAddGroup.mk'_surjective L.toAddSubgroup (Φd (∞ : ProjectiveLine))
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨Φd, hΦd_cont⟩
      (∞ : ProjectiveLine) e₀ (by simpa using he₀)
  have hlift : ∀ z, (QuotientAddGroup.mk' L.toAddSubgroup (F z) :
      JacobianAmbient X) = Φd z := by
    intro z
    simpa using congrFun hFlift z
  -- the lift is holomorphic, hence constant by compactness
  have hFmd : MDifferentiable 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (F : ProjectiveLine → Fin (genus X) → ℂ) :=
    ComplexTorus.mdifferentiable_lift_of_mdifferentiable hΦd_md
      F.continuous hlift
  have hconst : (F : ProjectiveLine → Fin (genus X) → ℂ) y = F y' :=
    hFmd.apply_eq_of_compactSpace y y'
  -- transport back to the Jacobian
  have hd : Φd y = Φd y' := by
    rw [← hlift y, ← hlift y', hconst]
  exact ULift.down_injective hd

end MeromorphicFunctionField

open MeromorphicFunctionField in
/-- **The S3 named hypothesis HOLDS**: the Jacobi pencil map is constant
for every nonconstant meromorphic function — the output of the Liouville
route (S4–S6). -/
theorem fiberAJConstancy (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : FiberAJConstancy X :=
  fun f hf y y' => fiberAJ_eq f hf y y'

end Jacobians.RiemannSurface
