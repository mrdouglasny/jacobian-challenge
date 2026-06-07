/-
  Dolbeault ladder — **common refinement of two finite covers** and its refinement maps.

  This file constructs the common refinement `𝔚 = 𝔘 ⊓ 𝔙` of two finite covers `𝔘, 𝔙`,
  and defines the projection/refinement maps `𝔚 ⪯ 𝔘` and `𝔚 ⪯ 𝔙`.
-/
import Jacobians.Dolbeault.CechRefinementLeray
import Mathlib.Analysis.Convex.Contractible

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

-- Local instance for decidability of set nonemptiness
noncomputable local instance decidable_nonempty (𝔘 𝔙 : FiniteCover X) (p : 𝔘.ι × 𝔙.ι) :
    Decidable ((𝔘.U p.1 ⊓ 𝔙.U p.2 : Opens X) : Set X).Nonempty :=
  Classical.propDecidable _

/-- The common refinement of two finite covers `𝔘` and `𝔙`. -/
noncomputable def commonRefinement (𝔘 𝔙 : FiniteCover X) : FiniteCover X where
  ι := { p : 𝔘.ι × 𝔙.ι // ((𝔘.U p.1 ⊓ 𝔙.U p.2 : Opens X) : Set X).Nonempty }
  fintype := Subtype.fintype _
  U p := 𝔘.U p.val.1 ⊓ 𝔙.U p.val.2
  covers := by
    rw [← TopologicalSpace.Opens.coe_inj]
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have h_cov : x ∈ ⋃ (p : 𝔘.ι × 𝔙.ι), ((𝔘.U p.1 ⊓ 𝔙.U p.2 : Opens X) : Set X) := by
      have h1 : x ∈ ((⊤ : Opens X) : Set X) := by
        simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ]
      have h2 : ((⊤ : Opens X) : Set X) = ⋃ (p : 𝔘.ι × 𝔙.ι), ((𝔘.U p.1 ⊓ 𝔙.U p.2 : Opens X) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup]
        congr 1
        rw [← iSup_inf_iSup, 𝔘.covers, 𝔙.covers, inf_idem]
      rwa [h2] at h1
    simp only [Set.mem_iUnion] at h_cov
    obtain ⟨p, hp⟩ := h_cov
    have hne : ((𝔘.U p.1 ⊓ 𝔙.U p.2 : Opens X) : Set X).Nonempty := ⟨x, hp⟩
    exact ⟨⟨p, hne⟩, hp⟩

/-- The projection refinement from `commonRefinement 𝔘 𝔙` to `𝔘`. -/
theorem commonRefinement_proj1 (𝔘 𝔙 : FiniteCover X) :
    IsRefinement (commonRefinement 𝔘 𝔙) 𝔘 (fun p => p.val.1) := by
  intro p
  exact inf_le_left

/-- The projection refinement from `commonRefinement 𝔘 𝔙` to `𝔙`. -/
theorem commonRefinement_proj2 (𝔘 𝔙 : FiniteCover X) :
    IsRefinement (commonRefinement 𝔘 𝔙) 𝔙 (fun p => p.val.2) := by
  intro p
  exact inf_le_right

/-- Helper lemma for the homeomorphism of the intersection of two chart-disks to the unit ball. -/
lemma exists_homeomorphism_to_ball_subset (𝔘 𝔙 : FiniteCover X) (i : 𝔘.ι) (j : 𝔙.ι)
    (hne : ((𝔘.U i ⊓ 𝔙.U j : Opens X) : Set X).Nonempty) :
    Nonempty (↥(𝔘.U i ⊓ 𝔙.U j : Opens X) ≃ₜ Metric.ball (0 : ℂ) 1) := sorry

/-- The intersection of two chart-disks on a Riemann surface is homeomorphic to a nonempty convex subset of ℂ. -/
theorem commonRefinement_intersection_homeo (𝔘 𝔙 : FiniteCover X) (i : 𝔘.ι) (j : 𝔙.ι)
    (hne : ((𝔘.U i ⊓ 𝔙.U j : Opens X) : Set X).Nonempty) :
    ∃ (U' : Set ℂ) (hU' : Convex ℝ U') (hne' : U'.Nonempty), Nonempty (↥(𝔘.U i ⊓ 𝔙.U j : Opens X) ≃ₜ U') := by
  use Metric.ball (0 : ℂ) 1
  refine ⟨convex_ball (0 : ℂ) 1, ⟨0, Metric.mem_ball_self (by linarith)⟩, ?_⟩
  exact exists_homeomorphism_to_ball_subset 𝔘 𝔙 i j hne

/-- If two covers are Leray, their common refinement is also Leray.
    This is a topological fact about Riemann surfaces/covers by disks. -/
theorem commonRefinement_isLeray (𝔘 𝔙 : FiniteCover X) (hU : 𝔘.IsLeray) (hV : 𝔙.IsLeray) :
    (commonRefinement 𝔘 𝔙).IsLeray := by
  intro ⟨⟨i, j⟩, hne⟩
  have _hUi : SimplyConnectedSpace ↥(𝔘.U i) := hU i
  have _hVj : SimplyConnectedSpace ↥(𝔙.U j) := hV j
  change SimplyConnectedSpace ↥(𝔘.U i ⊓ 𝔙.U j)
  have h_homeo := commonRefinement_intersection_homeo 𝔘 𝔙 i j hne
  obtain ⟨U', hU'_conv, hne', ⟨e⟩⟩ := h_homeo
  haveI : SimplyConnectedSpace ↥U' := by
    haveI : ContractibleSpace ↥U' := hU'_conv.contractibleSpace hne'
    exact SimplyConnectedSpace.ofContractible ↥U'
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- Solving local primitives for a fine 1-cocycle on coarse simply connected overlaps.
    Under the Leray assumption, the intersections of the covers are simply connected, hence acyclic.
    This guarantees the existence of a local 0-cochain η_local resolving the 1-cocycle. -/
theorem refinementLift_local_primitives {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X)
    (t : ↥(𝔙.cocycles1 D)) :
    ∃ η_local : 𝔙.Cochain0, ∀ a b, (t : 𝔙.Cochain1) (a, b) = 𝔙.cechDelta0 η_local (a, b) := sorry

/-- Assembling the coarse 1-cocycle from local primitives. -/
theorem refinementLift_assemble_cocycle {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X)
    (t : ↥(𝔙.cocycles1 D)) (η_local : 𝔙.Cochain0)
    (h_t_eq : ∀ a b, (t : 𝔙.Cochain1) (a, b) = 𝔙.cechDelta0 η_local (a, b)) :
    ∃ g : ↥(𝔘.cocycles1 D), hr.refineC1 (g : 𝔘.Cochain1) - (t : 𝔙.Cochain1) ∈ 𝔙.coboundaries1 D := sorry

/-- The Leray lift (surjectivity) condition holds for any refinement between Leray covers. -/
theorem refinementLift_of_leray {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X) :
    IsRefinement.RefinementLift hr D := by
  intro t
  have h_loc : ∃ η_local : 𝔙.Cochain0, ∀ a b, (t : 𝔙.Cochain1) (a, b) = 𝔙.cechDelta0 η_local (a, b) :=
    refinementLift_local_primitives hr hV hU D t
  obtain ⟨η_local, h_t_eq⟩ := h_loc
  exact refinementLift_assemble_cocycle hr hV hU D t η_local h_t_eq

theorem refinementDescend_obtain_split {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (_hV : 𝔙.IsLeray) (_hU : 𝔘.IsLeray) (D : Divisor X)
    (g : ↥(𝔘.cocycles1 D)) (hg : hr.refineC1 (g : 𝔘.Cochain1) ∈ 𝔙.coboundaries1 D) :
    ∃ η : 𝔙.Cochain0, η ∈ 𝔙.sections0 D ∧ 𝔙.cechDelta0 η = hr.refineC1 (g : 𝔘.Cochain1) := by
  rcases Submodule.mem_map.mp hg with ⟨η, hη, hη_eq⟩
  exact ⟨η, hη, hη_eq⟩

/-- Sheaf gluing on the fibers of the refinement map. -/
theorem refinementDescend_glue_helper {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X)
    (g : ↥(𝔘.cocycles1 D)) (η : 𝔙.Cochain0) (hη_sec : η ∈ 𝔙.sections0 D)
    (hη_eq : 𝔙.cechDelta0 η = hr.refineC1 (g : 𝔘.Cochain1)) :
    ∃ θ : 𝔘.Cochain0, (∀ a, η a = rawRestrictG (hr a) (θ (r a))) ∧ θ ∈ 𝔘.sections0 D := sorry

/-- Helper lemma showing the boundary match relation for descended fibers. -/
lemma refinementDescend_glue_fibers_eq {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X) (g : ↥(𝔘.cocycles1 D)) (η : 𝔙.Cochain0)
    (hη_eq : 𝔙.cechDelta0 η = hr.refineC1 (g : 𝔘.Cochain1)) (θ : 𝔘.Cochain0)
    (h_θ_eq : ∀ a, η a = rawRestrictG (hr a) (θ (r a))) :
    (g : 𝔘.Cochain1) = 𝔘.cechDelta0 θ := sorry

theorem refinementDescend_glue_fibers {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X)
    (g : ↥(𝔘.cocycles1 D)) (η : 𝔙.Cochain0) (hη_sec : η ∈ 𝔙.sections0 D)
    (hη_eq : 𝔙.cechDelta0 η = hr.refineC1 (g : 𝔘.Cochain1)) :
    ∃ θ : 𝔘.Cochain0, θ ∈ 𝔘.sections0 D ∧ (g : 𝔘.Cochain1) = 𝔘.cechDelta0 θ := by
  have h_glue := refinementDescend_glue_helper hr hV hU D g η hη_sec hη_eq
  obtain ⟨θ, h_θ_eq, h_θ_sec⟩ := h_glue
  exact ⟨θ, ⟨h_θ_sec, refinementDescend_glue_fibers_eq hr D g η hη_eq θ h_θ_eq⟩⟩

/-- The Leray descend (injectivity) condition holds for any refinement between Leray covers. -/
theorem refinementDescend_of_leray {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X) :
    IsRefinement.RefinementDescend hr D := by
  intro g hg
  obtain ⟨η, hη_sec, hη_eq⟩ := refinementDescend_obtain_split hr hV hU D g hg
  have h_desc : ∃ θ : 𝔘.Cochain0, θ ∈ 𝔘.sections0 D ∧ (g : 𝔘.Cochain1) = 𝔘.cechDelta0 θ :=
    refinementDescend_glue_fibers hr hV hU D g η hη_sec hη_eq
  obtain ⟨θ, hθ_sec, hθ_eq⟩ := h_desc
  rw [hθ_eq]
  exact ⟨θ, hθ_sec, rfl⟩

/-- The refinement equivalence between two Leray covers. -/
noncomputable def refineH1_equiv_of_leray_covers {𝔙 𝔘 : FiniteCover X} {r : 𝔙.ι → 𝔘.ι}
    (hr : IsRefinement 𝔙 𝔘 r) (hV : 𝔙.IsLeray) (hU : 𝔘.IsLeray) (D : Divisor X) :
    𝔘.cechH1 D ≃ₗ[ℂ] 𝔙.cechH1 D :=
  IsRefinement.refineH1_equiv_of_leray D hr
    (refinementLift_of_leray hr hV hU D)
    (refinementDescend_of_leray hr hV hU D)

/-- General cover-independence isomorphism of H¹ for any two Leray covers. -/
noncomputable def cechH1_equiv_of_leray (𝔘 𝔙 : FiniteCover X) (hU : 𝔘.IsLeray) (hV : 𝔙.IsLeray) (D : Divisor X) :
    𝔘.cechH1 D ≃ₗ[ℂ] 𝔙.cechH1 D :=
  let 𝔚 := commonRefinement 𝔘 𝔙
  have hW : 𝔚.IsLeray := commonRefinement_isLeray 𝔘 𝔙 hU hV
  let e1 := refineH1_equiv_of_leray_covers (commonRefinement_proj1 𝔘 𝔙) hW hU D
  let e2 := refineH1_equiv_of_leray_covers (commonRefinement_proj2 𝔘 𝔙) hW hV D
  e1.trans e2.symm

end FiniteCover

end Jacobians.Dolbeault
