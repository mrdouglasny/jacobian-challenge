/-
# Closing G2 / G3 / G4 from the Albanese interface axioms

Proves the three former torus axioms as **theorems** from the minimal interface in
`Jacobians/Axioms/AlbaneseInterface.lean` (A1 `AX_torus_uniformization`, AK
`AX_curve_image_subgroup_isOpen`). Lives downstream of `UniversalProperty` because
G4 needs the Jacobian's topological-group structure and G3 needs the proven
line-integral naturality, both of which are only available in this richer context.

* **G2** `torus_self_albanese` — directly A1 (the uniformization *is* the
  self-Albanese presentation).
* **G4** `curve_generates_jacobian` — from AK by "open subgroup of a connected
  group = ⊤" (Gemini-verified route).
* **G3** `period_functoriality` — from A1 + the proven naturality
  `torusPullback_pathIntegral_naturality`; **restricted to A1's self-Albanese
  presentation** (the old ∀-arbitrary-`P` form is unsound — Gemini-confirmed).
  Route scaffolded; the loop-period→lattice step is the remaining work.

See `docs/planning/UNIFIED_ALBANESE_DISCHARGE_PLAN.md`.
-/
import Jacobians.UniversalProperty
import Jacobians.Axioms.AlbaneseInterface

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians.Axioms

/-! ## G2 — `torus_self_albanese` (directly A1) -/

/-- **G2, theorem.** A complex torus is its own Albanese — this is exactly the
uniformization axiom A1. -/
noncomputable def torus_self_albanese {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] :
    TorusSelfAlbanesePresentation m A :=
  AX_torus_uniformization

/-! ## G4 — `curve_generates_jacobian` (from AK: open subgroup of connected = ⊤) -/

/-- **G4, theorem.** The Abel–Jacobi image group-generates the Jacobian. From AK
(local Jacobi inversion ⇒ the generated subgroup has non-empty interior) by:
nonempty interior ⇒ open subgroup ⇒ clopen ⇒ (Jacobian connected) ⇒ `⊤`. -/
theorem curve_generates_jacobian {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < genus X) :
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤ := by
  haveI : IsTopologicalAddGroup (_root_.Jacobian X) := by
    change IsTopologicalAddGroup (Jacobians.Jacobian X)
    exact topologicalAddGroup_of_lieAddGroup
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
  haveI : SeparatelyContinuousAdd (_root_.Jacobian X) := inferInstance
  set H : AddSubgroup (_root_.Jacobian X) :=
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) with hH
  obtain ⟨U, hUopen, hUne, hUsub⟩ := AX_curve_image_subgroup_isOpen x₀ h
  obtain ⟨u₀, hu₀U⟩ := hUne
  have hu₀H : u₀ ∈ H := hUsub hu₀U
  have hHopen : IsOpen (H : Set (_root_.Jacobian X)) := by
    refine AddSubgroup.isOpen_of_mem_nhds H (g := (0 : _root_.Jacobian X)) ?_
    have hmem : (fun x => x - u₀) '' U ⊆ (H : Set (_root_.Jacobian X)) := by
      rintro _ ⟨x, hxU, rfl⟩
      exact H.sub_mem (hUsub hxU) hu₀H
    have hopen : IsOpen ((fun x => x - u₀) '' U) :=
      (Homeomorph.subRight u₀).isOpen_image.mpr hUopen
    have h0mem : (0 : _root_.Jacobian X) ∈ (fun x => x - u₀) '' U := ⟨u₀, hu₀U, by simp⟩
    exact Filter.mem_of_superset (hopen.mem_nhds h0mem) hmem
  have hHclosed : IsClosed (H : Set (_root_.Jacobian X)) :=
    AddSubgroup.isClosed_of_isOpen H hHopen
  have hclopen : IsClopen (H : Set (_root_.Jacobian X)) := ⟨hHclosed, hHopen⟩
  have huniv : (H : Set (_root_.Jacobian X)) = Set.univ :=
    hclopen.eq_univ ⟨0, H.zero_mem⟩
  exact AddSubgroup.coe_eq_univ.mp huniv

/-! ## G3 — `period_functoriality` (from A1 + proven naturality)

Restricted to A1's **self-Albanese** presentation (the old ∀-arbitrary-`P` form is
unsound — Gemini-confirmed). The containment reduces to a single per-class bridge:
the dual pullback of a source period vector is a target period vector, hence in the
target lattice. That bridge (`torusAmbientLinear_periodMapInBasis_mem`) is the
naturality + self-Albanese step (`torusPullback_pathIntegral_naturality` carries a
loop's period to `f∘loop`'s period; the self-Albanese identity of A1 puts a torus
loop period in `Λ_A`); it remains the analytic residual. -/

open Jacobians.Axioms in
/-- **Reduction step.** The dual pullback of a period *vector* equals the Albanese
coordinate of the pulled-back period *functional*: `torusAmbientLinear` shares the
`evalEquiv.symm ∘ (dualCover.symm).dualMap` tail with
`torusAlbaneseCoordinateOfFunctional`, and the basis-coordinate equiv `eX` cancels
its own inverse on `periodMap X x₀ h`. Reduces the bridge to a statement purely
about the pulled-back period functional. -/
theorem torusAmbientLinear_periodMapInBasis_eq {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (h : H1 X (Classical.arbitrary X)) :
    torusAmbientLinear f hf
        (periodMapInBasis X (Classical.arbitrary X) (jacobianBasis X) h) =
      torusAlbaneseCoordinateOfFunctional (A := A)
        ((torusPullbackOneForm f hf).dualMap
          (periodMap X (Classical.arbitrary X) h)) := by
  unfold torusAmbientLinear torusAlbaneseCoordinateOfFunctional periodMapInBasis
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.restrictScalars_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearEquiv.symm_apply_apply]

open Jacobians.Axioms in
/-- The analytic bridge for G3 (residual): the dual pullback of a source period
class lands in the target lattice. By `torusPullback_pathIntegral_naturality`
(`∮_{f∘γ}ω = ∮_γ f*ω`) the image is the period of a loop `f∘γ` in `A`, and A1's
self-Albanese identity places a torus loop period in `Λ_A`. -/
theorem torusAmbientLinear_periodMapInBasis_mem {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) (h : H1 X (Classical.arbitrary X)) :
    torusAmbientLinear f hf
        (periodMapInBasis X (Classical.arbitrary X) (jacobianBasis X) h) ∈
      (torus_self_albanese (m := m) (A := A)).toTorusPresentation.lattice := by
  rw [torusAmbientLinear_periodMapInBasis_eq]
  -- Residual: `torusAlbaneseCoordinateOfFunctional ((torusPullbackOneForm f hf).dualMap
  --   (periodMap X x₀ h)) ∈ Λ_A`.  Split:
  --   R1 (developing-map H₁-naturality): `(periodMap h) (f* ell) = torusLineIntegral ell γ_A`
  --       for a loop `γ_A : ℝ → A` representing `f∘(loop for h)` (translated to base `0`);
  --   R2 (self-Albanese loop period): `coord` of a torus loop-period functional ∈ Λ_A,
  --       from `liftCoord_eq_albanese` with `γ = const 0`.
  sorry

open Jacobians.Axioms in
/-- **G3, theorem** (modulo the analytic bridge `torusAmbientLinear_periodMapInBasis_mem`).
The source period lattice maps into A1's self-Albanese target lattice under the dual
pullback. No new axiom beyond A1 (and the residual bridge). -/
theorem period_functoriality {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup ≤
      (torus_self_albanese (m := m) (A := A)).toTorusPresentation.lattice.toAddSubgroup.comap
        (torusAmbientLinear f hf).toAddMonoidHom := by
  rintro v ⟨h, rfl⟩
  exact torusAmbientLinear_periodMapInBasis_mem f hf h

end Jacobians.RiemannSurface
