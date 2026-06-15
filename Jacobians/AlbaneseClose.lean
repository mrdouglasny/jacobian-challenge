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
/-- The invariant torus one-form has zero line integral on the constant zero loop. -/
theorem torusLineIntegral_const_zero {m : ℕ} {A : Type*} [TopologicalSpace A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (ell : TorusHolomorphicOneForm m A) :
    torusLineIntegral (A := A) ell (fun _ => (0 : A)) = 0 := by
  unfold torusLineIntegral
  calc
    ∫ t in (0 : ℝ)..1, ((torusInvariantOneFormSection (A := A) ell).toFun ((fun _ => (0 : A)) t))
        (torusPathSpeed (fun _ => (0 : A)) t)
      = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
          refine intervalIntegral.integral_congr (fun t ht => ?_)
          have hderiv :
              deriv (↑(chartAt (H := Fin m → ℂ) (0 : A)) ∘ fun _ : ℝ => (0 : A)) t = 0 := by
            change deriv (fun _ : ℝ => (chartAt (H := Fin m → ℂ) (0 : A)) (0 : A)) t = 0
            simp
          rw [show torusPathSpeed (fun _ : ℝ => (0 : A)) t =
              deriv (↑(chartAt (H := Fin m → ℂ) (0 : A)) ∘ fun _ : ℝ => (0 : A)) t by
                simp [torusPathSpeed]]
          rw [hderiv]
          exact ((torusInvariantOneFormSection (A := A) ell).toFun (0 : A)).map_zero
    _ = 0 := by simp

open Jacobians.Axioms in
/-- A torus loop period represents a lattice element in any self-Albanese presentation. -/
theorem torusAlbaneseCoordinateOfFunctional_mem_lattice_of_loopPeriod
    {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (S : TorusSelfAlbanesePresentation m A) (γ : ℝ → A)
    (hγ0 : γ 0 = 0) (hγ1 : γ 1 = 0)
    {I : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ}
    (hI : ∀ ell, I ell = torusLineIntegral (A := A) ell γ) :
    torusAlbaneseCoordinateOfFunctional (A := A) I ∈ S.lattice := by
  have hconst : ∀ ell,
      (0 : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ) ell =
        torusLineIntegral (A := A) ell (fun _ => (0 : A)) := by
    intro ell
    simp [torusLineIntegral_const_zero]
  have hsum : S.liftCoord (0 : A) +
      torusAlbaneseCoordinateOfFunctional (A := A) I ∈ S.lattice := by
    have h :=
      S.liftCoord_eq_albanese
        (I := (0 : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ))
        (I₀ := I) (γ := fun _ => (0 : A)) (γ₀ := γ) (a := (0 : A))
        (by simp) (by simp) hγ0 hγ1 hconst hI
    simpa [torusAlbaneseCoordinateOfFunctional] using h
  have hlift0 : S.liftCoord (0 : A) ∈ S.lattice := by
    have h :=
      S.liftCoord_eq_albanese
        (I := (0 : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ))
        (I₀ := (0 : TorusHolomorphicOneForm m A →ₗ[ℂ] ℂ))
        (γ := fun _ => (0 : A)) (γ₀ := fun _ => (0 : A)) (a := (0 : A))
        (by simp) (by simp) (by simp) (by simp) hconst hconst
    simpa [torusAlbaneseCoordinateOfFunctional] using h
  have hsub := S.lattice.sub_mem hsum hlift0
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub

open Jacobians.Axioms in
/-- Pulling back an invariant torus one-form and integrating it around a smooth source loop
equals integrating the original invariant form around the image loop. -/
theorem torusPullback_lineIntegral_naturality_of_closedSmoothLoop
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (γ : ℝ → X) (hγ : _root_.Jacobians.IsClosedSmoothLoop γ)
    (ell : TorusHolomorphicOneForm m A) :
    _root_.Jacobians.lineIntegral
        (Jacobians.Bridge.bridgeKDFormEquiv ((torusPullbackOneForm f hf) ell)) γ =
      torusLineIntegral (A := A) ell (f ∘ γ) := by
  have hbridge :
      Jacobians.Bridge.bridgeForm ((torusPullbackOneForm f hf) ell) =
        (torusPullbackKirovOneForm f hf) ell := by
    change (Jacobians.Bridge.bridgeFormEquiv (X := X))
        ((Jacobians.Bridge.bridgeFormEquiv (X := X)).symm
          ((torusPullbackKirovOneForm f hf) ell)) =
      (torusPullbackKirovOneForm f hf) ell
    exact LinearEquiv.apply_symm_apply (Jacobians.Bridge.bridgeFormEquiv (X := X))
      ((torusPullbackKirovOneForm f hf) ell)
  rw [Jacobians.Bridge.port_lineIntegral_bridgeKD, hbridge]
  unfold Jacobians.Vendor.Kirov.lineIntegral torusLineIntegral
  refine intervalIntegral.integral_congr (fun t _ht => ?_)
  change
    ((torusInvariantOneFormSection (A := A) ell).toFun (f (γ t))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t))
        (_root_.Jacobians.pathSpeed γ t) =
      (torusInvariantOneFormSection (A := A) ell).toFun (f (γ t))
        (torusPathSpeed (f ∘ γ) t)
  rw [Jacobians.Bridge.port_pathSpeed_eq]
  rw [ContinuousLinearMap.comp_apply,
    torusPathSpeed_comp_eq_mfderiv f hf γ t
      hγ.cont.continuousAt (hγ.diff t _ht)]

/-- Evaluating an invariant torus one-form after translating both the basepoint and tangent
vector by the same group translation does not change its value. -/
private theorem torusInvariantOneFormSection_translate
    {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (ell : TorusHolomorphicOneForm m A) (a b : A)
    (v : TangentSpace 𝓘(ℂ, Fin m → ℂ) b) :
    (torusInvariantOneFormSection (A := A) ell).toFun (a + b)
      ((mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => a + y) b) v) =
    (torusInvariantOneFormSection (A := A) ell).toFun b v := by
  have h1 : MDifferentiableAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ)
      (fun y : A => -(a + b) + y) (a + b) :=
    by
      simpa using (contMDiffAt_const.add contMDiffAt_id).mdifferentiableAt
        (by decide : ω ≠ 0)
  have h2 : MDifferentiableAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ)
      (fun y : A => a + y) b :=
    by
      simpa using (contMDiffAt_const.add contMDiffAt_id).mdifferentiableAt
        (by decide : ω ≠ 0)
  have hcomp :
      (mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => -(a + b) + y) (a + b)).comp
        (mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => a + y) b) =
      mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => -b + y) b := by
    rw [← mfderiv_comp b h1 h2]
    congr 1
    ext y
    simp [add_assoc]
  have hcompv :
      (mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => -(a + b) + y) (a + b))
        (((mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => a + y) b)) v) =
      (mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) (fun y : A => -b + y) b) v := by
    exact congrArg (fun L => L v) hcomp
  unfold torusInvariantOneFormSection
  simp only [ContinuousLinearMap.comp_apply]
  simpa using congrArg
    (fun w =>
      (LinearMap.toContinuousLinearMap ell)
        ((Bundle.Trivialization.continuousLinearMapAt ℂ
          (trivializationAt (Fin m → ℂ) (TangentSpace 𝓘(ℂ, Fin m → ℂ)) (0 : A))
          (0 : A)) w))
    hcompv

/-- Chain rule for `torusPathSpeed` when both source and target are the same complex torus model. -/
private theorem torusPathSpeed_comp_eq_mfderiv_self
    {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (g : A → A) (hg : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω g)
    (γ : ℝ → A) (t : ℝ) (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := Fin m → ℂ) (γ t)).toFun ∘ γ) t) :
    torusPathSpeed (g ∘ γ) t =
      mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) g (γ t)
        (torusPathSpeed γ t) := by
  set φX := chartAt (H := Fin m → ℂ) (γ t) with hφX_def
  set φY := chartAt (H := Fin m → ℂ) (g (γ t)) with hφY_def
  set gLoc : (Fin m → ℂ) → (Fin m → ℂ) := fun z => φY (g (φX.symm z)) with hgLoc_def
  set gX : ℝ → (Fin m → ℂ) := φX.toFun ∘ γ with hgX_def
  set gY : ℝ → (Fin m → ℂ) := φY.toFun ∘ (g ∘ γ) with hgY_def
  have hγtX : γ t ∈ φX.source := mem_chart_source (Fin m → ℂ) (γ t)
  have hγ_source : ∀ᶠ s in nhds t, γ s ∈ φX.source :=
    hγ_cont.eventually (φX.open_source.mem_nhds hγtX)
  have hEq : gY =ᶠ[nhds t] gLoc ∘ gX := by
    filter_upwards [hγ_source] with s hs
    simp only [hgY_def, hgLoc_def, hgX_def, Function.comp_apply]
    congr 2
    exact (φX.left_inv hs).symm
  have hg_mdiff : MDifferentiableAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) g (γ t) :=
    hg.mdifferentiableAt (by decide : ω ≠ 0)
  have hgLoc_diff_ℂ : DifferentiableAt ℂ gLoc (gX t) := by
    have h1 := hg_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hgLoc_hasFD_ℂ : HasFDerivAt gLoc (fderiv ℂ gLoc (gX t)) (gX t) :=
    hgLoc_diff_ℂ.hasFDerivAt
  have hgLoc_hasFD_ℝ : HasFDerivAt gLoc
      ((fderiv ℂ gLoc (gX t)).restrictScalars ℝ) (gX t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hgLoc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hgLoc_hasFD_ℂ
  have hgLoc_diff_ℝ : DifferentiableAt ℝ gLoc (gX t) :=
    hgLoc_hasFD_ℝ.differentiableAt
  have hgLoc_fderiv_ℝ : fderiv ℝ gLoc (gX t) =
      (fderiv ℂ gLoc (gX t)).restrictScalars ℝ :=
    hgLoc_hasFD_ℝ.fderiv
  have h_chain : fderiv ℝ (gLoc ∘ gX) t =
      (fderiv ℝ gLoc (gX t)).comp (fderiv ℝ gX t) :=
    fderiv_comp t hgLoc_diff_ℝ hγ_diff
  have h_mfderiv :
      mfderiv 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) g (γ t) = fderiv ℂ gLoc (gX t) := by
    rw [hg_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
  rw [h_mfderiv]
  change fderiv ℝ ((chartAt (H := Fin m → ℂ) ((g ∘ γ) t)).toFun ∘ (g ∘ γ)) t 1 =
    fderiv ℂ gLoc (gX t) (torusPathSpeed γ t)
  have h_gY : (chartAt (H := Fin m → ℂ) ((g ∘ γ) t)).toFun ∘ (g ∘ γ) = gY := rfl
  rw [h_gY, hEq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
    hgLoc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
  rfl

/-- Chart-pullback differentiability for the image of a smooth source loop under a holomorphic
map into a complex torus. -/
private theorem torusComp_chartDifferentiableAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (γ : ℝ → X) (hγ : _root_.Jacobians.IsClosedSmoothLoop γ) (t : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    DifferentiableAt ℝ ((chartAt (H := Fin m → ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ)) t := by
  set φX := chartAt (H := ℂ) (γ t)
  set φA := chartAt (H := Fin m → ℂ) (f (γ t))
  set fLoc : ℂ → Fin m → ℂ := fun z => φA (f (φX.symm z))
  set gX : ℝ → ℂ := φX.toFun ∘ γ
  have hγ_source : ∀ᶠ s in nhds t, γ s ∈ φX.source :=
    hγ.cont.continuousAt.eventually
      (φX.open_source.mem_nhds (mem_chart_source ℂ (γ t)))
  have hEq : (φA.toFun ∘ (f ∘ γ)) =ᶠ[nhds t] fLoc ∘ gX := by
    filter_upwards [hγ_source] with s hs
    simp only [Function.comp_apply]
    congr 2
    exact (φX.left_inv hs).symm
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t) :=
    hf.mdifferentiableAt (by decide : ω ≠ 0)
  have hfLoc_diff_ℂ : DifferentiableAt ℂ fLoc (gX t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hfLoc_diff_ℝ : DifferentiableAt ℝ fLoc (gX t) :=
    hfLoc_diff_ℂ.restrictScalars ℝ
  have hgX_diff : DifferentiableAt ℝ gX t := hγ.diff t ht
  exact (Filter.EventuallyEq.differentiableAt_iff hEq).mpr
    (hfLoc_diff_ℝ.comp t hgX_diff)

open Jacobians.Axioms in
/-- Invariant torus one-forms have translation-invariant line integrals. -/
theorem torusLineIntegral_translate {m : ℕ} {A : Type*} [TopologicalSpace A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (ell : TorusHolomorphicOneForm m A) (γ : ℝ → A) (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := Fin m → ℂ) (γ t)).toFun ∘ γ) t)
    (a : A) :
    torusLineIntegral (A := A) ell ((fun y : A => a + y) ∘ γ) =
      torusLineIntegral (A := A) ell γ := by
  have ha : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun y : A => a + y) :=
    contMDiff_const.add contMDiff_id
  unfold torusLineIntegral
  refine intervalIntegral.integral_congr (fun t _ht => ?_)
  change ((torusInvariantOneFormSection (A := A) ell).toFun (((fun y : A => a + y) ∘ γ) t))
      (torusPathSpeed (((fun y : A => a + y) ∘ γ)) t) =
    ((torusInvariantOneFormSection (A := A) ell).toFun (γ t))
      (torusPathSpeed γ t)
  rw [torusPathSpeed_comp_eq_mfderiv_self (g := fun y : A => a + y) ha γ t
    hγ_cont.continuousAt (hγ_diff t _ht)]
  simpa [Function.comp_apply] using
    torusInvariantOneFormSection_translate (A := A) ell a (γ t) (torusPathSpeed γ t)

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
  obtain ⟨γ, hγ⟩ :=
    (analyticLoopsGenerateH1 (Classical.arbitrary X)).exists_loop h
  obtain ⟨lp, hlp, hperiod⟩ :=
    exists_isClosedSmoothLoop_lineIntegral_eq_canonicalArcIntegral
      (Classical.arbitrary X) γ
  let γA : ℝ → A := (fun y : A => -f (lp 0) + y) ∘ (f ∘ lp)
  have hγA0 : γA 0 = 0 := by
    simp [γA]
  have hγA1 : γA 1 = 0 := by
    simp [γA, hlp.closed]
  have hI : ∀ ell,
      ((torusPullbackOneForm f hf).dualMap
        (periodMap X (Classical.arbitrary X) h)) ell =
        torusLineIntegral (A := A) ell γA := by
    intro ell
    calc
      ((torusPullbackOneForm f hf).dualMap
          (periodMap X (Classical.arbitrary X) h)) ell
          = periodMap X (Classical.arbitrary X) h ((torusPullbackOneForm f hf) ell) := by
              rfl
      _ = canonicalArcIntegral γ.arc ((torusPullbackOneForm f hf) ell) := by
        rw [← hγ]
        simpa [periodMap] using
          loopIntegralToH1_loopToHomology_apply (Classical.arbitrary X) γ
            ((torusPullbackOneForm f hf) ell)
      _ = _root_.Jacobians.lineIntegral
            (Jacobians.Bridge.bridgeKDFormEquiv ((torusPullbackOneForm f hf) ell)) lp := by
        symm
        exact hperiod _
      _ = torusLineIntegral (A := A) ell (f ∘ lp) :=
        torusPullback_lineIntegral_naturality_of_closedSmoothLoop f hf lp hlp ell
      _ = torusLineIntegral (A := A) ell γA := by
        symm
        simpa [γA, Function.comp_assoc] using
          torusLineIntegral_translate (A := A) (ell := ell) (γ := f ∘ lp)
            (hf.continuous.comp hlp.cont)
            (fun t ht => torusComp_chartDifferentiableAt f hf lp hlp t ht)
            (-f (lp 0))
  simpa using
    torusAlbaneseCoordinateOfFunctional_mem_lattice_of_loopPeriod
      (S := torus_self_albanese (m := m) (A := A)) γA hγA0 hγA1 hI

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
