import Jacobians.Axioms.TorusAlbanese
import Jacobians.Axioms.AlbaneseInterface

/-!
# The Jacobian / Albanese universal property

Buzzard's Jacobian Challenge (`Jacobians/Challenge.lean`) pins the Jacobian
*operationally* — via functoriality of `pushforward`/`pullback`, the degree
identity `pushforward f ∘ pullback f = deg f • id`, Abel injectivity
(`ofCurve_inj`), and the genus-0 homeomorphism — but it never states the
*categorical* universal property that characterizes `(Jacobian X, ofCurve x₀)`
up to unique isomorphism. This file supplies that pin.

`IsJacobian x₀ J aj` says: `aj : X → J` is a holomorphic map from the pointed
compact connected Riemann surface `(X, x₀)` into a complex torus `J`, sending
`x₀ ↦ 0`, and *universal* among such maps — every pointed holomorphic map
`f : X → A` to a complex torus factors **uniquely** through `aj` by a holomorphic
group homomorphism. This is the Albanese universal property specialized to a
curve (where Albanese = Jacobian).

## Main definitions

* `Jacobians.IsJacobian` — the universal property, as a `Prop`-valued structure.

## Design notes

* A *complex torus* of complex dimension `n` is encoded as a **compact connected
  complex Lie group modeled on `Fin n → ℂ`** (`CompactSpace`, `ConnectedSpace`,
  `ChartedSpace (Fin n → ℂ)`, `IsManifold 𝓘(ℂ, Fin n → ℂ) ω`, `AddGroup`,
  `LieAddGroup 𝓘(ℂ, Fin n → ℂ) ω`). The Jacobian `J` has dimension `g` (its genus);
  the universal property quantifies over targets `A` of **any** dimension `m`. The
  curve `X` itself is a 1-dimensional manifold, modeled on `ℂ` (`𝓘(ℂ)`).
  Commutativity is **not** assumed: a compact connected complex Lie group is
  automatically abelian, so `AddGroup` suffices.
* Uniqueness is stated as `∃!` over bundled homomorphisms `J →+ A` together with
  a holomorphicity conjunct; `AddMonoidHom` extensionality plus the fact that
  `aj '' X` topologically generates `J` make this the morphism-level uniqueness
  that yields a *biholomorphic group isomorphism* between any two instances
  (categoricity).
* Basepoint discipline: `f x₀ = 0` is a hypothesis on the test map and
  `φ 0 = 0` is free from `AddMonoidHom`, so the factorization is automatically
  pointed.

The goal `IsJacobian x₀ (Jacobian X) (ofCurve x₀)` — that Buzzard's concrete
`Jacobian`/`ofCurve` satisfy this property — is the categoricity theorem that
closes the def-degeneracy gap categorically. **It is PROVED below as
`ofCurve_isJacobian` (2026-06-05):** for genus > 0, every pointed holomorphic
`f : X → A` to a complex torus factors uniquely through `ofCurve` by a
holomorphic group hom (genuine `∃!`). The `ConnectedSpace (Jacobian X)`
prerequisite is supplied (a torus is connected); the proof rests on the vetted
minimal Albanese interface — A1 `AX_torus_uniformization` + AK
`AX_curve_image_subgroup_isOpen` (the former three torus axioms
`AX_torus_self_albanese` / `AX_period_functoriality` / `AX_curve_generates_jacobian`
were proved as theorems and retired in the 2026-06-14 repoint refactor;
`AX_torus_oneforms_dualCover` discharged #232, `AX_torus_descent_holo` 2026-06-06),
and is `#print axioms`-clean (no `sorryAx`). The original proof
plan (lemma DAG, vetted-axiom leaves, effort) is in
`docs/universal-property-proof-plan.md`.

## Vetting

Statement vetted **2026-06-02** (cross-model, per the project axiom/statement
protocol): **Gemini** (gemini-3-pro-preview) — *Sound*: correct categorical UP,
categoricity holds, genus-0 boundary correct (`J = {0}` is the right answer by
Liouville), basepoint handling correct; flagged `AddCommGroup` as redundant →
relaxed to `AddGroup`; `[T2Space]` added to `X`, `J`, `A` (a complex torus is
Hausdorff; matches Buzzard's API). **Codex** — flagged that the original statement
modeled `J` and the target on `ChartedSpace ℂ` (1-dimensional), so it only
typechecked for genus-1 Jacobians; **fixed** by parametrizing the model spaces as
`Fin g → ℂ` (for `J`) and `Fin m → ℂ` (for targets `A`), so it now applies to the
genus-`g` Jacobian for all `g`.

## References

* Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1 & 11
  (the Albanese / universal property).
* Arbarello–Cornalba–Griffiths–Harris, *Geometry of Algebraic Curves I*,
  Ch. I (the Jacobian of a curve and Abel–Jacobi).

## Provenance

The universal-property characterization was proposed on the Lean Zulip
(`#Autoformalization > Jacobian challenge`, 2026-04-19) by **Michael Stoll** —
including the formulation over *complex tori* used here — as the way to rule out
hack solutions, and implemented in an algebraic-geometry variant
(`exists_unique_ofCurve_comp`) by **Christian Merten** (2026-04-20). This
complex-analytic formalization (`IsJacobian` / `ofCurve_isJacobian` /
`isJacobian_unique`) was developed independently.
-/

open scoped Manifold ContDiff Topology

namespace Jacobians

open Jacobians.Axioms
open Jacobians.RiemannSurface

/-- **The Jacobian / Albanese universal property.**

`IsJacobian x₀ J aj` holds when `aj : X → J` is a holomorphic map from the
pointed compact connected Riemann surface `(X, x₀)` to a complex torus `J`
(compact connected complex Lie group) with `aj x₀ = 0`, *universal* among such:
every pointed holomorphic map `f : X → A` to a complex torus factors uniquely
through `aj` by a holomorphic group homomorphism. This characterizes
`(J, aj)` up to unique isomorphism. -/
structure IsJacobian
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    {g : ℕ} (J : Type*) [TopologicalSpace J] [T2Space J] [CompactSpace J] [ConnectedSpace J]
    [ChartedSpace (Fin g → ℂ) J] [AddGroup J]
    [IsManifold 𝓘(ℂ, Fin g → ℂ) ω J] [LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω J]
    (aj : X → J) : Prop where
  /-- The Abel–Jacobi map is holomorphic. -/
  aj_holo : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin g → ℂ) ω aj
  /-- It sends the basepoint to the identity of the torus. -/
  aj_base : aj x₀ = 0
  /-- Universal property: every pointed holomorphic map `f : X → A` to a complex
  torus (of any dimension `m`) factors uniquely through `aj` by a holomorphic
  group homomorphism. -/
  universal :
    ∀ {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
      [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A), ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f → f x₀ = 0 →
      ∃! φ : J →+ A, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (φ : J → A) ∧
        ∀ x, f x = φ (aj x)

/-- Multivariable target version of Kirov's path-speed chain rule: the chart
velocity of `f ∘ γ` in the target torus is `mfderiv f` applied to the chart
velocity of `γ` on the curve. -/
theorem torusPathSpeed_comp_eq_mfderiv {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (γ : ℝ → X) (t : ℝ)
    (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    torusPathSpeed (f ∘ γ) t =
      mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t)
        (Vendor.Kirov.pathSpeed γ t) := by
  set φ_X := chartAt (H := ℂ) (γ t) with hφ_X_def
  set φ_A := chartAt (H := Fin m → ℂ) (f (γ t)) with hφ_A_def
  set f_loc : ℂ → (Fin m → ℂ) := fun z => φ_A (f (φ_X.symm z)) with hf_loc_def
  set g_X : ℝ → ℂ := φ_X.toFun ∘ γ with hg_X_def
  set g_A : ℝ → (Fin m → ℂ) := φ_A.toFun ∘ (f ∘ γ) with hg_A_def
  have hγt_X : γ t ∈ φ_X.source := mem_chart_source ℂ (γ t)
  have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
    hγ_cont.eventually (φ_X.open_source.mem_nhds hγt_X)
  have h_eq : g_A =ᶠ[𝓝 t] f_loc ∘ g_X := by
    filter_upwards [hγ_source] with s hs
    simp only [hg_A_def, hf_loc_def, hg_X_def, Function.comp_apply]
    congr 2
    exact (φ_X.left_inv hs).symm
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t) :=
    hf.mdifferentiableAt (by decide : ω ≠ 0)
  have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
    hf_loc_diff_ℂ.hasFDerivAt
  have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
      ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hf_loc_hasFD_ℂ
  have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
    hf_loc_hasFD_ℝ.differentiableAt
  have hf_loc_fderiv_ℝ : fderiv ℝ f_loc (g_X t) =
      (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ :=
    hf_loc_hasFD_ℝ.fderiv
  have h_chain : fderiv ℝ (f_loc ∘ g_X) t =
      (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) :=
    fderiv_comp t hf_loc_diff_ℝ hγ_diff
  have h_mfderiv :
      mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t) = fderiv ℂ f_loc (g_X t) := by
    rw [hf_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
  rw [h_mfderiv]
  change fderiv ℝ ((chartAt (H := Fin m → ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ)) t 1 =
    fderiv ℂ f_loc (g_X t) (Vendor.Kirov.pathSpeed γ t)
  have h_gA : (chartAt (H := Fin m → ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ) = g_A := rfl
  rw [h_gA, h_eq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
      hf_loc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
  rfl

/-- F2: line-integral naturality for the real torus pullback form along the
canonical bridge path. -/
theorem torusPullback_pathIntegral_naturality {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (x₀ p : X) (ell : TorusHolomorphicOneForm m A) :
    ((torusPullbackOneForm f hf).dualMap
        (Axioms.pathIntegralBasepointFunctional X x₀ p)) ell =
      torusLineIntegral ell (f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ p) := by
  classical
  let γ : ℝ → X := Jacobians.Bridge.bridgePath (X := X) x₀ p
  have hbridge :
      Jacobians.Bridge.bridgeForm ((torusPullbackOneForm f hf) ell) =
        (torusPullbackKirovOneForm f hf) ell := by
    change (Jacobians.Bridge.bridgeFormEquiv (X := X))
        ((Jacobians.Bridge.bridgeFormEquiv (X := X)).symm
          ((torusPullbackKirovOneForm f hf) ell)) =
      (torusPullbackKirovOneForm f hf) ell
    exact LinearEquiv.apply_symm_apply (Jacobians.Bridge.bridgeFormEquiv (X := X))
      ((torusPullbackKirovOneForm f hf) ell)
  change Axioms.pathIntegralBasepointFunctional X x₀ p
      ((torusPullbackOneForm f hf) ell) =
    torusLineIntegral ell (f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ p)
  change canonicalArcIntegral (Jacobians.Bridge.bridgePathArc (X := X) x₀ p)
      ((torusPullbackOneForm f hf) ell) =
    torusLineIntegral ell (f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ p)
  rw [← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
    (X := X) x₀ p ((torusPullbackOneForm f hf) ell)]
  change Vendor.Kirov.lineIntegral
      (Jacobians.Bridge.bridgeForm ((torusPullbackOneForm f hf) ell)) γ =
    torusLineIntegral ell (f ∘ γ)
  rw [hbridge]
  unfold Vendor.Kirov.lineIntegral torusLineIntegral
  refine intervalIntegral.integral_congr (fun t _ht => ?_)
  dsimp only [γ, Function.comp_apply]
  change
    ((torusInvariantOneFormSection (A := A) ell).toFun (f (γ t))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) f (γ t))
        (Vendor.Kirov.pathSpeed γ t) =
      (torusInvariantOneFormSection (A := A) ell).toFun (f (γ t))
        (torusPathSpeed (f ∘ γ) t)
  rw [ContinuousLinearMap.comp_apply,
    torusPathSpeed_comp_eq_mfderiv f hf γ t
      (Jacobians.Bridge.bridgePath_continuous (X := X) x₀ p).continuousAt
      (Jacobians.Bridge.bridgePath_chart_differentiable (X := X) x₀ p t)]

/-- F1/F2 linear-algebra bridge: applying the dualized torus pullback to the
source Abel-Jacobi coordinate is the torus Albanese coordinate of the pulled
back integration functional. -/
theorem torusAmbientLinear_ofCurveAmbient_sub {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f)
    (x₀ x : X) :
    torusAmbientLinear f hf (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀) =
      torusAlbaneseCoordinateOfFunctional (A := A)
        ((torusPullbackOneForm f hf).dualMap (Axioms.pathIntegralBasepointFunctional X x₀ x)) -
      torusAlbaneseCoordinateOfFunctional (A := A)
        ((torusPullbackOneForm f hf).dualMap
          (Axioms.pathIntegralBasepointFunctional X x₀ x₀)) := by
  classical
  unfold torusAmbientLinear torusAlbaneseCoordinateOfFunctional ofCurveAmbient
  simp [LinearMap.comp_apply, map_sub]

/-! ## Albanese interface discharge (G2/G3/G4 as theorems from A1+AK) -/

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
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < RiemannSurface.genus X) :
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤ := by
  haveI : IsTopologicalAddGroup (_root_.Jacobian X) := by
    change IsTopologicalAddGroup (Jacobians.Jacobian X)
    exact topologicalAddGroup_of_lieAddGroup
      (modelWithCornersSelf ℂ (Fin (RiemannSurface.genus X) → ℂ)) ω
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


/-! ## UP-1: existence of the descended homomorphism -/

/-- The additive homomorphism produced by the E-row of the universal-property
plan: dualize pullback of target torus one-forms, use period functoriality to
descend to the Jacobian quotient, then map from the target torus presentation
back to the abstract target `A`. -/
noncomputable def jacobianUniversalPhi {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    Jacobian X →+ A :=
  let P : TorusPresentation m A := (torus_self_albanese (A := A)).toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using period_functoriality f hf
  let qφ :
      ((Fin (RiemannSurface.genus X) → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+
        ((Fin m → ℂ) ⧸ P.lattice.toAddSubgroup) :=
    Vendor.Kirov.ZLatticeQuotient.pushforward ΛX P.lattice Lc hL
  { toFun := fun z => P.fromQuot (qφ z.down)
    map_zero' := by
      change P.fromQuot (qφ 0) = 0
      exact (congrArg P.fromQuot (map_zero qφ)).trans (map_zero P.fromQuot)
    map_add' := by
      intro z w
      change P.fromQuot (qφ (z.down + w.down)) =
        P.fromQuot (qφ z.down) + P.fromQuot (qφ w.down)
      exact (congrArg P.fromQuot (map_add qφ z.down w.down)).trans
        (map_add P.fromQuot (qφ z.down) (qφ w.down)) }

/-- The descended homomorphism in `jacobianUniversalPhi` is holomorphic. -/
theorem jacobianUniversalPhi_holo {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (jacobianUniversalPhi f hf : Jacobian X → A) := by
  classical
  unfold jacobianUniversalPhi
  dsimp only
  let P : TorusPresentation m A := (torus_self_albanese (A := A)).toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using period_functoriality f hf
  let qφ :
      ((Fin (RiemannSurface.genus X) → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+
        ((Fin m → ℂ) ⧸ P.lattice.toAddSubgroup) :=
    Vendor.Kirov.ZLatticeQuotient.pushforward ΛX P.lattice Lc hL
  change ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
    (fun z : Jacobian X => P.fromQuot (qφ z.down))
  simpa [qφ, ΛX] using AX_torus_descent_holo P Lc hL

/-- UP-1, E1-E6: existence of a holomorphic group homomorphism
`Jacobian X →+ A` attached to a pointed holomorphic map `f : X → A`.

This is only the homomorphism-existence part of the universal-property DAG.
The factorization identity `f = φ ∘ ofCurve x₀` and uniqueness are the later
F- and U-rows. -/
theorem jacobianUniversal_phi_exists {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∀ {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A] [CompactSpace A]
      [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A), ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f → f x₀ = 0 →
      ∃ φ : Jacobian X →+ A,
        ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
          (φ : Jacobian X → A) := by
  intro m A _ _ _ _ _ _ _ _ f hf _hbase
  exact ⟨jacobianUniversalPhi f hf, jacobianUniversalPhi_holo f hf⟩

/-! ## UP-2: factorization through the Abel-Jacobi map -/

/-- The quotient-level factorization step, reduced to the coordinate identity
that the dualized pullback map sends the Abel-Jacobi coordinate of `x` to the
target-torus Albanese coordinate of `f x`.

This lemma is intentionally conditional: the remaining analytic input is the
coordinate equality in the hypothesis. Once that identity is available from
pullback naturality for invariant torus forms, the A1 self-Albanese presentation closes
the target quotient rewrite through `TorusPresentation.fromQuot_liftCoord`. -/
theorem jacobianUniversal_phi_factorizes_of_coordinate_eq {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∀ {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A] [CompactSpace A]
      [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f),
      (∀ x,
        (torus_self_albanese (m := m) (A := A)).liftCoord (f x) -
            torusAmbientLinear f hf (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀) ∈
          (torus_self_albanese (m := m) (A := A)).toTorusPresentation.lattice) →
      ∀ x, f x = jacobianUniversalPhi f hf (Jacobian.ofCurve x₀ x) := by
  intro m A _ _ _ _ _ _ _ _ f hf hcoord x
  classical
  unfold jacobianUniversalPhi Jacobian.ofCurve Axioms.ofCurveImpl
  dsimp only
  let S : TorusSelfAlbanesePresentation m A := torus_self_albanese (A := A)
  let P : TorusPresentation m A := S.toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using period_functoriality f hf
  let qφ :
      ((Fin (RiemannSurface.genus X) → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+
        ((Fin m → ℂ) ⧸ P.lattice.toAddSubgroup) :=
    Vendor.Kirov.ZLatticeQuotient.pushforward ΛX P.lattice Lc hL
  change f x = P.fromQuot (qφ (QuotientAddGroup.mk' ΛX.toAddSubgroup
    (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀)))
  rw [← P.fromQuot_liftCoord (f x)]
  congr 1
  change QuotientAddGroup.mk' P.lattice.toAddSubgroup (P.liftCoord (f x)) =
    qφ (QuotientAddGroup.mk' ΛX.toAddSubgroup
      (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀))
  have hq : qφ (QuotientAddGroup.mk' ΛX.toAddSubgroup
        (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀)) =
      QuotientAddGroup.mk' P.lattice.toAddSubgroup
        (L (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀)) := rfl
  rw [hq, ← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  simpa [S, P, L] using (hcoord x)

/-- F1-F3: the homomorphism produced by UP-1 factors the pointed holomorphic
map `f` through the Abel-Jacobi map. -/
theorem jacobianUniversal_phi_factorizes {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∀ {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A] [CompactSpace A]
      [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f), f x₀ = 0 →
      ∀ x, f x = jacobianUniversalPhi f hf (Jacobian.ofCurve x₀ x) := by
  intro m A _ _ _ _ _ _ _ _ f hf hbase
  refine jacobianUniversal_phi_factorizes_of_coordinate_eq x₀ f hf ?_
  intro x
  let S : TorusSelfAlbanesePresentation m A := torus_self_albanese (A := A)
  let γ : ℝ → A := f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ x
  let γ₀ : ℝ → A := f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ x₀
  -- goal: `S.liftCoord (f x) − torusAmbientLinear f hf (diff) ∈ lattice`.
  -- Rewrite the dual pullback as a difference of path-integral coordinates, then
  -- the (mod-Λ) self-Albanese identity of `S` gives the membership directly.
  rw [torusAmbientLinear_ofCurveAmbient_sub f hf x₀ x]
  exact S.liftCoord_eq_albanese γ γ₀ (f x)
    (by simp [γ, Jacobians.Bridge.bridgePath_at_zero, hbase])
    (by simp [γ, Jacobians.Bridge.bridgePath_at_one])
    (by simp [γ₀, Jacobians.Bridge.bridgePath_at_zero, hbase])
    (by simp [γ₀, Jacobians.Bridge.bridgePath_at_one, hbase])
    (by
      intro ell
      simpa [γ] using torusPullback_pathIntegral_naturality f hf x₀ x ell)
    (by
      intro ell
      simpa [γ₀] using torusPullback_pathIntegral_naturality f hf x₀ x₀ ell)


/-! ## UP-3: uniqueness of the descended homomorphism -/

/-- UP-3, U1-U2: any two additive homomorphisms out of the Jacobian that agree
on the Abel-Jacobi image of a positive-genus curve are equal. -/
theorem jacobianUniversal_phi_unique {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (hg : 0 < RiemannSurface.genus X) :
    ∀ {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A] [CompactSpace A]
      [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A) (φ₁ φ₂ : Jacobian X →+ A),
      (ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
          (φ₁ : Jacobian X → A) ∧
        ∀ x, f x = φ₁ (Jacobian.ofCurve x₀ x)) →
      (ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
          (φ₂ : Jacobian X → A) ∧
        ∀ x, f x = φ₂ (Jacobian.ofCurve x₀ x)) →
      φ₁ = φ₂ := by
  intro m A _ _ _ _ _ _ _ _ f φ₁ φ₂ hφ₁ hφ₂
  refine AddMonoidHom.eq_of_eqOn_dense (curve_generates_jacobian x₀ hg) ?_
  rintro _ ⟨x, rfl⟩
  exact (hφ₁.2 x).symm.trans (hφ₂.2 x)

/-- Buzzard's concrete Abel-Jacobi map satisfies the positive-genus
Jacobian/Albanese universal property. -/
theorem ofCurve_isJacobian {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (hg : 0 < RiemannSurface.genus X) :
    IsJacobian (g := RiemannSurface.genus X) x₀ (Jacobian X) (Jacobian.ofCurve x₀) := by
  refine
    { aj_holo := Jacobian.ofCurve_contMDiff x₀
      aj_base := Jacobian.ofCurve_self x₀
      universal := ?_ }
  intro m A _ _ _ _ _ _ _ _ f hf hbase
  let φ : Jacobian X →+ A := jacobianUniversalPhi f hf
  have hφ_holo :
      ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
        (φ : Jacobian X → A) :=
    jacobianUniversalPhi_holo f hf
  have hφ_fac : ∀ x, f x = φ (Jacobian.ofCurve x₀ x) :=
    jacobianUniversal_phi_factorizes x₀ f hf hbase
  refine ⟨φ, ⟨hφ_holo, hφ_fac⟩, ?_⟩
  intro ψ hψ
  exact (jacobianUniversal_phi_unique x₀ hg f φ ψ ⟨hφ_holo, hφ_fac⟩ hψ).symm

/-! ## Categoricity: the universal property determines the Jacobian

The universal property is not merely *satisfied* by the Jacobian; it
*characterizes* it. The next theorem is the categoricity certificate: any two
objects satisfying `IsJacobian` are biholomorphically, group-isomorphically the
same, via a unique pair of mutually inverse holomorphic homomorphisms
intertwining their Abel–Jacobi maps. This is the initial-object uniqueness
(Yoneda) for the pointed category of holomorphic maps to complex tori.

It uses **none of Buzzard's 24 challenge requirements** — only the three fields
of `IsJacobian` (`aj_holo`, `aj_base`, `universal`) — and is **axiom-free**
(`#print axioms isJacobian_unique` depends only on `propext`, `Classical.choice`,
`Quot.sound`). The challenge requirements re-enter only in the corollary
`isJacobian_iso_jacobian`, which names Buzzard's concrete `Jacobian X` as one of
the two objects via `ofCurve_isJacobian` (and so inherits its torus axioms). -/

universe u

/-- **Categoricity of the Albanese / Jacobian universal property.**

If `(J₁, aj₁)` and `(J₂, aj₂)` both satisfy `IsJacobian x₀`, there is a pair of
mutually inverse holomorphic group homomorphisms `φ : J₁ →+ J₂`, `ψ : J₂ →+ J₁`
— a biholomorphic group isomorphism `J₁ ≅ J₂` — intertwining the Abel–Jacobi
maps (`aj₂ = φ ∘ aj₁` and `aj₁ = ψ ∘ aj₂`). The factorizing `φ` is moreover the
unique holomorphic group hom with `φ ∘ aj₁ = aj₂` (the `∃!` in `universal`).

The proof is pure initial-object algebra over the universal property and uses
none of the challenge's 24 requirements; it is axiom-free. -/
theorem isJacobian_unique
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X) {g₁ g₂ : ℕ}
    {J₁ : Type u} [TopologicalSpace J₁] [T2Space J₁] [CompactSpace J₁] [ConnectedSpace J₁]
    [ChartedSpace (Fin g₁ → ℂ) J₁] [AddGroup J₁] [IsManifold 𝓘(ℂ, Fin g₁ → ℂ) ω J₁]
    [LieAddGroup 𝓘(ℂ, Fin g₁ → ℂ) ω J₁]
    {J₂ : Type u} [TopologicalSpace J₂] [T2Space J₂] [CompactSpace J₂] [ConnectedSpace J₂]
    [ChartedSpace (Fin g₂ → ℂ) J₂] [AddGroup J₂] [IsManifold 𝓘(ℂ, Fin g₂ → ℂ) ω J₂]
    [LieAddGroup 𝓘(ℂ, Fin g₂ → ℂ) ω J₂]
    {aj₁ : X → J₁} {aj₂ : X → J₂}
    (hJ₁ : IsJacobian.{u, u, u} (g := g₁) x₀ J₁ aj₁)
    (hJ₂ : IsJacobian.{u, u, u} (g := g₂) x₀ J₂ aj₂) :
    ∃ φ : J₁ →+ J₂, ∃ ψ : J₂ →+ J₁,
      ContMDiff 𝓘(ℂ, Fin g₁ → ℂ) 𝓘(ℂ, Fin g₂ → ℂ) ω (φ : J₁ → J₂) ∧
      ContMDiff 𝓘(ℂ, Fin g₂ → ℂ) 𝓘(ℂ, Fin g₁ → ℂ) ω (ψ : J₂ → J₁) ∧
      ψ.comp φ = AddMonoidHom.id J₁ ∧ φ.comp ψ = AddMonoidHom.id J₂ ∧
      (∀ x, aj₂ x = φ (aj₁ x)) ∧ (∀ x, aj₁ x = ψ (aj₂ x)) := by
  obtain ⟨φ, ⟨hφ_holo, hφ_fac⟩, _⟩ := hJ₁.universal (A := J₂) (m := g₂) aj₂ hJ₂.aj_holo hJ₂.aj_base
  obtain ⟨ψ, ⟨hψ_holo, hψ_fac⟩, _⟩ := hJ₂.universal (A := J₁) (m := g₁) aj₁ hJ₁.aj_holo hJ₁.aj_base
  refine ⟨φ, ψ, hφ_holo, hψ_holo, ?_, ?_, hφ_fac, hψ_fac⟩
  · obtain ⟨χ, _, huniq⟩ := hJ₁.universal (A := J₁) (m := g₁) aj₁ hJ₁.aj_holo hJ₁.aj_base
    have e1 : ψ.comp φ = χ :=
      huniq _ ⟨by rw [AddMonoidHom.coe_comp]; exact hψ_holo.comp hφ_holo,
        fun x => by rw [AddMonoidHom.comp_apply, ← hφ_fac x]; exact hψ_fac x⟩
    have e2 : AddMonoidHom.id J₁ = χ :=
      huniq _ ⟨by rw [AddMonoidHom.coe_id]; exact contMDiff_id,
        fun x => by rw [AddMonoidHom.id_apply]⟩
    exact e1.trans e2.symm
  · obtain ⟨χ, _, huniq⟩ := hJ₂.universal (A := J₂) (m := g₂) aj₂ hJ₂.aj_holo hJ₂.aj_base
    have e1 : φ.comp ψ = χ :=
      huniq _ ⟨by rw [AddMonoidHom.coe_comp]; exact hφ_holo.comp hψ_holo,
        fun x => by rw [AddMonoidHom.comp_apply, ← hψ_fac x]; exact hφ_fac x⟩
    have e2 : AddMonoidHom.id J₂ = χ :=
      huniq _ ⟨by rw [AddMonoidHom.coe_id]; exact contMDiff_id,
        fun x => by rw [AddMonoidHom.id_apply]⟩
    exact e1.trans e2.symm

/-- **The universal property determines Buzzard's concrete Jacobian.** For
positive genus, every object satisfying `IsJacobian` is biholomorphically,
group-isomorphically the same as `Jacobian X`, with the isomorphism intertwining
the Abel–Jacobi maps. (This specializes `isJacobian_unique` to
`ofCurve_isJacobian`, and so rests on the same torus axioms as the latter.) -/
theorem isJacobian_iso_jacobian
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X] (x₀ : X) {g₁ : ℕ}
    {J₁ : Type u} [TopologicalSpace J₁] [T2Space J₁] [CompactSpace J₁] [ConnectedSpace J₁]
    [ChartedSpace (Fin g₁ → ℂ) J₁] [AddGroup J₁] [IsManifold 𝓘(ℂ, Fin g₁ → ℂ) ω J₁]
    [LieAddGroup 𝓘(ℂ, Fin g₁ → ℂ) ω J₁] {aj₁ : X → J₁}
    (hg : 0 < RiemannSurface.genus X)
    (hJ : IsJacobian.{u, u, u} (g := g₁) x₀ J₁ aj₁) :
    ∃ φ : J₁ →+ Jacobian X, ∃ ψ : Jacobian X →+ J₁,
      ContMDiff 𝓘(ℂ, Fin g₁ → ℂ) 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) ω
        (φ : J₁ → Jacobian X) ∧
      ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin g₁ → ℂ) ω
        (ψ : Jacobian X → J₁) ∧
      ψ.comp φ = AddMonoidHom.id J₁ ∧ φ.comp ψ = AddMonoidHom.id (Jacobian X) ∧
      (∀ x, Jacobian.ofCurve x₀ x = φ (aj₁ x)) ∧
      (∀ x, aj₁ x = ψ (Jacobian.ofCurve x₀ x)) :=
  isJacobian_unique x₀ hJ (ofCurve_isJacobian.{u, u} x₀ hg)

end Jacobians
