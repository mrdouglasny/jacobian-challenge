import Jacobians.Axioms.TorusAlbanese

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
torus axioms (`AX_torus_oneforms_dualCover` discharged #232) / `AX_torus_self_albanese` /
`AX_period_functoriality` + `AX_curve_generates_jacobian` (the descent
smoothness `AX_torus_descent_holo` was itself discharged to a theorem
2026-06-06), and is `#print axioms`-clean (no `sorryAx`). The original proof
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
  let P : TorusPresentation m A := (AX_torus_self_albanese (A := A)).toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using AX_period_functoriality P f hf
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
  let P : TorusPresentation m A := (AX_torus_self_albanese (A := A)).toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using AX_period_functoriality P f hf
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

/-- The quotient-level factorization step, reduced to the coordinate identity
that the dualized pullback map sends the Abel-Jacobi coordinate of `x` to the
target-torus Albanese coordinate of `f x`.

This lemma is intentionally conditional: the remaining analytic input is the
coordinate equality in the hypothesis. Once that identity is available from
pullback naturality for invariant torus forms, `AX_torus_self_albanese` closes
the target quotient rewrite through `TorusPresentation.fromQuot_liftCoord`. -/
theorem jacobianUniversal_phi_factorizes_of_coordinate_eq {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∀ {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A] [CompactSpace A]
      [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f),
      (∀ x,
        torusAmbientLinear f hf (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀) =
          (AX_torus_self_albanese (m := m) (A := A)).liftCoord (f x)) →
      ∀ x, f x = jacobianUniversalPhi f hf (Jacobian.ofCurve x₀ x) := by
  intro m A _ _ _ _ _ _ _ _ f hf hcoord x
  classical
  unfold jacobianUniversalPhi Jacobian.ofCurve Axioms.ofCurveImpl
  dsimp only
  let S : TorusSelfAlbanesePresentation m A := AX_torus_self_albanese (A := A)
  let P : TorusPresentation m A := S.toTorusPresentation
  letI : DiscreteTopology P.lattice := P.lattice_discrete
  letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
  let ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  let L : (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    torusAmbientLinear f hf
  let Lc : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap L
  let hL : ΛX.toAddSubgroup ≤ P.lattice.toAddSubgroup.comap Lc.toAddMonoidHom := by
    simpa [ΛX, L, Lc] using AX_period_functoriality P f hf
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
  have hLift :
      P.liftCoord (f x) = L (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀) := by
    simpa [S, P, L] using (hcoord x).symm
  rw [hLift]
  rfl

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
  let S : TorusSelfAlbanesePresentation m A := AX_torus_self_albanese (A := A)
  let γ : ℝ → A := f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ x
  let γ₀ : ℝ → A := f ∘ Jacobians.Bridge.bridgePath (X := X) x₀ x₀
  calc
    torusAmbientLinear f hf (ofCurveAmbient X x₀ x - ofCurveAmbient X x₀ x₀)
        =
          torusAlbaneseCoordinateOfFunctional (A := A)
            ((torusPullbackOneForm f hf).dualMap
              (Axioms.pathIntegralBasepointFunctional X x₀ x)) -
          torusAlbaneseCoordinateOfFunctional (A := A)
            ((torusPullbackOneForm f hf).dualMap
              (Axioms.pathIntegralBasepointFunctional X x₀ x₀)) :=
      torusAmbientLinear_ofCurveAmbient_sub f hf x₀ x
    _ = S.liftCoord (f x) := by
      symm
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
  refine AddMonoidHom.eq_of_eqOn_dense (AX_curve_generates_jacobian x₀ hg) ?_
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

end Jacobians
