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

The open goal `IsJacobian x₀ (Jacobian X) (ofCurve x₀)` — that Buzzard's concrete
`Jacobian`/`ofCurve` satisfy this property — is the categoricity theorem that
would close the def-degeneracy gap categorically; it is not proved here. The proof
plan (lemma DAG, vetted-axiom leaves, effort) is in
`docs/universal-property-proof-plan.md`. One prerequisite instance is still missing
for the goal to typecheck: `ConnectedSpace (Jacobian X)` (true — a torus is
connected — but not provided by Buzzard's API).

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
  let P : TorusPresentation m A := AX_torus_self_albanese (A := A)
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
  let P : TorusPresentation m A := AX_torus_self_albanese (A := A)
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

end Jacobians
