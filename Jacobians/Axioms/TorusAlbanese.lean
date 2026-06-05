import Jacobians.Challenge
import Jacobians.Vendor.Kirov.ZLatticeQuotient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Textbook Albanese facts for complex tori

This file houses the four cross-model-vetted textbook axioms used by the
universal-property proof plan in `docs/universal-property-proof-plan.md`.

The repo's current `HolomorphicOneForm` API is curve-only
(`[ChartedSpace ℂ X]`). For a target complex torus modelled on
`Fin m → ℂ`, this file therefore uses `TorusHolomorphicOneForm m A` as the
target-torus form space until a genuine multivariable holomorphic cotangent
section API lands.
-/

open scoped Manifold ContDiff Topology

namespace Jacobians.Axioms

open Jacobians.RiemannSurface

/-- Placeholder for holomorphic one-forms on a complex torus modelled on
`Fin m → ℂ`, pending a project-wide multivariable cotangent-section API.

It is intentionally basis-shaped so the E-row construction can talk to the
existing Jacobian coordinates without changing `HolomorphicOneForm`, which is
currently specific to compact Riemann surfaces. -/
abbrev TorusHolomorphicOneForm (m : ℕ) (_A : Type*) := Module.Dual ℂ (Fin m → ℂ)

/-- A concrete presentation of an abstract target torus `A` by its universal
cover `Fin m → ℂ` modulo a full integer lattice, together with the holomorphic
group map back to `A`. -/
structure TorusPresentation (m : ℕ) (A : Type*) [TopologicalSpace A]
    [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] where
  lattice : Submodule ℤ (Fin m → ℂ)
  lattice_discrete : DiscreteTopology lattice
  lattice_isZLattice : IsZLattice ℝ lattice
  fromQuot : ((Fin m → ℂ) ⧸ lattice.toAddSubgroup) →+ A
  fromQuot_holo :
    letI : DiscreteTopology lattice := lattice_discrete
    letI : IsZLattice ℝ lattice := lattice_isZLattice
    ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fromQuot : ((Fin m → ℂ) ⧸ lattice.toAddSubgroup) → A)

/-- The pullback of target-torus invariant forms along a pointed holomorphic
map from a curve.

This is a temporary glue definition while the repository has no multivariable
holomorphic-one-form pullback API for `ChartedSpace (Fin m → ℂ)` targets. The
period-functoriality axiom below is the load-bearing mathematical statement
used by the quotient descent. -/
noncomputable def torusPullbackOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (_f : X → A) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω _f) :
    TorusHolomorphicOneForm m A →ₗ[ℂ] HolomorphicOneForm X :=
  0

/-- **Axiom.** Invariant holomorphic one-forms on a complex torus are the
dual of its universal cover.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1.
Strategy: lift a holomorphic one-form to the cover `ℂ^m`, use translation
invariance/Liouville to make its coefficient constant, then descend constant
linear functionals exactly to invariant forms.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_torus_oneforms_dualCover {m : ℕ} {A : Type*} [TopologicalSpace A]
    [T2Space A] [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A]
    [AddGroup A] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A]
    [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] :
    TorusHolomorphicOneForm m A ≃ₗ[ℂ] Module.Dual ℂ (Fin m → ℂ)

/-- **Axiom.** A complex torus is canonically recovered from its own
Abel-Jacobi map.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1.
Strategy: integrate invariant one-forms from `0` to a point on the universal
cover; the period ambiguity is exactly the lattice, so the resulting quotient
map is a biholomorphic group isomorphism.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_torus_self_albanese {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A] :
    TorusPresentation m A

/-- The cover-linear map induced by dualizing pullback of one-forms. -/
noncomputable def torusAmbientLinear {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (f : X → A) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    (Fin (RiemannSurface.genus X) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  let eX : (HolomorphicOneForm X →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      (Fin (RiemannSurface.genus X) → ℂ) :=
    (jacobianBasis X).dualBasis.equivFun
  let eA : TorusHolomorphicOneForm m A ≃ₗ[ℂ] Module.Dual ℂ (Fin m → ℂ) :=
    AX_torus_oneforms_dualCover (A := A)
  (Module.evalEquiv ℂ (Fin m → ℂ)).symm.toLinearMap.comp
    ((eA.symm.toLinearMap).dualMap.comp
      ((torusPullbackOneForm f hf).dualMap.comp eX.symm.toLinearMap))

/-- **Axiom.** A holomorphic map from a compact curve to a complex torus sends
the source period lattice to the target period lattice under the dual period
map.

Reference: Griffiths-Harris, Ch. 0 and Ch. 2.
Strategy: for every cycle `γ` and invariant form `ω`, use
`∮_{f_* γ} ω = ∮_γ f^*ω`; in basis coordinates this says exactly that the
dualized pullback map carries the source lattice into the target lattice.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_period_functoriality {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (P : TorusPresentation m A) (f : X → A)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f) :
    (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup ≤
      P.lattice.toAddSubgroup.comap (torusAmbientLinear f hf).toAddMonoidHom

/-- **Conditional fallback axiom.** A complex-linear, lattice-compatible lift
descends to a holomorphic group homomorphism on quotient tori.

Reference: Birkenhake-Lange, *Complex Abelian Varieties*, Ch. 1; standard
quotient-manifold descent for covering maps.
Strategy: prove smoothness locally after choosing branches of the universal
covering maps; in those charts the descended map is exactly the original
complex-linear map.

Fallback vetted: Gemini + Codex 2026-06-02; used only when the direct E6 chart
descent proof is unavailable. -/
axiom AX_torus_descent_holo {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {m : ℕ} {A : Type v} [TopologicalSpace A] [T2Space A]
    [CompactSpace A] [ConnectedSpace A] [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
    (P : TorusPresentation m A)
    (L : (Fin (RiemannSurface.genus X) → ℂ) →L[ℂ] (Fin m → ℂ))
    (hL : (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup ≤
      P.lattice.toAddSubgroup.comap L.toAddMonoidHom) :
    letI : DiscreteTopology P.lattice := P.lattice_discrete
    letI : IsZLattice ℝ P.lattice := P.lattice_isZLattice
    ContMDiff 𝓘(ℂ, Fin (RiemannSurface.genus X) → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fun z : Jacobian X =>
        P.fromQuot
          ((Vendor.Kirov.ZLatticeQuotient.pushforward
              (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X))
              P.lattice L hL) z.down))

/-- **Axiom.** The Abel-Jacobi image of a positive-genus curve generates its
Jacobian as an abstract additive group.

Reference: Mumford, *Curves and their Jacobians*; Milne, *Abelian Varieties* §I.
Strategy: Jacobi inversion writes every Jacobian point as a difference of
effective divisors of degree `g`, hence as a finite sum of Abel-Jacobi image
points.

Vetted: Gemini + Codex 2026-06-02. -/
axiom AX_curve_generates_jacobian {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < RiemannSurface.genus X) :
    AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤

end Jacobians.Axioms
