/-
`ofCurveImpl`: axiom-stub for the Abel-Jacobi map.

**Classical content.** For a compact Riemann surface `X` of genus `g`,
fix a basepoint `P₀ : X`. The **Abel-Jacobi map** is
    `ofCurve P₀ : X → Jacobian X`
    `P ↦ [∫_{P₀}^P ω_1, …, ∫_{P₀}^P ω_g]`
in terms of a basis `ω_1, …, ω_g` of `HolomorphicOneForm X`, with
integration along any smooth path from `P₀` to `P` (well-defined modulo
the period lattice).

This is a **classical, canonical definition** — the Abel-Jacobi map is
the central object connecting the complex-analytic and algebraic-
geometric views of a curve.

**Why axiomatized.** The definition requires:
  - A chosen basis of `HolomorphicOneForm X` — we have one via
    `Jacobians.Jacobian.jacobianBasis` (from `Module.finBasis`).
  - Path integrals of holomorphic 1-forms — requires the
    `PathIntegral.lean` subproject (multi-week) or the
    `AX_AnalyticCycleBasis`-based approach.

Following the `periodMap` / `intersectionForm` pattern, we axiomatize
the typed value and let downstream code reference it. The axiom is
retired to a `def` when path integration lands.

## Properties (separate axioms, TODO)

Abel's theorem and related: `ofCurve_contMDiff` (smooth), `ofCurve_self`
(sends basepoint to 0), `ofCurve_inj` (injective for positive genus,
= Abel's theorem). These are separate axioms to be declared when
needed.

See `docs/formalization-plan.md` §7; discharge priority #10
(`AX_AbelTheorem`).
Reference: Mumford Vol I §II.3; Griffiths-Harris Ch. 2.3; Forster Ch. III.
-/
import Jacobians.Jacobian.Construction

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- **Axiom-stub.** The Abel-Jacobi map lifted to the ambient `Fin g → ℂ`
(pre-quotient by the period lattice).

Classical content: `(P₀, P) ↦ [∫_{P₀}^P ω_i]_i` computing the integral
from `P₀` to `P` against a chosen basis of `HolomorphicOneForm X`.
Well-defined only modulo the period lattice — reducing to
`Jacobian X = (Fin g → ℂ) ⧸ Λ` recovers the real Abel-Jacobi map.

Retired to a `def` when path integrals + basepoint choice are
concrete. -/
axiom ofCurveAmbient (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : X → X → (Fin (genus X) → ℂ)

/-- The Abel-Jacobi map `ofCurveImpl P₀ : X → Jacobian X`, defined as the
quotient of the ambient lift `ofCurveAmbient`, normalized so that
`ofCurveImpl P₀ P₀ = 0`.

Setting the formula to `ofCurveAmbient X P₀ P - ofCurveAmbient X P₀ P₀`
before the quotient guarantees the basepoint-sent-to-zero property by
construction, rather than needing it as a separate axiom. -/
noncomputable def ofCurveImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ : X) : X → Jacobian X :=
  fun P => ULift.up <|
    QuotientAddGroup.mk' _ (ofCurveAmbient X P₀ P - ofCurveAmbient X P₀ P₀)

/-- **Axiom-stub.** The pushforward map
`pushforward f hf : Jacobian X →ₜ+ Jacobian Y` associated to a
holomorphic map `f : X → Y` between compact Riemann surfaces.

Classical definition: `f_*[γ] := [f ∘ γ]` on the level of loops, extended
linearly to `H_1` and then to the period-lattice quotient. Well-defined
because `f` sends loops to loops (continuity) and the period map is
natural. -/
axiom pushforwardImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y

/-- **Axiom-stub.** The pullback map
`pullback f hf : Jacobian Y →ₜ+ Jacobian X` associated to a holomorphic
map `f : X → Y`.

Classical definition: `f^*ω := ω ∘ df` on the level of 1-forms, then
dualised to the Jacobian via `periodMap`. Equal to zero if `f` is
constant (no 1-forms to pull back). -/
axiom pullbackImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X

/-- **Axiom-stub.** The degree of a holomorphic map between compact
Riemann surfaces. Zero if `f` is constant; otherwise the common
fiber-count `|f⁻¹(q)|` weighted by local multiplicities (well-defined
by `AX_BranchLocus`). -/
axiom degreeImpl {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ

/-! ## Properties of `ofCurveImpl`, pushforward, pullback, degree

The following axiom-stubs encode the classical theorems. Each retires
to a derived theorem once the corresponding `def` replaces its
axiom-stub counterpart and the underlying path-integral / branch-locus
machinery lands. -/

/-- **Axiom.** The Abel-Jacobi map is smooth/holomorphic. -/
axiom AX_ofCurve_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ContMDiff 𝓘(ℂ, ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ofCurveImpl X P)

/-- **Theorem (retired 2026-04-23).** The Abel-Jacobi map sends the
basepoint to zero. Used to be an axiom; now derivable because the
`ofCurveImpl` definition subtracts `ofCurveAmbient X P₀ P₀` from the
numerator, making the identity definitional. -/
theorem AX_ofCurve_self {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ofCurveImpl X P P = 0 := by
  unfold ofCurveImpl
  ext : 1
  simp
  rfl

/-- **Axiom (= Abel's theorem, on the curve side).** The Abel-Jacobi
map is injective when the genus is positive. -/
axiom AX_ofCurve_inj {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) (_h : 0 < genus X) :
    Function.Injective (ofCurveImpl X P)

/-- **Axiom.** Pushforward on Jacobians is smooth. -/
axiom AX_pushforward_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforwardImpl X Y f hf)

/-- **Axiom.** Pushforward is the identity on identity. (Functoriality, part 1.) -/
axiom AX_pushforward_id_apply {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : Jacobian X) :
    pushforwardImpl X X id contMDiff_id P = P

/-- **Axiom.** Pushforward respects composition. (Functoriality, part 2.) -/
axiom AX_pushforward_comp_apply
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : Jacobian X) :
    pushforwardImpl X Z (g ∘ f) (hg.comp hf) P =
      pushforwardImpl Y Z g hg (pushforwardImpl X Y f hf P)

/-- **Axiom.** Pullback on Jacobians is smooth. -/
axiom AX_pullback_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullbackImpl X Y f hf)

/-- **Axiom.** Pullback is the identity on identity. (Functoriality, part 1.) -/
axiom AX_pullback_id_apply {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : Jacobian X) :
    pullbackImpl X X id contMDiff_id P = P

/-- **Axiom.** Pullback respects composition (contravariantly). (Functoriality, part 2.) -/
axiom AX_pullback_comp_apply
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : Jacobian Z) :
    pullbackImpl X Z (g.comp f) (hg.comp hf) P =
      pullbackImpl X Y f hf (pullbackImpl Y Z g hg P)

/-- **Axiom.** The composition "pullback then pushforward" multiplies by degree. -/
axiom AX_pushforward_pullback {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (P : Jacobian Y) :
    pushforwardImpl X Y f hf (pullbackImpl X Y f hf P) = (degreeImpl f hf) • P

/-- **Axiom (LieAddGroup).** Placeholder for the Lie group structure on
the universe-lifted Jacobian. In `Jacobians/Jacobian/Construction.lean`
we derived ChartedSpace, IsManifold, and six more instances via ULift
transfer, but LieAddGroup through ULift hits a Mathlib-level chart
target universe mismatch (`Set.{max u 0}` vs `Set.{0}`). Axiomatize
until that infrastructure lands. -/
axiom AX_jacobian_lieAddGroup {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X)

end Jacobians.Axioms
