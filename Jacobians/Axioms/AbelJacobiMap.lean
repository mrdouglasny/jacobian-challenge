/-
# Abel-Jacobi map, pushforward, pullback, degree — as real definitions

The four Buzzard-challenge data maps are here defined as real Lean
`noncomputable def`s, factored through smaller functional axioms rather
than axiomatized wholesale. The refactor (2026-04-23) responds to
external review (Codex, session 2026-04-23) flagging that
`ofCurveAmbient`, `pushforwardImpl`, `pullbackImpl`, `degreeImpl` were
previously top-level axioms.

## What is now a real def vs what is still axiomatic

- `ofCurveAmbient X P₀ P : Fin (genus X) → ℂ` — **def** via
  `pathIntegralBasepointFunctional` applied to `jacobianBasis X`.
- `ofCurveImpl X P₀ : X → Jacobian X` — **def** (as before) via the
  quotient with basepoint-normalization.
- `pushforwardImpl X Y f hf : Jacobian X →ₜ+ Jacobian Y` — **def** via
  `QuotientAddGroup.map` of the ambient linear axiom
  `pushforwardAmbientLinear`, ULift-wrapped and made continuous through
  finite-dim automatic continuity.
- `pullbackImpl X Y f hf : Jacobian Y →ₜ+ Jacobian X` — **def**,
  symmetric to `pushforwardImpl` via `pullbackAmbientLinear`.
- `degreeImpl f hf : ℕ` — **def** via `AX_BranchLocus`
  (`Classical.choose` of the common fiber degree); 0 for constants.

Still axiomatic (smaller-grained than before; 2026-04-23 round-2
refactor responded to Gemini review by adding the local-antiderivative
axiom and structured form primitives):
- `pathIntegralBasepointFunctional` — the functional
  `X → X → (HolomorphicOneForm X →ₗ[ℂ] ℂ)`, "integrate from `P₀` to
  `P`". Now paired with:
- `AX_pathIntegral_local_antiderivative` — Fundamental Theorem of
  Calculus: the derivative of the functional w.r.t. upper endpoint
  (in the chart at `P`) equals `form.coeff P (chart P)`. This binds
  `pathIntegralBasepointFunctional` to the 1-form cocycle data and
  prevents trivial-zero satisfaction of downstream smoothness claims.
- `pullbackOneForm (f : X → Y) : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X`
  — structured primitive replacing the former
  `pushforwardAmbientLinear` axiom. `pushforwardAmbientLinear` is now
  a real `def` derived by transporting `(pullbackOneForm f).dualMap`
  through the basis `jacobianBasis`.
- `pushforwardOneForm (f : X → Y) : HolomorphicOneForm X →ₗ[ℂ]
  HolomorphicOneForm Y` — the trace / pushforward of 1-forms along a
  finite cover. Analogously feeds `pullbackAmbientLinear` as a `def`.
- `AX_pushforwardAmbient_preserves_lattice`,
  `AX_pullbackAmbient_preserves_lattice` — still axioms; retire to
  theorems once period-map naturality is derived.
- Property axioms (`AX_ofCurve_contMDiff`, `AX_ofCurve_inj`,
  `AX_pushforward_contMDiff`, functoriality, `AX_pushforward_pullback`)
  — properties of the defs, retire with the usual textbook proofs.
- **`AX_jacobian_lieAddGroup`** is no longer an axiom (2026-04-23
  round-3): converted to a theorem via the ULift-smoothness lemmas
  `contMDiff_ulift_up` / `contMDiff_ulift_down` in
  `Jacobian/Construction.lean`, composed with the axiom-free
  `LieAddGroup (ComplexTorus V L)` instance.

Reference: Mumford Vol I §II.3; Griffiths-Harris Ch. 2.3; Forster Ch. III.
See `docs/formalization-plan.md` §7.
-/
import Jacobians.Jacobian.Construction
import Jacobians.Axioms.BranchLocus

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety

/-! ### Primitive functional axioms: path-integral functional + local
antiderivative + functorial primitives on 1-forms

The axioms in this section are the **atomic classical facts** we
axiomatize. Each is smaller-grained than the packaged "pushforward on
Jacobians" or "Abel-Jacobi map" axioms they replace. Per external review
(Gemini 2026-04-23), the single-functional axiom
`pathIntegralBasepointFunctional` on its own is too weak — it can be
satisfied by trivial maps disconnected from the 1-form cocycle — so it
is paired here with `AX_pathIntegral_local_antiderivative`, which binds
it to the chart-local 1-form coefficient.

Similarly, pushforward/pullback on Jacobians factor through
`pullbackOneForm` / `pushforwardOneForm` (pullback and trace of
holomorphic 1-forms). The ambient linear maps and period-lattice
preservation are then derived or re-expressed at the more atomic level.
-/

/-- **Axiom.** The path-integral functional from `P₀` to `P`: given a
holomorphic 1-form `ω`, returns `∫_{P₀}^P ω ∈ ℂ`. Linear in `ω`. For
two paths from `P₀` to `P`, the values differ by an element of the
period lattice.

Retires to a `def` once multi-chart path integration +
`pathIntegralAnalyticArc` land. On its own this axiom is too weak
(the choice function could be trivial); it is **load-bearing** only in
combination with `AX_pathIntegral_local_antiderivative` below. -/
axiom pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ

/-- **Axiom.** Local antiderivative property: the derivative of the
path integral w.r.t. the upper endpoint, viewed in the chart at `P`,
equals the chart-local coefficient of the 1-form at `P`.

Precisely: the scalar function `z ↦ (∫_{P₀}^{φ⁻¹(z)} ω)` has derivative
`form.coeff P (φ(P))` at `z = φ(P)`, where `φ = extChartAt 𝓘(ℂ) P`.

This is the Fundamental Theorem of Calculus for path integrals of
1-forms, localised to one chart. It links
`pathIntegralBasepointFunctional` to the cocycle-predicate content of
`HolomorphicOneForm`, preventing the zero-functional (or any other
trivial choice) from silently satisfying downstream smoothness /
injectivity claims. -/
axiom AX_pathIntegral_local_antiderivative (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        pathIntegralBasepointFunctional X P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P)

/-- **Axiom.** The pullback of holomorphic 1-forms along a holomorphic
map `f : X → Y`, as a ℂ-linear map of `HolomorphicOneForm` modules.

Classical content: `(pullbackOneForm f) ω_Y = ω_Y ∘ df` on the cocycle
data. Linearity is obvious; the fact that the result still satisfies
the cocycle condition is the main content and uses holomorphicity of
`f`. -/
axiom pullbackOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X

/-- **Axiom.** The pushforward (trace) of holomorphic 1-forms along a
non-constant holomorphic map `f : X → Y` between compact Riemann
surfaces. Classical content: for `ω ∈ Ω¹(X)` and `q ∈ Y`,
`(pushforwardOneForm f)(ω) (q) = Σ_{p ∈ f⁻¹(q)} (local contribution)`,
with multiplicities counted by `localOrder`. For constant `f` this is
the zero map. -/
axiom pushforwardOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y

/-! ### Functoriality axioms on the form-level primitives

Per Gemini 2026-04-23 review: "functoriality on Jacobians is free via
contravariance of `Module.Dual`" — so we axiomatize functoriality at
the form-level (atomic classical fact: pullback commutes with
composition), and the Jacobian-level functoriality becomes derivable. -/

/-- **Axiom.** Pullback of 1-forms preserves identity. -/
axiom AX_pullbackOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pullbackOneForm (id : X → X) contMDiff_id = LinearMap.id

/-- **Axiom.** Pullback of 1-forms is contravariant under composition.
Classical: `(g ∘ f)^* ω = f^* (g^* ω)`. -/
axiom AX_pullbackOneForm_comp {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {Z : Type w} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackOneForm (g ∘ f) (hg.comp hf) =
      (pullbackOneForm f hf).comp (pullbackOneForm g hg)

/-- **Axiom.** Pushforward (trace) of 1-forms preserves identity. -/
axiom AX_pushforwardOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pushforwardOneForm (id : X → X) contMDiff_id = LinearMap.id

/-- **Axiom.** Pushforward (trace) of 1-forms is covariant under
composition. Classical: `(g ∘ f)_* ω = g_* (f_* ω)`. -/
axiom AX_pushforwardOneForm_comp {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {Z : Type w} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardOneForm (g ∘ f) (hg.comp hf) =
      (pushforwardOneForm g hg).comp (pushforwardOneForm f hf)

/-! ### `ofCurve` as a real definition -/

/-- The ambient Abel-Jacobi: `(P₀, P) ↦ (∫_{P₀}^P ω_i)_i` where `ω_i`
is the `i`-th vector of `jacobianBasis X`.

This is now a real `def`; the only remaining axiomatization is at the
level of the single-form functional `pathIntegralBasepointFunctional`.
Note the result is in `Fin (genus X) → ℂ` before quotienting by the
period lattice — different paths produce lifts that agree modulo the
period lattice, and descent to `Jacobian` (= quotient by the lattice)
makes the choice irrelevant. -/
noncomputable def ofCurveAmbient (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : X → X → (Fin (genus X) → ℂ) :=
  fun P₀ P i => pathIntegralBasepointFunctional X P₀ P (jacobianBasis X i)

/-- The Abel-Jacobi map `ofCurveImpl P₀ : X → Jacobian X`, real `def`.
Subtracts `ofCurveAmbient X P₀ P₀` in the numerator so that the
basepoint-sent-to-zero property `ofCurveImpl X P₀ P₀ = 0` is
definitional (not a separate axiom). -/
noncomputable def ofCurveImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ : X) : X → Jacobian X :=
  fun P => ULift.up <|
    QuotientAddGroup.mk' _ (ofCurveAmbient X P₀ P - ofCurveAmbient X P₀ P₀)

/-! ### Properties of `ofCurveImpl` (axioms for now) -/

/-- **Axiom.** The Abel-Jacobi map is smooth/holomorphic. -/
axiom AX_ofCurve_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ContMDiff 𝓘(ℂ, ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ofCurveImpl X P)

/-- **Theorem (derived 2026-04-23).** The Abel-Jacobi map sends the
basepoint to zero — definitional from the subtraction in `ofCurveImpl`. -/
theorem AX_ofCurve_self {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ofCurveImpl X P P = 0 := by
  unfold ofCurveImpl
  ext : 1
  simp
  rfl

/-- **Axiom (= Abel's theorem, curve side).** The Abel-Jacobi map is
injective when `genus X > 0`. -/
axiom AX_ofCurve_inj {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) (_h : 0 < genus X) :
    Function.Injective (ofCurveImpl X P)

/-! ### Ambient linear maps — derived from the form-level primitives -/

/-- The ambient ℂ-linear map underlying the pushforward on Jacobians,
as a real `def`. Derived as the basis-transport of `(pullbackOneForm f
hf).dualMap`: pushforward on the dual `(HolomorphicOneForm X)∨ →
(HolomorphicOneForm Y)∨` is the standard dual of the pullback of
1-forms, so functoriality properties on the Jacobians follow
contravariantly from properties of `pullbackOneForm` (no extra
ambient-level axiom is needed for functoriality, only for
lattice-preservation). -/
noncomputable def pushforwardAmbientLinear {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) :=
  let eX : (HolomorphicOneForm X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
    (jacobianBasis X).dualBasis.equivFun
  let eY : (HolomorphicOneForm Y →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (genus Y) → ℂ) :=
    (jacobianBasis Y).dualBasis.equivFun
  eY.toLinearMap.comp
    ((pullbackOneForm f hf).dualMap.comp eX.symm.toLinearMap)

/-- The ambient ℂ-linear map underlying the pullback on Jacobians, as
a real `def`. Symmetric construction using `pushforwardOneForm`
(trace of 1-forms). -/
noncomputable def pullbackAmbientLinear {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ) :=
  let eX : (HolomorphicOneForm X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
    (jacobianBasis X).dualBasis.equivFun
  let eY : (HolomorphicOneForm Y →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (genus Y) → ℂ) :=
    (jacobianBasis Y).dualBasis.equivFun
  eX.toLinearMap.comp
    ((pushforwardOneForm f hf).dualMap.comp eY.symm.toLinearMap)

/-- **Axiom.** Lattice preservation: the pushforward ambient map sends
the period lattice of `X` into the period lattice of `Y`.

Classical content: the period-map naturality `∫_{f_*γ} ω_Y = ∫_γ
(pullbackOneForm f) ω_Y`, combined with the fact that `f_*` sends
integer cycles to integer cycles. Retires to a theorem once
`pushforwardH1` + path-integral naturality land. -/
axiom AX_pushforwardAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
              (jacobianBasis X)).toAddSubgroup,
      (pushforwardAmbientLinear f hf) v ∈
        (periodLatticeInBasis Y (Classical.arbitrary Y)
          (jacobianBasis Y)).toAddSubgroup

/-- **Axiom.** Lattice preservation for pullback. Symmetric to
`AX_pushforwardAmbient_preserves_lattice`. -/
axiom AX_pullbackAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
              (jacobianBasis Y)).toAddSubgroup,
      (pullbackAmbientLinear f hf) v ∈
        (periodLatticeInBasis X (Classical.arbitrary X)
          (jacobianBasis X)).toAddSubgroup

/-! ### Helper: descend an ambient ℂ-linear lattice-preserving map to
a continuous add-monoid hom of Jacobians. -/

/-- Build a `Jacobian X →ₜ+ Jacobian Y` from an ambient ℂ-linear map
preserving the period lattices. Packages the three moves:
  (1) `QuotientAddGroup.map` descends the linear map to a hom of
      quotients `V⧸LX → W⧸LY`;
  (2) continuity is automatic because `L` is ℂ-linear on a
      finite-dim normed space, hence continuous, and the quotient map
      `V → V⧸LX` is a quotient map;
  (3) `ULift.up / .down` wrap to match the universe-lifted `Jacobian`. -/
noncomputable def jacobianHomOfAmbient (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (L : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))
    (hL : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                    (jacobianBasis X)).toAddSubgroup,
            L v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
                      (jacobianBasis Y)).toAddSubgroup) :
    Jacobian X →ₜ+ Jacobian Y :=
  let LX := (periodLatticeInBasis X (Classical.arbitrary X)
              (jacobianBasis X)).toAddSubgroup
  let LY := (periodLatticeInBasis Y (Classical.arbitrary Y)
              (jacobianBasis Y)).toAddSubgroup
  let qMap : (Fin (genus X) → ℂ) ⧸ LX →+ (Fin (genus Y) → ℂ) ⧸ LY :=
    QuotientAddGroup.map LX LY L.toAddMonoidHom hL
  { toFun := fun p => ULift.up (qMap p.down)
    map_zero' := by
      apply ULift.ext
      exact map_zero qMap
    map_add' := by
      intro a b
      apply ULift.ext
      exact map_add qMap a.down b.down
    continuous_toFun := by
      -- L is continuous (finite-dim ℂ-linear); `QuotientAddGroup.mk' LY ∘ L`
      -- descends through the quotient map on source, giving continuity of `qMap`.
      have hL_cont : Continuous (L : (Fin (genus X) → ℂ) → (Fin (genus Y) → ℂ)) :=
        L.continuous_of_finiteDimensional
      have hqCont : Continuous qMap := by
        refine continuous_quot_lift _ ?_
        exact (continuous_quot_mk).comp hL_cont
      exact (continuous_uliftUp).comp (hqCont.comp continuous_uliftDown) }

/-! ### `pushforward` and `pullback` as real definitions -/

/-- The pushforward on Jacobians, as a real `def`. -/
noncomputable def pushforwardImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf)
    (AX_pushforwardAmbient_preserves_lattice f hf)

/-- The pullback on Jacobians, as a real `def`. -/
noncomputable def pullbackImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  jacobianHomOfAmbient Y X (pullbackAmbientLinear f hf)
    (AX_pullbackAmbient_preserves_lattice f hf)

/-! ### `degree` as a real definition -/

/-- The degree of a holomorphic map between compact Riemann surfaces,
as a real `def`. Zero if `f` is constant; otherwise the common
fiber-weighted count from `AX_BranchLocus`. -/
noncomputable def degreeImpl {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := by
  classical
  exact if hc : ∃ c : Y, ∀ x : X, f x = c then 0
        else Classical.choose (AX_BranchLocus f hf hc)

/-! ### Property axioms for pushforward / pullback / degree

These are properties of the real `def`s above. Each retires via a
textbook proof once the corresponding analytic / branch-locus
infrastructure lands. -/

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

/-- The Lie group structure on the universe-lifted Jacobian, now derived
through the ULift transfer lemmas in `Jacobian/Construction.lean`. -/
theorem AX_jacobian_lieAddGroup {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  infer_instance

end Jacobians.Axioms
