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
- `pullbackOneForm (f : X → Y) : HolomorphicOneForm Y →ₗ[ℂ]
  HolomorphicOneForm X` — **def**, transported across the Kirov
  holomorphic-1-form equivalence; feeds `pushforwardAmbientLinear`.

Still axiomatic (smaller-grained than before; 2026-04-23 round-2
refactor responded to Gemini review by adding the local-antiderivative
axiom and structured form primitives):\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
- `pathIntegralBasepointFunctional` — the functional
  `X → X → (HolomorphicOneForm X →ₗ[ℂ] ℂ)`, "integrate from `P₀` to
  `P`". De-opaqued to `canonicalArcIntegral (Bridge.bridgePathArc P₀ P)`;
  linearity is transported from `Bridge.kirovBackedFunctional` via the bridge
  equality to keep the computed values identical. (A former companion FTC axiom
  `AX_pathIntegral_local_antiderivative`
  was DELETED 2026-06-04 — it was false; see the note where it stood. The
  anti-degeneracy it was meant to provide comes instead from the concrete integral
  being genuine, provably nonzero on the `Elliptic` period witness.)
- `pushforwardOneForm (f : X → Y) : HolomorphicOneForm X →ₗ[ℂ]
  HolomorphicOneForm Y` — the trace / pushforward of 1-forms along a
  finite cover. Analogously feeds `pullbackAmbientLinear` as a `def`.
- `AX_pushforwardAmbient_preserves_lattice`,
  `AX_pullbackAmbient_preserves_lattice` — still axioms; retire to
  theorems once period-map naturality is derived.
- Property axioms (`AX_ofCurve_contMDiff`, `AX_ofCurve_inj`,
  `AX_pushforward_contMDiff`, pushforward functoriality,
  `AX_pushforward_pullback`)
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
import Jacobians.Bridge.KirovHolomorphicEquiv
import Jacobians.Bridge.KirovCanonicalEq

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety

/-! ### Primitive functional axioms: path-integral functional + local
antiderivative + form-level primitives

The axioms in this section are the **atomic classical facts** we
axiomatize. Each is smaller-grained than the packaged "pushforward on
Jacobians" or "Abel-Jacobi map" axioms they replace. Per external review
(Gemini 2026-04-23), the single-functional axiom
`pathIntegralBasepointFunctional` on its own is too weak — it can be
satisfied by trivial maps disconnected from the 1-form cocycle. The
former remedy (a companion FTC axiom binding it to the chart coefficient)
was **wrong**: that axiom (`AX_pathIntegral_local_antiderivative`) was
false (it forced a global primitive — see its deletion note). The correct
remedy is to make the functional **concrete** — the canonical moving-chart
arc integral over `Bridge.bridgePathArc P₀ P`, pointwise equal to
`Bridge.kirovBackedFunctional` — rather than to bind an opaque functional
with a (false) FTC.

Similarly, pushforward/pullback on Jacobians factor through
`pullbackOneForm` / `pushforwardOneForm` (pullback and trace of
holomorphic 1-forms). Pullback is now transported from Kirov's
cotangent-bundle-section model; pushforward remains the trace primitive.
The ambient linear maps and period-lattice preservation are then derived
or re-expressed at the more atomic level.
-/

/-- The path-integral functional from `P₀` to `P`: given a holomorphic 1-form
`ω`, returns `∫_{P₀}^P ω ∈ ℂ`, linear in `ω`. For two paths from `P₀` to `P`
the values differ by an element of the period lattice.

**De-opaqued 2026-06-04** from an axiom to this real `def`, then re-based onto
the canonical moving-chart arc integral in U3: it computes
`canonicalArcIntegral (Bridge.bridgePathArc P₀ P)`. Linearity is borrowed from
`Bridge.kirovBackedFunctional` through
`Bridge.kirovBackedFunctional_eq_canonicalArcIntegral`, so the values remain
pointwise equal to the previous Kirov-backed definition while the `ofCurve`
chain now routes through `canonicalArcIntegral` / `bridgePathArc`. This makes
`ofCurve` a **computed** map and rules out the zero-functional degeneracy by
*concreteness* — not by a companion FTC (the former
`AX_pathIntegral_local_antiderivative` was false and is deleted; see its note).
The path-dependence of the chosen `bridgePath` is absorbed by the period-lattice
quotient in `ofCurveImpl`, governed by `RiemannSurface.loopIntegralToH1`. -/
noncomputable def pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun form :=
    canonicalArcIntegral (Jacobians.Bridge.bridgePathArc P₀ P) form
  map_add' form₁ form₂ := by
    rw [← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
        (X := X) P₀ P (form₁ + form₂),
      ← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
        (X := X) P₀ P form₁,
      ← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
        (X := X) P₀ P form₂]
    exact (Jacobians.Bridge.kirovBackedFunctional P₀ P).map_add' form₁ form₂
  map_smul' c form := by
    rw [← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
        (X := X) P₀ P (c • form),
      ← Jacobians.Bridge.kirovBackedFunctional_eq_canonicalArcIntegral
        (X := X) P₀ P form]
    exact (Jacobians.Bridge.kirovBackedFunctional P₀ P).map_smul' c form

/- **REMOVED 2026-06-04 — this axiom was FALSE.**

The former `AX_pathIntegral_local_antiderivative` asserted, for a
*single-valued* `ℂ`-valued functional `H(Q) := pathIntegralBasepointFunctional
X P₀ Q form`, that `z ↦ H((extChartAt P).symm z)` has derivative
`form.coeff P (φ P)` at `z = φ P`, **for every `P`**. Quantified over all `P`,
that makes `H : X → ℂ` complex-differentiable at every point with
`mfderiv H = ω_form`, i.e. a *global primitive* of the holomorphic 1-form
`form`. Then every period `∮_γ ω_form = ∮_γ dH = 0` — contradicting the
existence of holomorphic 1-forms with nonzero periods on any genus `≥ 1`
curve (e.g. `genus_Elliptic = 1`, `∮_{aLoop} ω₁ ≠ 0`). So the axiom asserted
a falsehood and was an unsoundness landmine; it was *dangling* (no headline
depended on it). It is deleted, not relabelled (a prior relabelling attempt
was reverted — see `KirovLineIntegral.lean`).

The honest content: the Abel–Jacobi map is genuinely multivalued, landing in
`ℂ^g/Λ` (`ofCurveImpl`, the quotient below). Path-independence enters at the
**closed-loop / homology** level via the (true, standard) axiom
`Jacobians.RiemannSurface.loopIntegralToH1` — `∮_γ ω` depends only on
`[γ] ∈ H₁` — which is what makes the period lattice and `ofCurve` well-defined.
A real local-antiderivative ("FTC") statement, if ever wanted, must be made at
the quotient level (`ofCurve` is manifold-differentiable, the period ambiguity
being locally constant), *not* on a single-valued ℂ lift. -/

/-- The pullback of holomorphic 1-forms along a holomorphic map `f : X → Y`,
as a ℂ-linear map of `HolomorphicOneForm` modules.

This is transported across `Jacobians.Bridge.bridgeFormEquiv` from Kirov's
cotangent-bundle-section pullback. -/
noncomputable def pullbackOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X :=
  (Jacobians.Bridge.bridgeFormEquiv (X := X)).symm.toLinearMap.comp
    ((Jacobians.Vendor.Kirov.pullbackForm f _hf).comp
      (Jacobians.Bridge.bridgeFormEquiv (X := Y)).toLinearMap)

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

/-! ### Functoriality on the form-level primitives

Per Gemini 2026-04-23 review: "functoriality on Jacobians is free via
contravariance of `Module.Dual`" — so we prove or state functoriality at
the form-level. Pullback identity/composition are now theorems via Kirov
transport; pushforward identity/composition remain trace axioms. The
Jacobian-level functoriality then becomes derivable. -/

/-- Pullback of 1-forms preserves identity. -/
theorem AX_pullbackOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pullbackOneForm (id : X → X) contMDiff_id = LinearMap.id := by
  unfold pullbackOneForm
  rw [Jacobians.Vendor.Kirov.pullbackForm_id]
  ext form
  simp

/-- Pullback of 1-forms is contravariant under composition.
Classical: `(g ∘ f)^* ω = f^* (g^* ω)`. -/
theorem AX_pullbackOneForm_comp {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {Z : Type w} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackOneForm (g ∘ f) (hg.comp hf) =
      (pullbackOneForm f hf).comp (pullbackOneForm g hg) := by
  unfold pullbackOneForm
  rw [Jacobians.Vendor.Kirov.pullbackForm_comp f hf g hg (hg.comp hf)]
  ext form
  simp [LinearMap.comp_apply]

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

theorem jacobianHomOfAmbient_id_apply (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (P : Jacobian X) :
    jacobianHomOfAmbient X X (LinearMap.id : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ))
      (by
        intro v hv
        simpa using hv) P = P := by
  rcases P with ⟨P⟩
  apply ULift.ext
  refine Quotient.inductionOn P ?_
  intro v
  change
      (QuotientAddGroup.map
        (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
        (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
        LinearMap.id.toAddMonoidHom
        (by
          intro w hw
          simpa using hw))
        (QuotientAddGroup.mk'
          (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup v) =
    QuotientAddGroup.mk'
      (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup v
  simpa using
    (QuotientAddGroup.map_mk'
      (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
      (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
      LinearMap.id.toAddMonoidHom
      (by
        intro w hw
        simpa using hw)
      v)

theorem jacobianHomOfAmbient_comp_apply
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (Z : Type w) [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (LXY : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))
    (hXY : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                    (jacobianBasis X)).toAddSubgroup,
              LXY v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
                  (jacobianBasis Y)).toAddSubgroup)
    (LYZ : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus Z) → ℂ))
    (hYZ : ∀ v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
                    (jacobianBasis Y)).toAddSubgroup,
              LYZ v ∈ (periodLatticeInBasis Z (Classical.arbitrary Z)
                  (jacobianBasis Z)).toAddSubgroup)
    (hXZ : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                    (jacobianBasis X)).toAddSubgroup,
              (LYZ.comp LXY) v ∈ (periodLatticeInBasis Z (Classical.arbitrary Z)
                  (jacobianBasis Z)).toAddSubgroup)
    (P : Jacobian X) :
    jacobianHomOfAmbient X Z (LYZ.comp LXY) hXZ P =
      jacobianHomOfAmbient Y Z LYZ hYZ (jacobianHomOfAmbient X Y LXY hXY P) := by
  rcases P with ⟨P⟩
  apply ULift.ext
  refine Quotient.inductionOn P ?_
  intro v
  change
      (QuotientAddGroup.map
        (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
        (periodLatticeInBasis Z (Classical.arbitrary Z) (jacobianBasis Z)).toAddSubgroup
        (LYZ.comp LXY).toAddMonoidHom hXZ)
        (QuotientAddGroup.mk'
          (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup v) =
    (QuotientAddGroup.map
      (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup
      (periodLatticeInBasis Z (Classical.arbitrary Z) (jacobianBasis Z)).toAddSubgroup
      LYZ.toAddMonoidHom hYZ)
      ((QuotientAddGroup.map
        (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
        (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup
        LXY.toAddMonoidHom hXY)
        (QuotientAddGroup.mk'
          (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup v))
  simp [QuotientAddGroup.map_mk']

theorem jacobianHomOfAmbient_congr_apply
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {L L' : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hLL' : L = L')
    (hL : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                    (jacobianBasis X)).toAddSubgroup,
              L v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
                  (jacobianBasis Y)).toAddSubgroup)
    (hL' : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                    (jacobianBasis X)).toAddSubgroup,
              L' v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
                  (jacobianBasis Y)).toAddSubgroup)
    (P : Jacobian X) :
    jacobianHomOfAmbient X Y L hL P = jacobianHomOfAmbient X Y L' hL' P := by
  subst hLL'
  rfl

theorem pushforwardAmbientLinear_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pushforwardAmbientLinear (id : X → X) contMDiff_id = LinearMap.id := by
  ext v i
  simp [pushforwardAmbientLinear, AX_pullbackOneForm_id, LinearMap.dualMap_id]

theorem pullbackAmbientLinear_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pullbackAmbientLinear (id : X → X) contMDiff_id = LinearMap.id := by
  ext v i
  simp [pullbackAmbientLinear, AX_pushforwardOneForm_id, LinearMap.dualMap_id]

theorem pushforwardAmbientLinear_comp
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardAmbientLinear (g ∘ f) (hg.comp hf) =
      (pushforwardAmbientLinear g hg).comp (pushforwardAmbientLinear f hf) := by
  apply LinearMap.ext
  intro v
  show ((jacobianBasis Z).dualBasis.equivFun : _ ≃ₗ[ℂ] _)
      ((pullbackOneForm (g ∘ f) (hg.comp hf)).dualMap
        (((jacobianBasis X).dualBasis.equivFun).symm v)) = _
  rw [AX_pullbackOneForm_comp f hf g hg,
      ← LinearMap.dualMap_comp_dualMap (pullbackOneForm g hg) (pullbackOneForm f hf)]
  simp only [pushforwardAmbientLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

theorem pullbackAmbientLinear_comp
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackAmbientLinear (g ∘ f) (hg.comp hf) =
      (pullbackAmbientLinear f hf).comp (pullbackAmbientLinear g hg) := by
  apply LinearMap.ext
  intro v
  show ((jacobianBasis X).dualBasis.equivFun : _ ≃ₗ[ℂ] _)
      ((pushforwardOneForm (g ∘ f) (hg.comp hf)).dualMap
        (((jacobianBasis Z).dualBasis.equivFun).symm v)) = _
  rw [AX_pushforwardOneForm_comp f hf g hg,
      ← LinearMap.dualMap_comp_dualMap (pushforwardOneForm f hf) (pushforwardOneForm g hg)]
  simp only [pullbackAmbientLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

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

/-- Pushforward is the identity on identity. (Functoriality, part 1.) -/
theorem AX_pushforward_id_apply {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : Jacobian X) :
    pushforwardImpl X X id contMDiff_id P = P := by
  simpa [pushforwardImpl, pushforwardAmbientLinear_id] using
    (jacobianHomOfAmbient_id_apply X P)

/-- Pushforward respects composition. (Functoriality, part 2.) -/
theorem AX_pushforward_comp_apply
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
      pushforwardImpl Y Z g hg (pushforwardImpl X Y f hf P) := by
  -- Helper: composite lattice preservation
  have hXZ : ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
                      (jacobianBasis X)).toAddSubgroup,
      ((pushforwardAmbientLinear g hg).comp (pushforwardAmbientLinear f hf)) v ∈
        (periodLatticeInBasis Z (Classical.arbitrary Z)
          (jacobianBasis Z)).toAddSubgroup := fun v hv => by
    simpa using AX_pushforwardAmbient_preserves_lattice g hg _
      (AX_pushforwardAmbient_preserves_lattice f hf v hv)
  calc pushforwardImpl X Z (g ∘ f) (hg.comp hf) P
      = jacobianHomOfAmbient X Z
          ((pushforwardAmbientLinear g hg).comp (pushforwardAmbientLinear f hf)) hXZ P := by
        apply jacobianHomOfAmbient_congr_apply
        exact pushforwardAmbientLinear_comp f hf g hg
    _ = pushforwardImpl Y Z g hg (pushforwardImpl X Y f hf P) :=
        jacobianHomOfAmbient_comp_apply X Y Z
          (pushforwardAmbientLinear f hf) (AX_pushforwardAmbient_preserves_lattice f hf)
          (pushforwardAmbientLinear g hg) (AX_pushforwardAmbient_preserves_lattice g hg)
          hXZ P

/-- **Axiom.** Pullback on Jacobians is smooth. -/
axiom AX_pullback_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullbackImpl X Y f hf)

/-- Pullback is the identity on identity. (Functoriality, part 1.) -/
theorem AX_pullback_id_apply {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : Jacobian X) :
    pullbackImpl X X id contMDiff_id P = P := by
  simpa [pullbackImpl, pullbackAmbientLinear_id] using
    (jacobianHomOfAmbient_id_apply X P)

/-- Pullback respects composition (contravariantly). (Functoriality, part 2.) -/
theorem AX_pullback_comp_apply
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
      pullbackImpl X Y f hf (pullbackImpl Y Z g hg P) := by
  have hZX : ∀ v ∈ (periodLatticeInBasis Z (Classical.arbitrary Z)
                      (jacobianBasis Z)).toAddSubgroup,
      ((pullbackAmbientLinear f hf).comp (pullbackAmbientLinear g hg)) v ∈
        (periodLatticeInBasis X (Classical.arbitrary X)
          (jacobianBasis X)).toAddSubgroup := fun v hv => by
    simpa using AX_pullbackAmbient_preserves_lattice f hf _
      (AX_pullbackAmbient_preserves_lattice g hg v hv)
  calc pullbackImpl X Z (g.comp f) (hg.comp hf) P
      = jacobianHomOfAmbient Z X
          ((pullbackAmbientLinear f hf).comp (pullbackAmbientLinear g hg)) hZX P := by
        apply jacobianHomOfAmbient_congr_apply
        exact pullbackAmbientLinear_comp f hf g hg
    _ = pullbackImpl X Y f hf (pullbackImpl Y Z g hg P) :=
        jacobianHomOfAmbient_comp_apply Z Y X
          (pullbackAmbientLinear g hg) (AX_pullbackAmbient_preserves_lattice g hg)
          (pullbackAmbientLinear f hf) (AX_pullbackAmbient_preserves_lattice f hf)
          hZX P

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
