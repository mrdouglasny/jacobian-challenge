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
- Property axioms (`AX_ofCurve_contMDiff`,
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
import Jacobians.RiemannSurface.LoopIntegralHom
import Jacobians.RiemannSurface.ArcAlgebra
import Jacobians.Bridge.KirovHolomorphicEquiv
import Jacobians.Bridge.KirovCanonicalEq
import Jacobians.Vendor.Kirov.ZLatticeQuotient

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

/-- **Theorem (period 1-cocycle).** For any three points and piecewise-analytic arcs
between them, the period of the closed 1-cycle `p_xz - p_xy - p_yz` lies in the
period lattice. Minimal analytic content of homotopy invariance (Stokes for closed
forms over 1-cycles); genus-1 instance PROVEN
(`analyticLoop_..._mem_lattice`). Form B (triangle) chosen over the loop form
after two deep-think passes (REFORMULATE verdict) to avoid arc-concat/reversal +
cross-basepoint identification. Ref: Griffiths-Harris Ch.2; Forster §21. Vetted
DT + external deep-think 2026-06-05. -/
theorem AX_Period_Triangle {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (x y z : X) (p_xy p_yz p_xz : AnalyticArc X)
    (h_xy0 : p_xy.extend 0 = x) (h_xy1 : p_xy.extend 1 = y)
    (h_yz0 : p_yz.extend 0 = y) (h_yz1 : p_yz.extend 1 = z)
    (h_xz0 : p_xz.extend 0 = x) (h_xz1 : p_xz.extend 1 = z) :
    (fun i => canonicalArcIntegral p_xz (jacobianBasis X i)
            - (canonicalArcIntegral p_xy (jacobianBasis X i)
             + canonicalArcIntegral p_yz (jacobianBasis X i)))
      ∈ periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X) := by
  classical
  let x₀ : X := Classical.arbitrary X
  let b := jacobianBasis X
  let p₀x : AnalyticArc X := Jacobians.Bridge.bridgePathArc (X := X) x₀ x
  have hp₀x0 : p₀x.extend 0 = x₀ := by
    simp [p₀x, Jacobians.Bridge.bridgePathArc]
  have hp₀x1 : p₀x.extend 1 = x := by
    simp [p₀x, Jacobians.Bridge.bridgePathArc]
  have hxy_yz : p_xy.extend 1 = p_yz.extend 0 := by
    rw [h_xy1, h_yz0]
  let xy_yz : AnalyticArc X := p_xy.trans p_yz hxy_yz
  have hxy_yz_xz :
      xy_yz.extend 1 = p_xz.reverse.extend 0 := by
    simp [xy_yz, h_yz1, h_xz1]
  let tri : AnalyticArc X := xy_yz.trans p_xz.reverse hxy_yz_xz
  have htri0 : tri.extend 0 = x := by
    simp [tri, xy_yz, h_xy0]
  have htri1 : tri.extend 1 = x := by
    simp [tri, h_xz0]
  have hp₀x_tri : p₀x.extend 1 = tri.extend 0 := by
    rw [hp₀x1, htri0]
  let p₀x_tri : AnalyticArc X := p₀x.trans tri hp₀x_tri
  have hp₀x_tri_rev :
      p₀x_tri.extend 1 = p₀x.reverse.extend 0 := by
    simp [p₀x_tri, htri1, hp₀x1]
  let closedArc : AnalyticArc X := p₀x_tri.trans p₀x.reverse hp₀x_tri_rev
  let closedLoop : AnalyticLoop X x₀ :=
    { arc := closedArc
      start_eq := by
        simp [closedArc, p₀x_tri, hp₀x0]
      end_eq := by
        simp [closedArc, hp₀x0] }
  have hloop_mem :
      (fun i => canonicalArcIntegral closedLoop.arc (b i)) ∈
        periodLatticeInBasis X x₀ b :=
    Jacobians.RiemannSurface.loop_canonicalArcIntegral_mem_periodLatticeInBasis
      x₀ b closedLoop
  have hneg :
      -(fun i => canonicalArcIntegral closedLoop.arc (b i)) ∈
        periodLatticeInBasis X x₀ b :=
    Submodule.neg_mem _ hloop_mem
  convert hneg using 1
  ext i
  have hint (γ : AnalyticArc X) :
      IntervalIntegrable (canonicalIntegrand γ (b i)) MeasureTheory.volume 0 1 :=
    analyticArc_canonicalIntegrand_intervalIntegrable γ (b i)
  have hxyyz :
      canonicalArcIntegral xy_yz (b i) =
        canonicalArcIntegral p_xy (b i) + canonicalArcIntegral p_yz (b i) :=
    canonicalArcIntegral_trans p_xy p_yz hxy_yz (b i) (hint p_xy) (hint p_yz)
  have htri :
      canonicalArcIntegral tri (b i) =
        canonicalArcIntegral xy_yz (b i) + canonicalArcIntegral p_xz.reverse (b i) :=
    canonicalArcIntegral_trans xy_yz p_xz.reverse hxy_yz_xz (b i)
      (hint xy_yz) (hint p_xz.reverse)
  have hp₀xtri :
      canonicalArcIntegral p₀x_tri (b i) =
        canonicalArcIntegral p₀x (b i) + canonicalArcIntegral tri (b i) :=
    canonicalArcIntegral_trans p₀x tri hp₀x_tri (b i) (hint p₀x) (hint tri)
  have hclosed :
      canonicalArcIntegral closedArc (b i) =
        canonicalArcIntegral p₀x_tri (b i) + canonicalArcIntegral p₀x.reverse (b i) :=
    canonicalArcIntegral_trans p₀x_tri p₀x.reverse hp₀x_tri_rev (b i)
      (hint p₀x_tri) (hint p₀x.reverse)
  have hxzrev :
      canonicalArcIntegral p_xz.reverse (b i) =
        -canonicalArcIntegral p_xz (b i) :=
    canonicalArcIntegral_reverse p_xz (b i)
  have hp₀xrev :
      canonicalArcIntegral p₀x.reverse (b i) =
        -canonicalArcIntegral p₀x (b i) :=
    canonicalArcIntegral_reverse p₀x (b i)
  simp only [Pi.neg_apply]
  rw [hclosed, hp₀xtri, htri, hxyyz, hxzrev, hp₀xrev]
  ring

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

/-- The degree-zero Abel-Jacobi difference is independent of the chosen basepoint. -/
theorem ofCurveImpl_basepoint_independent {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (b b' Q₁ Q₂ : X) :
    ofCurveImpl X b Q₁ - ofCurveImpl X b Q₂ =
      ofCurveImpl X b' Q₁ - ofCurveImpl X b' Q₂ := by
  let Λ := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  have htri₁ := AX_Period_Triangle (X := X) (x := b') (y := b) (z := Q₁)
    (p_xy := Jacobians.Bridge.bridgePathArc (X := X) b' b)
    (p_yz := Jacobians.Bridge.bridgePathArc (X := X) b Q₁)
    (p_xz := Jacobians.Bridge.bridgePathArc (X := X) b' Q₁)
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
  have htri₂ := AX_Period_Triangle (X := X) (x := b') (y := b) (z := Q₂)
    (p_xy := Jacobians.Bridge.bridgePathArc (X := X) b' b)
    (p_yz := Jacobians.Bridge.bridgePathArc (X := X) b Q₂)
    (p_xz := Jacobians.Bridge.bridgePathArc (X := X) b' Q₂)
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
  have htri₁' :
      (ofCurveAmbient X b' Q₁ - (ofCurveAmbient X b' b + ofCurveAmbient X b Q₁)) ∈ Λ := by
    simpa [Λ, ofCurveAmbient, pathIntegralBasepointFunctional] using htri₁
  have htri₂' :
      (ofCurveAmbient X b' Q₂ - (ofCurveAmbient X b' b + ofCurveAmbient X b Q₂)) ∈ Λ := by
    simpa [Λ, ofCurveAmbient, pathIntegralBasepointFunctional] using htri₂
  have hmem :
      ((ofCurveAmbient X b Q₁ - ofCurveAmbient X b Q₂) -
        (ofCurveAmbient X b' Q₁ - ofCurveAmbient X b' Q₂)) ∈ Λ := by
    have hsub := sub_mem htri₂' htri₁'
    convert hsub using 1
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  unfold ofCurveImpl
  change ULift.up
      ((QuotientAddGroup.mk' Λ.toAddSubgroup (ofCurveAmbient X b Q₁ - ofCurveAmbient X b b)) -
        QuotientAddGroup.mk' Λ.toAddSubgroup (ofCurveAmbient X b Q₂ - ofCurveAmbient X b b)) =
    ULift.up
      ((QuotientAddGroup.mk' Λ.toAddSubgroup
          (ofCurveAmbient X b' Q₁ - ofCurveAmbient X b' b')) -
        QuotientAddGroup.mk' Λ.toAddSubgroup (ofCurveAmbient X b' Q₂ - ofCurveAmbient X b' b'))
  apply congrArg ULift.up
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply]
  rw [← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
  apply (QuotientAddGroup.eq_iff_sub_mem (N := Λ.toAddSubgroup)).mpr
  convert hmem using 1
  ext i
  simp only [Pi.sub_apply]
  abel

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

/-- Smoothness engine for quotient-torus pushforward maps, using
`ComplexTorus.instChartedSpace` on both source and target. The proof works
at the chart level: after `contMDiffAt_iff`, it shows the chart composition
`extChartAt ∘ fCT ∘ (extChartAt).symm` equals the affine map `Φ + c₀`
(where `c₀` is a fixed lattice element) on a neighbourhood, which is smooth
because `Φ` is a continuous linear map. -/
private theorem complexTorus_pushforward_contMDiff_engine {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) [DiscreteTopology ΛX] [IsZLattice ℝ ΛX]
    (ΛY : Submodule ℤ (Fin gY → ℂ)) [DiscreteTopology ΛY] [IsZLattice ℝ ΛY]
    (Φ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    let fCT : Jacobians.AbelianVariety.ComplexTorus (Fin gX → ℂ) ΛX →
              Jacobians.AbelianVariety.ComplexTorus (Fin gY → ℂ) ΛY :=
      fun q => Vendor.Kirov.ZLatticeQuotient.pushforward ΛX ΛY Φ hΦ q
    ContMDiff 𝓘(ℂ, Fin gX → ℂ) 𝓘(ℂ, Fin gY → ℂ) ω fCT := by
  intro fCT qX
  let IX := 𝓘(ℂ, Fin gX → ℂ)
  let IY := 𝓘(ℂ, Fin gY → ℂ)
  set target_q : Jacobians.AbelianVariety.ComplexTorus (Fin gY → ℂ) ΛY :=
    fCT qX with htgt_def
  set x₀ := extChartAt IX qX qX
  set y₀ := extChartAt IY target_q target_q
  have hqX_src : qX ∈ (extChartAt IX qX).source := mem_extChartAt_source qX
  have hx₀_tgt : x₀ ∈ (extChartAt IX qX).target :=
    (extChartAt IX qX).map_source hqX_src
  have htgt_src : target_q ∈ (extChartAt IY target_q).source :=
    mem_extChartAt_source target_q
  have hy₀_tgt : y₀ ∈ (extChartAt IY target_q).target :=
    (extChartAt IY target_q).map_source htgt_src
  have hx₀_mk :
      (QuotientAddGroup.mk' ΛX.toAddSubgroup x₀ :
        Jacobians.AbelianVariety.ComplexTorus _ ΛX) = qX :=
    (Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
      (L := ΛX) qX
      ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
        (L := ΛX) qX).1 hx₀_tgt)).symm.trans
      ((extChartAt IX qX).left_inv hqX_src)
  have hy₀_mk :
      (QuotientAddGroup.mk' ΛY.toAddSubgroup y₀ :
        Jacobians.AbelianVariety.ComplexTorus _ ΛY) = target_q :=
    (Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
      (L := ΛY) target_q
      ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
        (L := ΛY) target_q).1 hy₀_tgt)).symm.trans
      ((extChartAt IY target_q).left_inv htgt_src)
  have hfwd :
      target_q = (QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x₀) :
        Jacobians.AbelianVariety.ComplexTorus _ ΛY) := by
    rw [htgt_def, ← hx₀_mk]; rfl
  set c₀ := y₀ - Φ x₀
  have hc₀_mem : c₀ ∈ ΛY.toAddSubgroup := by
    have hmk_eq :
        (QuotientAddGroup.mk' ΛY.toAddSubgroup y₀ :
          Jacobians.AbelianVariety.ComplexTorus _ ΛY) =
        QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x₀) := by
      rw [hy₀_mk, hfwd]
    rw [QuotientAddGroup.mk'_eq_mk'] at hmk_eq
    obtain ⟨z, hz_mem, hz_eq⟩ := hmk_eq
    have hc₀z : c₀ = -z := by
      change y₀ - Φ x₀ = -z
      have : y₀ = Φ x₀ + (-z) := by rw [← hz_eq]; abel
      rw [this]; abel
    rw [hc₀z]; exact AddSubgroup.neg_mem _ hz_mem
  have hshift : ∀ x : Fin gX → ℂ,
      (QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x + c₀) :
        Jacobians.AbelianVariety.ComplexTorus _ ΛY) =
      QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x) := by
    intro x
    apply Quotient.sound'
    rw [QuotientAddGroup.leftRel_apply]
    have : -(Φ x + c₀) + Φ x = -c₀ := by abel
    rw [this]; exact AddSubgroup.neg_mem _ hc₀_mem
  have hy₀_eq : y₀ = Φ x₀ + c₀ := by
    change y₀ = Φ x₀ + (y₀ - Φ x₀); abel
  have hopen_tgt :
      IsOpen ((fun x => Φ x + c₀) ⁻¹' (extChartAt IY target_q).target) :=
    (Φ.continuous.add continuous_const).isOpen_preimage _
      (isOpen_extChartAt_target _)
  have hmem_tgt :
      x₀ ∈ (fun x => Φ x + c₀) ⁻¹' (extChartAt IY target_q).target := by
    simp only [Set.mem_preimage]; rw [← hy₀_eq]; exact hy₀_tgt
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_quot_lift _
      (QuotientAddGroup.continuous_mk.comp Φ.continuous)).continuousAt
  · simp only [modelWithCornersSelf_coe, Set.range_id]
    rw [contDiffWithinAt_univ]
    have hsmooth : ContDiffAt ℂ ω (fun x => Φ x + c₀) x₀ :=
      Φ.contDiff.contDiffAt.add contDiffAt_const
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target (I := IX) qX).mem_nhds
        hx₀_tgt,
      hopen_tgt.mem_nhds hmem_tgt] with x hx_src hx_tgt
    have hsymm_x :
        (extChartAt IX qX).symm x =
          (QuotientAddGroup.mk' ΛX.toAddSubgroup x :
            Jacobians.AbelianVariety.ComplexTorus _ ΛX) :=
      Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
        (L := ΛX) qX
        ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
          (L := ΛX) qX).1 hx_src)
    have hsymm_y :
        (extChartAt IY target_q).symm (Φ x + c₀) =
          (QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x + c₀) :
            Jacobians.AbelianVariety.ComplexTorus _ ΛY) :=
      Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
        (L := ΛY) target_q
        ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
          (L := ΛY) target_q).1 hx_tgt)
    have hmk_fCT :
        fCT ((extChartAt IX qX).symm x) =
          (QuotientAddGroup.mk' ΛY.toAddSubgroup (Φ x) :
            Jacobians.AbelianVariety.ComplexTorus _ ΛY) := by
      rw [hsymm_x]; rfl
    have hmk_eq :
        fCT ((extChartAt IX qX).symm x) =
          (extChartAt IY target_q).symm (Φ x + c₀) := by
      rw [hmk_fCT, hsymm_y, hshift]
    change (extChartAt IY target_q)
        (fCT ((extChartAt IX qX).symm x)) = Φ x + c₀
    rw [hmk_eq]
    exact (extChartAt IY target_q).right_inv hx_tgt

/-- Pushforward on Jacobians is smooth.

Proved by composing `complexTorus_pushforward_contMDiff_engine`
(the engine for complex-torus quotient maps using `ComplexTorus.instChartedSpace`)
with the ULift transfer lemmas `contMDiff_ulift_up` / `contMDiff_ulift_down`,
after showing that `pushforwardImpl` equals the Kirov pushforward up to `ULift`
wrapping. -/
theorem AX_pushforward_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforwardImpl X Y f hf) := by
  set ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  set ΛY := periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)
  set Φ : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus Y) → ℂ) :=
    LinearMap.toContinuousLinearMap (pushforwardAmbientLinear f hf)
  have hsub : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom := by
    intro v hv
    exact AX_pushforwardAmbient_preserves_lattice f hf v hv
  have hpush := complexTorus_pushforward_contMDiff_engine ΛX ΛY Φ hsub
  -- Define the function with types matching JacobianAmbient
  set fCT : JacobianAmbient X → JacobianAmbient Y := fun q =>
    Vendor.Kirov.ZLatticeQuotient.pushforward ΛX ΛY Φ hsub q
  have hbridge :
      ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω
        (fun z : Jacobian X => (ULift.up (fCT z.down) : Jacobian Y)) :=
    Jacobians.Jacobian.contMDiff_ulift_up.comp
      (hpush.comp Jacobians.Jacobian.contMDiff_ulift_down)
  -- Show pushforwardImpl equals the ULift-wrapped fCT
  -- Show pushforwardImpl equals the ULift-wrapped fCT
  have h : ∀ z : Jacobian X,
      pushforwardImpl X Y f hf z = (ULift.up (fCT z.down) : Jacobian Y) := by
    intro ⟨w⟩
    apply ULift.ext
    refine QuotientAddGroup.induction_on w (fun v => ?_)
    change (QuotientAddGroup.map ΛX.toAddSubgroup ΛY.toAddSubgroup
        (pushforwardAmbientLinear f hf).toAddMonoidHom
        (AX_pushforwardAmbient_preserves_lattice f hf))
      (QuotientAddGroup.mk v) =
      (QuotientAddGroup.map ΛX.toAddSubgroup ΛY.toAddSubgroup
        Φ.toAddMonoidHom hsub)
      (QuotientAddGroup.mk v)
    simp [Φ]
  exact hbridge.congr (fun z => (h z).symm)

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

/-- Pullback on Jacobians is smooth.

Symmetric to `AX_pushforward_contMDiff`: `pullbackImpl` is
`jacobianHomOfAmbient Y X (pullbackAmbientLinear f hf) ...`, which has the
same `QuotientAddGroup.map` shape as `Kirov.pushforward` with
`Φ := pullbackAmbientLinear f hf`. -/
theorem AX_pullback_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullbackImpl X Y f hf) := by
  set ΛX := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)
  set ΛY := periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)
  set Φ : (Fin (genus Y) → ℂ) →L[ℂ] (Fin (genus X) → ℂ) :=
    LinearMap.toContinuousLinearMap (pullbackAmbientLinear f hf)
  have hsub : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Φ.toAddMonoidHom := by
    intro v hv
    exact AX_pullbackAmbient_preserves_lattice f hf v hv
  have hpush := complexTorus_pushforward_contMDiff_engine ΛY ΛX Φ hsub
  set fCT : JacobianAmbient Y → JacobianAmbient X := fun q =>
    Vendor.Kirov.ZLatticeQuotient.pushforward ΛY ΛX Φ hsub q
  have hbridge :
      ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
        (fun z : Jacobian Y => (ULift.up (fCT z.down) : Jacobian X)) :=
    Jacobians.Jacobian.contMDiff_ulift_up.comp
      (hpush.comp Jacobians.Jacobian.contMDiff_ulift_down)
  -- Show pullbackImpl equals the ULift-wrapped fCT
  have h : ∀ z : Jacobian Y,
      pullbackImpl X Y f hf z = (ULift.up (fCT z.down) : Jacobian X) := by
    intro ⟨w⟩
    apply ULift.ext
    refine QuotientAddGroup.induction_on w (fun v => ?_)
    change (QuotientAddGroup.map ΛY.toAddSubgroup ΛX.toAddSubgroup
        (pullbackAmbientLinear f hf).toAddMonoidHom
        (AX_pullbackAmbient_preserves_lattice f hf))
      (QuotientAddGroup.mk v) =
      (QuotientAddGroup.map ΛY.toAddSubgroup ΛX.toAddSubgroup
        Φ.toAddMonoidHom hsub)
      (QuotientAddGroup.mk v)
    simp [Φ]
  exact hbridge.congr (fun z => (h z).symm)

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
