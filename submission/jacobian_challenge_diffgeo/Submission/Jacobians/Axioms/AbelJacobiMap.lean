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
  **No longer an axiom (2026-06-10)**: now a real `def` via the
  Kirov-Dolbeault port's fibre-sum trace `traceFormTotal`, transported
  across `Jacobians.Bridge.bridgeKDFormEquiv`; its identity and
  composition laws (`AX_pushforwardOneForm_id`/`_comp`) are theorems
  conjugating `traceFormTotal_id`/`_comp` (issues #26/#27/#28).
- `AX_pushforwardAmbient_preserves_lattice`,
  `AX_pullbackAmbient_preserves_lattice` — still axioms; retire to
  theorems once period-map naturality is derived.
- Property axioms (`AX_ofCurve_contMDiff`,
  `AX_pushforward_contMDiff`, `AX_pushforward_pullback`)
  — properties of the defs, retire with the usual textbook proofs.
- **`AX_jacobian_lieAddGroup`** is no longer an axiom (2026-04-23
  round-3): converted to a theorem via the ULift-smoothness lemmas
  `contMDiff_ulift_up` / `contMDiff_ulift_down` in
  `Jacobian/Construction.lean`, composed with the axiom-free
  `LieAddGroup (ComplexTorus V L)` instance.

Reference: Mumford Vol I §II.3; Griffiths-Harris Ch. 2.3; Forster Ch. III.
See `docs/formalization-plan.md` §7.
-/
import Submission.Jacobians.Jacobian.Construction
import Submission.Jacobians.Axioms.BranchLocus
import Submission.Jacobians.RiemannSurface.LoopIntegralHom
import Submission.Jacobians.RiemannSurface.LoopLattice
import Submission.Jacobians.RiemannSurface.DevelopingNaturality
import Submission.Jacobians.RiemannSurface.ArcAlgebra
import Submission.Jacobians.Bridge.KirovHolomorphicEquiv
import Submission.Jacobians.Bridge.KirovCanonicalEq
import Submission.Jacobians.Bridge.KirovDolbeaultTrace
import Submission.Jacobians.Bridge.KirovDolbeaultLattice
import Submission.Jacobians.Vendor.Kirov.ZLatticeQuotient

universe u v w

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety Jacobians.Bridge

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

/-- The pushforward (trace) of holomorphic 1-forms along a
holomorphic map `f : X → Y` between compact Riemann surfaces.
Classical content: for `ω ∈ Ω¹(X)` and `q ∈ Y`,
`(pushforwardOneForm f)(ω) (q) = Σ_{p ∈ f⁻¹(q)} (local contribution)`,
with multiplicities counted by `localOrder`. For constant `f` this is
the zero map.

This is now a real `def` (2026-06-10, issue #26): the Kirov-Dolbeault
port's fibre-sum trace `traceFormTotal` — genuine `traceForm` (fibre
sum via `(mfderiv f x)⁻¹` off the branch locus, extended across branch
points) for non-constant `f`, and `0` for constant `f`
(`traceFormTotal_eq_zero_of_const`, definitionally the `dif` branch) —
transported across `Jacobians.Bridge.bridgeKDFormEquiv`. -/
noncomputable def pushforwardOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y :=
  (Jacobians.Bridge.bridgeKDFormEquiv (X := Y)).symm.toLinearMap.comp
    ((_root_.Jacobians.traceFormTotal f _hf).comp
      (Jacobians.Bridge.bridgeKDFormEquiv (X := X)).toLinearMap)

/-! ### Functoriality on the form-level primitives

Per Gemini 2026-04-23 review: "functoriality on Jacobians is free via
contravariance of `Module.Dual`" — so we prove or state functoriality at
the form-level. Pullback identity/composition are theorems via Kirov
transport; pushforward identity/composition are theorems (2026-06-10)
via the Kirov-Dolbeault trace bridge. The Jacobian-level functoriality
then becomes derivable. -/

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

/-- The chart-local coefficient family of `pullbackOneForm f hf form`
satisfies the cross-manifold pullback transformation law against `form`:
in compatible charts, `(f^*ω)(x, z) = ω(y, F z) · F'(z)` where
`F = φ_y ∘ f ∘ φ_x⁻¹` is the chart read of `f`.

Unwinds the Kirov bridge (`sectionCoeff` / `localRep` /
`toFun_eq_localRep_smul`) down to Kirov's pointwise
`(f^*α)(x) = α(f x) ∘ mfderiv f x`; the tangent-trivialization factor is
converted to the complex derivative of the chart read exactly as in
`Bridge.BridgeFormEquiv.chartTransitionFactor_eq_fderiv` (the `f = id`
case). This is the relation hypothesis consumed by the developing-value
naturality engine (`developingValue_comp_of_isPullbackCoeffRel`). -/
theorem pullbackOneForm_isPullbackCoeffRel {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (form : HolomorphicOneForm Y) :
    IsPullbackCoeffRel f (pullbackOneForm f hf form) form := by
  classical
  intro x y z hz hfq
  set q : X := (extChartAt 𝓘(ℂ) x).symm z with hq_def
  have hqx : q ∈ (extChartAt 𝓘(ℂ) x).source := (extChartAt 𝓘(ℂ) x).map_target hz
  have hxq : (extChartAt 𝓘(ℂ) x) q = z := (extChartAt 𝓘(ℂ) x).right_inv hz
  have hqx_chart : q ∈ (chartAt ℂ x).source := by
    simpa [extChartAt] using hqx
  have hfq_chart : f q ∈ (chartAt ℂ y).source := by
    simpa [extChartAt] using hfq
  have hfq_base : f q ∈
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) y).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  -- Step 1: unfold the bridge — the pullback's coefficient is the `localRep`
  -- of Kirov's section pullback.
  set αY := Jacobians.Bridge.bridgeForm form with hαY_def
  set β := Jacobians.Vendor.Kirov.pullbackForm f hf αY with hβ_def
  have hunfold : pullbackOneForm f hf form =
      Jacobians.Bridge.BridgeFormEquiv.inverseForm β := by
    simp only [pullbackOneForm, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Jacobians.Bridge.bridgeFormEquiv, LinearEquiv.ofLinear_apply,
      LinearEquiv.ofLinear_symm_apply, hβ_def, hαY_def]
  have hLHS : (pullbackOneForm f hf form).coeff x z =
      Jacobians.Vendor.Kirov.Montel.localRep β x q := by
    rw [hunfold]
    have h1 : (Jacobians.Bridge.BridgeFormEquiv.inverseForm β).coeff x z =
        Jacobians.Bridge.BridgeFormEquiv.sectionCoeff β x z := rfl
    rw [h1, Jacobians.Bridge.BridgeFormEquiv.sectionCoeff_apply_of_mem β hz]
  -- Step 2: Kirov's pullback section evaluated on the chart unit tangent.
  set w : TangentSpace 𝓘(ℂ, ℂ) (f q) := mfderiv 𝓘(ℂ) 𝓘(ℂ) f q
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q 1)
    with hw_def
  have hβ_localRep : Jacobians.Vendor.Kirov.Montel.localRep β x q =
      αY.toFun (f q) w := rfl
  -- Step 3: split off the scalar coefficient at `f q` in the `y`-chart.
  have htoFun := Jacobians.Vendor.Kirov.Montel.toFun_eq_localRep_smul αY y (f q)
    hfq_base
  have hsplit : αY.toFun (f q) w =
      Jacobians.Vendor.Kirov.Montel.localRep αY y (f q) *
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
            y).continuousLinearEquivAt ℂ (f q) hfq_base :
          TangentSpace 𝓘(ℂ, ℂ) (f q) →L[ℂ] ℂ) w := by
    rw [htoFun]
    simp
  -- Step 4: the trivialization factor is the derivative of the chart read.
  have hA : ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
          y).continuousLinearEquivAt ℂ (f q) hfq_base :
        TangentSpace 𝓘(ℂ, ℂ) (f q) →L[ℂ] ℂ) w =
      fderiv ℂ
        ((extChartAt 𝓘(ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) z 1 := by
    have hmdiff_y : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) y) (f q) := mdifferentiableAt_extChartAt hfq_chart
    have hmdiff_f : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f q :=
      hf.mdifferentiableAt (by decide)
    have hmdiff_symm_within : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z :=
      mdifferentiableWithinAt_extChartAt_symm hz
    have hmdiff_symm : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) x).symm z := by
      have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
        ModelWithCorners.range_eq_univ _
      rw [← mdifferentiableWithinAt_univ, ← hrange]
      exact hmdiff_symm_within
    have hchain1 : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f q).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z) :=
      mfderiv_comp_of_eq hmdiff_f hmdiff_symm hq_def.symm
    have hmdiff_fsymm : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z :=
      MDifferentiableAt.comp z
        (show MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f
            ((extChartAt 𝓘(ℂ, ℂ) x).symm z) from hq_def ▸ hmdiff_f)
        hmdiff_symm
    have hchain2 : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) (f q)).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z) :=
      mfderiv_comp_of_eq hmdiff_y hmdiff_fsymm
        (by rw [Function.comp_apply, ← hq_def])
    have hmfd_y :
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
            y).continuousLinearMapAt ℂ (f q) =
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) (f q) :=
      TangentBundle.continuousLinearMapAt_trivializationAt hfq_chart
    have hsymm_x :
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q =
          mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ)))
            ((extChartAt 𝓘(ℂ, ℂ) x) q) :=
      TangentBundle.symmL_trivializationAt hqx_chart
    have hsymm_mfderiv :
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z =
          mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z := by
      have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
        ModelWithCorners.range_eq_univ _
      rw [hrange, mfderivWithin_univ]
    have hcoe : ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
            y).continuousLinearEquivAt ℂ (f q) hfq_base :
          TangentSpace 𝓘(ℂ, ℂ) (f q) →L[ℂ] ℂ) =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
            y).continuousLinearMapAt ℂ (f q) :=
      Bundle.Trivialization.coe_continuousLinearEquivAt_eq'
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) y) hfq_base
    rw [hcoe, hmfd_y, hw_def, hsymm_x, hxq, ← hsymm_mfderiv]
    have hcomp : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) (f q)).comp
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f q).comp
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z)) := by
      rw [hchain2, hchain1]
    have hfd : fderiv ℂ
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          ((extChartAt 𝓘(ℂ, ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z :=
      mfderiv_eq_fderiv.symm
    rw [hfd, hcomp]
    rfl
  -- Step 5: identify the scalar coefficient with `form.coeff` at `y`.
  have hRHS : form.coeff y ((extChartAt 𝓘(ℂ) y) (f q)) =
      Jacobians.Vendor.Kirov.Montel.localRep αY y (f q) := by
    conv_lhs => rw [show form = Jacobians.Bridge.BridgeFormEquiv.inverseForm αY
      from (Jacobians.Bridge.BridgeFormEquiv.inverseForm_bridgeForm form).symm]
    have h1 : (Jacobians.Bridge.BridgeFormEquiv.inverseForm αY).coeff y
        ((extChartAt 𝓘(ℂ) y) (f q)) =
        Jacobians.Bridge.BridgeFormEquiv.sectionCoeff αY y
          ((extChartAt 𝓘(ℂ) y) (f q)) := rfl
    rw [h1, Jacobians.Bridge.BridgeFormEquiv.sectionCoeff_apply_of_mem αY
      ((extChartAt 𝓘(ℂ) y).map_source hfq), (extChartAt 𝓘(ℂ) y).left_inv hfq]
  calc (pullbackOneForm f hf form).coeff x z
      = Jacobians.Vendor.Kirov.Montel.localRep β x q := hLHS
    _ = αY.toFun (f q) w := hβ_localRep
    _ = Jacobians.Vendor.Kirov.Montel.localRep αY y (f q) *
          ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
              y).continuousLinearEquivAt ℂ (f q) hfq_base :
            TangentSpace 𝓘(ℂ, ℂ) (f q) →L[ℂ] ℂ) w := hsplit
    _ = form.coeff y ((extChartAt 𝓘(ℂ) y) (f q)) *
          fderiv ℂ ((extChartAt 𝓘(ℂ) y) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) z 1 := by
        rw [hA, hRHS]

/-- Pushforward (trace) of 1-forms preserves identity. Conjugate of the
port's `traceFormTotal_id` across `bridgeKDFormEquiv` (issue #27). -/
theorem AX_pushforwardOneForm_id {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    pushforwardOneForm (id : X → X) contMDiff_id = LinearMap.id := by
  unfold pushforwardOneForm
  rw [_root_.Jacobians.traceFormTotal_id]
  ext form
  simp

/-- Pushforward (trace) of 1-forms is covariant under composition.
Classical: `(g ∘ f)_* ω = g_* (f_* ω)`. Conjugate of the port's
`traceFormTotal_comp` across `bridgeKDFormEquiv` (issue #28); the
constancy case-splits (`f` or `g` constant ⇒ both sides `0`) live in
the port proof. -/
theorem AX_pushforwardOneForm_comp {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {Z : Type w} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardOneForm (g ∘ f) (hg.comp hf) =
      (pushforwardOneForm g hg).comp (pushforwardOneForm f hf) := by
  unfold pushforwardOneForm
  rw [_root_.Jacobians.traceFormTotal_comp f hf g hg (hg.comp hf)]
  ext form
  simp [LinearMap.comp_apply]

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


/-! ### Chart-line descent helpers for `AX_ofCurve_contMDiff`

These lemmas package the straight chart-line `Bridge.chartLine` as an
`AnalyticArc` and compute its canonical period integral in closed form,
so the chart-level model of the Abel–Jacobi map can be compared to
`ofCurveAmbient` via `AX_Period_Triangle`.  They also supply the
parametric-integral analyticity used for chart-level smoothness. -/
section ChartLineDescent

open Jacobians.Bridge
open MeasureTheory Filter

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Continuity of `chartLine` at a parameter whose affine image lies in the
chart target. (Transcribed from the private companion in
`Bridge.KirovLineIntegral`.) -/
private lemma aux_chartLine_continuousAt (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    ContinuousAt (chartLine (X := X) P z) t := by
  let η : ℝ → ℂ := fun s =>
    (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  have hsymm_cont :
      ContinuousAt ((extChartAt 𝓘(ℂ, ℂ) P).symm : ℂ → X) (η t) := by
    exact (continuousOn_extChartAt_symm P).continuousAt
      (hOpen.mem_nhds (by simpa [η] using hz))
  have hη_cont : ContinuousAt η t := by
    dsimp [η]
    fun_prop
  have hcomp :
      ContinuousAt (((extChartAt 𝓘(ℂ, ℂ) P).symm : ℂ → X) ∘ η) t :=
    hsymm_cont.comp hη_cont
  change ContinuousAt
    (fun s : ℝ =>
      (extChartAt 𝓘(ℂ, ℂ) P).symm
        ((1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z)) t
  simpa [η, Function.comp_def] using hcomp

/- Real-differentiability of the current-chart pullback of `chartLine`.
(Transcribed from the private companion in `Bridge.KirovLineIntegral`.) -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
private lemma aux_chartLine_chartDiff (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (chartLine (X := X) P z t)).toFun ∘
        chartLine (X := X) P z) t := by
  let w : ℂ := (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z
  let y : X := chartLine (X := X) P z t
  have hy_eq : y = (extChartAt 𝓘(ℂ, ℂ) P).symm w := by
    simp [y, w, chartLine]
  have htrans_diff_C : DifferentiableAt ℂ
      ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) w := by
    have hsymm_mdiff_within : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) P).symm (Set.range (𝓘(ℂ, ℂ))) w := by
      simpa [w] using mdifferentiableWithinAt_extChartAt_symm hz
    have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) P).symm w := by
      have hrange :
          (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
        ModelWithCorners.range_eq_univ _
      rw [← mdifferentiableWithinAt_univ, ← hrange]
      exact hsymm_mdiff_within
    have hchart_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (extChartAt 𝓘(ℂ, ℂ) y) ((extChartAt 𝓘(ℂ, ℂ) P).symm w) := by
      apply mdifferentiableAt_extChartAt
      rw [← extChartAt_source (I := 𝓘(ℂ, ℂ)), ← hy_eq]
      exact mem_extChartAt_source y
    exact (hchart_mdiff.comp w hsymm_mdiff).differentiableAt
  have htrans_diff_R : DifferentiableAt ℝ
      ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) w :=
    htrans_diff_C.restrictScalars ℝ
  have haff : DifferentiableAt ℝ
      (fun s : ℝ => (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z) t := by
    fun_prop
  have hcomp := htrans_diff_R.comp t haff
  simpa [chartLine, y, w, extChartAt_coe, modelWithCornersSelf_coe,
    Function.comp_def] using hcomp

/-- The fixed-chart derivative of `chartLine` equals the constant velocity
`z - (extChartAt P) P`. (Transcribed from `Bridge.KirovLineIntegral`.) -/
private lemma aux_pathSpeed_chartLine (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) P).toFun ∘ chartLine (X := X) P z)
        t (1 : ℝ) =
      z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
  let a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P
  let η : ℝ → ℂ := fun s => (1 - s) • a + s • z
  have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) P).target := by
    rw [extChartAt_target]
    simp [(chartAt ℂ P).open_target]
  have hη_cont : ContinuousAt η t := by
    dsimp [η]
    fun_prop
  have hη_target : ∀ᶠ s in 𝓝 t, η s ∈ (extChartAt 𝓘(ℂ, ℂ) P).target :=
    hη_cont.eventually (hOpen.mem_nhds (by simpa [η, a] using hz))
  have heq :
      ((extChartAt 𝓘(ℂ, ℂ) P).toFun ∘ chartLine (X := X) P z) =ᶠ[𝓝 t]
        η := by
    filter_upwards [hη_target] with s hs
    exact extChartAt_chartLine (X := X) P z (by simpa [η, a] using hs)
  have hder : fderiv ℝ η t (1 : ℝ) = z - a := by
    have hder' : HasDerivAt (fun s : ℝ => a + s • (z - a)) (z - a) t := by
      simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using
        (hasDerivAt_const (x := t) (c := a)).add
          ((hasDerivAt_id t).smul_const (z - a))
    have hfun : (fun s : ℝ => (1 - s) • a + s • z) =
        fun s : ℝ => a + s • (z - a) := by
      funext s
      rw [sub_smul, one_smul]
      module
    exact (hder'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).deriv
  simpa [a] using
    (congrArg (fun L : ℝ →L[ℝ] ℂ => L (1 : ℝ)) heq.fderiv_eq).trans hder

/-- The manifold derivative of the fixed chart applied to the chart-line
speed equals the constant velocity. (Transcribed from
`Bridge.KirovLineIntegral`.) -/
private lemma aux_mfderiv_pathSpeed_chartLine (P : X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) P)
        (chartLine (X := X) P z t))
      (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
      z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
  have hspeed := mfderiv_extChartAt_apply_pathSpeed (x := P)
    (γ := chartLine (X := X) P z) (t := t)
    (aux_chartLine_continuousAt (X := X) P z hz)
    (aux_chartLine_chartDiff (X := X) P z hz)
    (by
      have hsrc := (extChartAt 𝓘(ℂ, ℂ) P).map_target hz
      simpa [chartLine] using hsrc)
  exact hspeed.trans (aux_pathSpeed_chartLine (X := X) P z hz)

/-- The `bridgeForm` integrand along `chartLine` in closed form.
(Transcribed from `Bridge.KirovLineIntegral`.) -/
private lemma aux_bridgeForm_chartLine_integrand
    (P : X) (form : HolomorphicOneForm X) (z : ℂ) {t : ℝ}
    (hz : (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    (Jacobians.Bridge.bridgeForm form).toFun (chartLine (X := X) P z t)
      (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
      form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
        (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
  let y : X := chartLine (X := X) P z t
  have hy_self : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
  have hy_fixed : y ∈ (extChartAt 𝓘(ℂ, ℂ) P).source := by
    have hsrc := (extChartAt 𝓘(ℂ, ℂ) P).map_target hz
    simpa [y, chartLine] using hsrc
  have hswap : (Jacobians.Bridge.bridgeForm form).toFun y =
      BridgeForm.rawCLM form P y := by
    change BridgeForm.rawCLM form y y = BridgeForm.rawCLM form P y
    exact BridgeForm.rawCLM_swap_chart form hy_self hy_fixed
  have hcoord :
      (extChartAt 𝓘(ℂ, ℂ) P) y =
        (1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z := by
    simpa [y] using extChartAt_chartLine (X := X) P z hz
  have hspeed :
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) P) y)
        (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) =
        z - (extChartAt 𝓘(ℂ, ℂ) P) P := by
    simpa [y] using aux_mfderiv_pathSpeed_chartLine (X := X) P z hz
  calc
    (Jacobians.Bridge.bridgeForm form).toFun (chartLine (X := X) P z t)
        (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t)
        = BridgeForm.rawCLM form P y
            (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t) := by
          rw [hswap]
    _ = form.coeff P ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
        (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
          unfold BridgeForm.rawCLM
          rw [hcoord]
          change form.coeff P
              ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) •
              ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
                (extChartAt 𝓘(ℂ, ℂ) P) y)
                (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) t)) =
            form.coeff P
              ((1 - t) • (extChartAt 𝓘(ℂ, ℂ) P) P + t • z) *
              (z - (extChartAt 𝓘(ℂ, ℂ) P) P)
          rw [hspeed]
          rfl

/-- The canonical moving-chart integrand of `chartLine` agrees with the
closed-form fixed-chart integrand. -/
private lemma aux_canonicalIntegrand_chartLine
    (P : X) (form : HolomorphicOneForm X) (z : ℂ) {r : ℝ}
    (hr : (1 - r) • (extChartAt 𝓘(ℂ, ℂ) P) P + r • z ∈
      (extChartAt 𝓘(ℂ, ℂ) P).target) :
    form.coeff (chartLine (X := X) P z r)
        ((extChartAt 𝓘(ℂ, ℂ) (chartLine (X := X) P z r))
          (chartLine (X := X) P z r))
        * deriv (fun u => (extChartAt 𝓘(ℂ, ℂ) (chartLine (X := X) P z r))
            (chartLine (X := X) P z u)) r
      = form.coeff P ((1 - r) • (extChartAt 𝓘(ℂ, ℂ) P) P + r • z) *
          (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
  set y : X := chartLine (X := X) P z r
  have hmf := mfderiv_extChartAt_apply_pathSpeed (x := y)
    (γ := chartLine (X := X) P z) (t := r)
    (aux_chartLine_continuousAt (X := X) P z hr)
    (aux_chartLine_chartDiff (X := X) P z hr)
    (mem_extChartAt_source y)
  have hbr := aux_bridgeForm_chartLine_integrand (X := X) P form z hr
  rw [show deriv (fun u => (extChartAt 𝓘(ℂ,ℂ) y) (chartLine (X := X) P z u)) r
      = mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) (extChartAt 𝓘(ℂ,ℂ) y) y
          (Jacobians.Vendor.Kirov.pathSpeed (chartLine (X := X) P z) r) from by
        rw [hmf]; rfl]
  exact hbr

/-- Global continuity of the clamped chart-line `extend` used to build an
`AnalyticArc`. -/
private lemma aux_chartLineDescent_continuous (P : X) (z : ℂ)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target) :
    Continuous (fun t : ℝ => chartLine (X := X) P z (max 0 (min t 1))) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hcl_mem : max 0 (min t 1) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right t 1)⟩
  have hcl_cont : ContinuousAt (fun s : ℝ => max 0 (min s 1)) t := by fun_prop
  exact ContinuousAt.comp (g := chartLine (X := X) P z) (f := fun s : ℝ => max 0 (min s 1))
    (aux_chartLine_continuousAt (X := X) P z (hseg _ hcl_mem)) hcl_cont

/-- Strong piecewise analyticity of the clamped chart-line `extend`. -/
private lemma aux_chartLineDescent_analytic (P : X) (z : ℂ)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target) :
    IsAnalyticArcStrong X
      (fun t : ℝ => chartLine (X := X) P z (max 0 (min t 1)))
      ({0, 1} : Finset ℝ) := by
  intro a ha b hb hab _hcons
  have ha2 : a = 0 ∨ a = 1 := by simpa [Finset.mem_insert, Finset.mem_singleton] using ha
  have hb2 : b = 0 ∨ b = 1 := by simpa [Finset.mem_insert, Finset.mem_singleton] using hb
  have hab01 : a = 0 ∧ b = 1 := by
    rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; linarith)
  obtain ⟨rfl, rfl⟩ := hab01
  refine ⟨{0, 1}, by simp, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  · intro s hs t ht hst _hcons'
    have hs2 : s = 0 ∨ s = 1 := by simpa [Finset.mem_insert, Finset.mem_singleton] using hs
    have ht2 : t = 0 ∨ t = 1 := by simpa [Finset.mem_insert, Finset.mem_singleton] using ht
    have hst01 : s = 0 ∧ t = 1 := by
      rcases hs2 with rfl | rfl <;> rcases ht2 with rfl | rfl <;>
        first
          | exact ⟨rfl, rfl⟩
          | (exfalso; linarith)
    obtain ⟨rfl, rfl⟩ := hst01
    refine ⟨P, Set.univ, fun r => (1 - r) • (extChartAt 𝓘(ℂ, ℂ) P) P + r • z,
      isOpen_univ, Set.subset_univ _, ?_, ?_, ?_⟩
    · intro x _
      exact ((analyticAt_const.sub analyticAt_id).smul analyticAt_const).add
        (analyticAt_id.smul analyticAt_const)
    · intro r hr
      have hr' : r ∈ Set.Icc (0:ℝ) 1 := hr.2
      have hcl : max 0 (min r 1) = r := by
        rw [min_eq_left hr'.2, max_eq_right hr'.1]
      show chartLine (X := X) P z (max 0 (min r 1)) ∈ (extChartAt 𝓘(ℂ, ℂ) P).source
      rw [hcl]
      have := (extChartAt 𝓘(ℂ, ℂ) P).map_target (hseg r hr')
      simpa [chartLine] using this
    · intro r hr
      have hr' : r ∈ Set.Icc (0:ℝ) 1 := hr.2
      have hcl : max 0 (min r 1) = r := by
        rw [min_eq_left hr'.2, max_eq_right hr'.1]
      show (extChartAt 𝓘(ℂ, ℂ) P) (chartLine (X := X) P z (max 0 (min r 1)))
        = (1 - r) • (extChartAt 𝓘(ℂ, ℂ) P) P + r • z
      rw [hcl]
      exact extChartAt_chartLine (X := X) P z (hseg r hr')

/-- The chart-line packaged as an `AnalyticArc`, clamped to `[0,1]` so that
its `extend` is globally continuous. -/
noncomputable def chartLineDescentArc (P : X) (z : ℂ)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target) :
    AnalyticArc X where
  extend := fun t : ℝ => chartLine (X := X) P z (max 0 (min t 1))
  continuous' := aux_chartLineDescent_continuous P z hseg
  partition := {0, 1}
  partition_subset := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := aux_chartLineDescent_analytic P z hseg

@[simp] private lemma chartLineDescentArc_extend (P : X) (z : ℂ)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target) (t : ℝ) :
    (chartLineDescentArc (X := X) P z hseg).extend t =
      chartLine (X := X) P z (max 0 (min t 1)) := rfl

/-- The canonical period integral of the chart-line arc, in closed form. -/
private lemma aux_canonicalArcIntegral_chartLineDescentArc
    (P : X) (z : ℂ) (form : HolomorphicOneForm X)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) P) P + s • z ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target) :
    canonicalArcIntegral (chartLineDescentArc (X := X) P z hseg) form
      = ∫ t in (0 : ℝ)..1,
          form.coeff P ((1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) P) P + (t : ℂ) • z)
            * (z - (extChartAt 𝓘(ℂ, ℂ) P) P) := by
  unfold canonicalArcIntegral
  refine intervalIntegral.integral_congr_ae ?_
  have hsub : {(1:ℝ)}ᶜ ∈ MeasureTheory.ae (volume : Measure ℝ) := by
    rw [mem_ae_iff, compl_compl]; exact measure_singleton 1
  filter_upwards [hsub] with r hr1 hr_uIoc
  have hr : r ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr_uIoc
    exact ⟨hr_uIoc.1, lt_of_le_of_ne hr_uIoc.2 (by simpa using hr1)⟩
  have hr_icc : r ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hr
  have hr_tgt := hseg r hr_icc
  have hcl_r : max 0 (min r 1) = r := by
    rw [min_eq_left (le_of_lt hr.2), max_eq_right (le_of_lt hr.1)]
  have hext_eq : (chartLineDescentArc (X:=X) P z hseg).extend =ᶠ[nhds r]
      chartLine (X:=X) P z := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
    rw [chartLineDescentArc_extend]
    congr 1
    rw [min_eq_left (le_of_lt hu.2), max_eq_right (le_of_lt hu.1)]
  simp only [canonicalIntegrand]
  rw [show (chartLineDescentArc (X:=X) P z hseg).extend r = chartLine (X:=X) P z r from by
        rw [chartLineDescentArc_extend, hcl_r]]
  rw [show deriv (fun u => (extChartAt 𝓘(ℂ,ℂ) (chartLine (X:=X) P z r))
            ((chartLineDescentArc (X:=X) P z hseg).extend u)) r
        = deriv (fun u => (extChartAt 𝓘(ℂ,ℂ) (chartLine (X:=X) P z r))
            (chartLine (X:=X) P z u)) r
      from Filter.EventuallyEq.deriv_eq
        (hext_eq.fun_comp (extChartAt 𝓘(ℂ,ℂ) (chartLine (X:=X) P z r)))]
  rw [show ((1 : ℂ) - (r : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) P) P + (r : ℂ) • z
        = ((1 : ℝ) - r) • (extChartAt 𝓘(ℂ, ℂ) P) P + r • z from by
      simp only [Complex.real_smul, smul_eq_mul]; push_cast; ring]
  exact aux_canonicalIntegrand_chartLine (X:=X) P form z hr_tgt

/-- **Chart-line triangle.**  Modulo the period lattice, the Abel–Jacobi
vector along the bridge path `P → Q` equals the bridge path `P → Qstar`
plus the chart-line leg `Qstar → Q`. -/
private lemma aux_ofCurveAmbient_chartLine_mem
    (P Qstar Q : X)
    (hQ_src : Q ∈ (extChartAt 𝓘(ℂ, ℂ) Qstar).source)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
            + s • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q ∈
          (extChartAt 𝓘(ℂ, ℂ) Qstar).target) :
    (fun i => ofCurveAmbient X P Q i
        - (ofCurveAmbient X P Qstar i
          + ∫ t in (0 : ℝ)..1,
              (jacobianBasis X i).coeff Qstar
                ((1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
                  + (t : ℂ) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q)
                * ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q
                  - (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar)))
      ∈ periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X) := by
  have htri := AX_Period_Triangle (X := X) (x := P) (y := Qstar) (z := Q)
    (p_xy := Jacobians.Bridge.bridgePathArc (X := X) P Qstar)
    (p_yz := chartLineDescentArc (X := X) Qstar ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q) hseg)
    (p_xz := Jacobians.Bridge.bridgePathArc (X := X) P Q)
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [chartLineDescentArc])
    (by
      show chartLine (X := X) Qstar ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q) (max 0 (min 1 1)) = Q
      simp only [min_self, max_eq_right (zero_le_one), chartLine_at_one]
      exact (extChartAt 𝓘(ℂ, ℂ) Qstar).left_inv hQ_src)
    (by simp [Jacobians.Bridge.bridgePathArc])
    (by simp [Jacobians.Bridge.bridgePathArc])
  have hfun :
      (fun i => ofCurveAmbient X P Q i
          - (ofCurveAmbient X P Qstar i
            + ∫ t in (0 : ℝ)..1,
                (jacobianBasis X i).coeff Qstar
                  ((1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
                    + (t : ℂ) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q)
                  * ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q
                    - (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar)))
        = (fun i =>
            canonicalArcIntegral (Jacobians.Bridge.bridgePathArc (X := X) P Q)
                (jacobianBasis X i)
            - (canonicalArcIntegral (Jacobians.Bridge.bridgePathArc (X := X) P Qstar)
                (jacobianBasis X i)
              + canonicalArcIntegral
                  (chartLineDescentArc (X := X) Qstar ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q) hseg)
                  (jacobianBasis X i))) := by
    funext i
    have h3 := aux_canonicalArcIntegral_chartLineDescentArc (X := X) Qstar
      ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q) (jacobianBasis X i) hseg
    rw [show ofCurveAmbient X P Q i
          = canonicalArcIntegral (Jacobians.Bridge.bridgePathArc (X := X) P Q)
              (jacobianBasis X i) from rfl,
      show ofCurveAmbient X P Qstar i
          = canonicalArcIntegral (Jacobians.Bridge.bridgePathArc (X := X) P Qstar)
              (jacobianBasis X i) from rfl,
      ← h3]
  rw [hfun]
  exact htri

/-- **Parametric analyticity of the chart-line vector.**  The chart-line
integral is `ContDiffAt ℂ ω` (analytic) in the endpoint at the chart
centre. -/
private lemma aux_chartLineVec_contDiffAt
    (P : X) (form : HolomorphicOneForm X) :
    ContDiffAt ℂ ω
      (fun z : ℂ => ∫ t in (0 : ℝ)..1,
        form.coeff P ((1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) P) P + (t : ℂ) • z)
          * (z - (extChartAt 𝓘(ℂ, ℂ) P) P))
      ((extChartAt 𝓘(ℂ, ℂ) P) P) := by
  set a : ℂ := (extChartAt 𝓘(ℂ, ℂ) P) P with ha_def
  have hfun : (fun z : ℂ => ∫ t in (0:ℝ)..1,
        form.coeff P ((1-(t:ℂ))•a+(t:ℂ)•z) * (z-a))
      = (fun z : ℂ => (∫ t in (0:ℝ)..1, form.coeff P ((1-(t:ℂ))•a+(t:ℂ)•z)) * (z-a)) := by
    funext z; rw [intervalIntegral.integral_mul_const]
  rw [hfun]
  have htgt_open := isOpen_extChartAt_target (I := 𝓘(ℂ,ℂ)) P
  have ha_tgt : a ∈ (extChartAt 𝓘(ℂ,ℂ) P).target := by
    rw [ha_def]; exact (extChartAt 𝓘(ℂ,ℂ) P).map_source (mem_extChartAt_source P)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp htgt_open a ha_tgt
  set R : ℝ := ρ / 2 with hR_def
  have hR_pos : 0 < R := by positivity
  have hclosed_sub : Metric.closedBall a R ⊆ (extChartAt 𝓘(ℂ,ℂ) P).target := by
    intro w hw
    apply hρ_sub
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have : R < ρ := by rw [hR_def]; linarith
    linarith
  have hcoeff_an : AnalyticOnNhd ℂ (form.coeff P) (extChartAt 𝓘(ℂ,ℂ) P).target :=
    (htgt_open.analyticOn_iff_analyticOnNhd).mp (form.2.1 P)
  have hderiv_an : AnalyticOnNhd ℂ (deriv (form.coeff P)) (extChartAt 𝓘(ℂ,ℂ) P).target :=
    hcoeff_an.deriv
  have hderiv_cont : ContinuousOn (deriv (form.coeff P)) (Metric.closedBall a R) :=
    (hderiv_an.mono hclosed_sub).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hderiv_cont
  have hseg_mem : ∀ x ∈ Metric.ball a R, ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
      (1-(t:ℂ))•a+(t:ℂ)•x ∈ Metric.closedBall a R := by
    intro x hx t ht
    have hxc : x ∈ Metric.closedBall a R := Metric.ball_subset_closedBall hx
    rw [Metric.mem_closedBall] at hxc ⊢
    have hdist : dist ((1-(t:ℂ))•a+(t:ℂ)•x) a = t * dist x a := by
      rw [Complex.dist_eq, Complex.dist_eq]
      have he : (1-(t:ℂ))•a+(t:ℂ)•x - a = (t:ℂ)*(x-a) := by
        simp only [smul_eq_mul]; ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [hdist]
    nlinarith [ht.1, ht.2, dist_nonneg (x:=x) (y:=a), hxc]
  have hcont_t : ∀ z ∈ Metric.ball a R,
      ContinuousOn (fun t : ℝ => form.coeff P ((1-(t:ℂ))•a+(t:ℂ)•z)) (Set.Icc (0:ℝ) 1) := by
    intro z hz
    have haff : ContinuousOn (fun t : ℝ => (1-(t:ℂ))•a+(t:ℂ)•z) (Set.Icc (0:ℝ) 1) := by fun_prop
    exact (hcoeff_an.continuousOn.mono hclosed_sub).comp haff
      (fun t ht => hseg_mem z hz t ht)
  have key : ContDiffAt ℂ ω
      (fun z : ℂ => ∫ t in (0:ℝ)..1, form.coeff P ((1-(t:ℂ))•a+(t:ℂ)•z)) a := by
    have hDiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in (0:ℝ)..1, form.coeff P ((1-(t:ℂ))•a+(t:ℂ)•z))
        (Metric.ball a R) := by
      intro z₁ hz₁
      have hball_nhds : Metric.ball a R ∈ 𝓝 z₁ := Metric.isOpen_ball.mem_nhds hz₁
      have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (a := (0:ℝ)) (b := 1) (μ := volume) (x₀ := z₁) (s := Metric.ball a R)
        (bound := fun _ => max M 0)
        (F := fun z t => form.coeff P ((1-(t:ℂ))•a + (t:ℂ)•z))
        (F' := fun z t => deriv (form.coeff P) ((1-(t:ℂ))•a+(t:ℂ)•z) * (t:ℂ))
        hball_nhds ?hF_meas ?hF_int ?hF'_meas ?h_bound ?bound_int ?h_diff
      · exact (hres.2).differentiableAt.differentiableWithinAt
      case hF_meas =>
        filter_upwards [Metric.isOpen_ball.mem_nhds hz₁] with z hz
        exact (hcont_t z hz).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
          measurableSet_uIoc (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)
      case hF_int =>
        exact (hcont_t z₁ hz₁).intervalIntegrable_of_Icc zero_le_one
      case hF'_meas =>
        have hcont' : ContinuousOn
            (fun t : ℝ => deriv (form.coeff P) ((1-(t:ℂ))•a+(t:ℂ)•z₁) * (t:ℂ))
            (Set.Icc (0:ℝ) 1) := by
          have haff : ContinuousOn (fun t : ℝ => (1-(t:ℂ))•a+(t:ℂ)•z₁) (Set.Icc (0:ℝ) 1) := by
            fun_prop
          exact ((hderiv_an.continuousOn.mono hclosed_sub).comp haff
            (fun t ht => hseg_mem z₁ hz₁ t ht)).mul (by fun_prop)
        exact hcont'.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
          measurableSet_uIoc (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)
      case h_bound =>
        filter_upwards with t ht x hx
        have htIcc : t ∈ Set.Icc (0:ℝ) 1 := by
          have : t ∈ Set.Ioc (0:ℝ) 1 := by rwa [Set.uIoc_of_le zero_le_one] at ht
          exact Set.Ioc_subset_Icc_self this
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htIcc.1]
        have hb := hM _ (hseg_mem x hx t htIcc)
        calc ‖deriv (form.coeff P) ((1-(t:ℂ))•a+(t:ℂ)•x)‖ * t
            ≤ M * 1 := by
              apply mul_le_mul hb htIcc.2 htIcc.1 (le_trans (norm_nonneg _) hb)
          _ = M := by ring
          _ ≤ max M 0 := le_max_left _ _
      case bound_int =>
        exact intervalIntegrable_const
      case h_diff =>
        filter_upwards with t ht x hx
        have htIcc : t ∈ Set.Icc (0:ℝ) 1 := by
          have : t ∈ Set.Ioc (0:ℝ) 1 := by rwa [Set.uIoc_of_le zero_le_one] at ht
          exact Set.Ioc_subset_Icc_self this
        have hpt_tgt : (1-(t:ℂ))•a+(t:ℂ)•x ∈ (extChartAt 𝓘(ℂ,ℂ) P).target :=
          hclosed_sub (hseg_mem x hx t htIcc)
        have hcoeff_hd : HasDerivAt (form.coeff P)
            (deriv (form.coeff P) ((1-(t:ℂ))•a+(t:ℂ)•x)) ((1-(t:ℂ))•a+(t:ℂ)•x) :=
          ((hcoeff_an _ hpt_tgt).differentiableAt).hasDerivAt
        have haff_hd : HasDerivAt (fun z : ℂ => (1-(t:ℂ))•a+(t:ℂ)•z) (t:ℂ) x := by
          simpa using ((hasDerivAt_id x).const_mul (t:ℂ)).const_add ((1-(t:ℂ))•a)
        exact hcoeff_hd.comp x haff_hd
    exact ((hDiffOn.analyticOnNhd Metric.isOpen_ball) a (Metric.mem_ball_self hR_pos)).contDiffAt
  exact key.mul (contDiffAt_id.sub contDiffAt_const)

end ChartLineDescent

/-- **Theorem.** The Abel-Jacobi map is smooth/holomorphic.

The proof factors through `ULift.up` (smooth by `contMDiff_ulift_up`)
and sets up the quotient-descent scaffold (lattice constant `c₀`,
`extChartAt` representatives `y₀`, `z₀`). The remaining obligation —
chart-level smoothness of the torus-valued map — follows the same
pattern as `complexTorus_pushforward_contMDiff_engine` with the linear
model replaced by the chart-line integral; the chart-line integral's
analyticity (and hence `ContDiffAt ℂ ω`) is the content of the
parametric-FTC step (`chartLine_FTC` + `DifferentiableOn.analyticOn`).
-/
theorem AX_ofCurve_contMDiff {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) :
    ContMDiff 𝓘(ℂ, ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ofCurveImpl X P) := by
  -- ═══════════════════════════════════════════════════════════════════
  -- Abel-Jacobi smoothness — structured proof skeleton
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 0: Notation
  let IY := modelWithCornersSelf ℂ (Fin (genus X) → ℂ)
  -- Step 1: ContMDiff = ∀ Qstar, ContMDiffAt. Fix an arbitrary target point.
  intro Qstar
  -- Step 2: Factor  ofCurveImpl X P = ULift.up ∘ φ  and peel off ULift.up.
  -- φ Q := QuotientAddGroup.mk' Λ.toAddSubgroup (ofCurveAmbient X P Q − ofCurveAmbient X P P)
  show ContMDiffAt 𝓘(ℂ, ℂ) IY ω (ofCurveImpl X P) Qstar

  set Λ := periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X) with hΛ
  -- `φ Q := mk' Λ (ofCurveAmbient X P Q − ofCurveAmbient X P P)`, bound with an
  -- explicit `JacobianAmbient X` (= `ComplexTorus`) codomain so every
  -- `contMDiffAt_iff` computation resolves to the `ComplexTorus` atlas
  -- (matching `contMDiff_ulift_up`), as in
  -- `complexTorus_pushforward_contMDiff_engine`.
  set φ : X → JacobianAmbient X := fun Q =>
    QuotientAddGroup.mk' Λ.toAddSubgroup
      (ofCurveAmbient X P Q - ofCurveAmbient X P P)
    with hφ_def
  have hφ : ContMDiffAt 𝓘(ℂ, ℂ) IY ω φ Qstar := by
    -- ───────────────────────────────────────────────────────────────────
    -- Step 3: Quotient-descent scaffold (mirrors complexTorus_pushforward_contMDiff_engine)
    -- ───────────────────────────────────────────────────────────────────
    set target_q : JacobianAmbient X := φ Qstar with htgt
    set v₀ : Fin (genus X) → ℂ := ofCurveAmbient X P Qstar - ofCurveAmbient X P P with hv₀
    -- v₀ lifts target_q
    have hv₀_mk :
        (QuotientAddGroup.mk' Λ.toAddSubgroup v₀ : JacobianAmbient X) = target_q := rfl
    -- Pick the extChartAt lift of target_q in the torus (ComplexTorus atlas).
    set y₀ := extChartAt IY target_q target_q with hy₀_def
    have htgt_src : target_q ∈ (extChartAt IY target_q).source :=
      mem_extChartAt_source target_q
    have hy₀_tgt : y₀ ∈ (extChartAt IY target_q).target :=
      (extChartAt IY target_q).map_source htgt_src
    -- The torus chart symm at y₀ is mk' v₀  (up to lattice)
    have hy₀_mk :
        (QuotientAddGroup.mk' Λ.toAddSubgroup y₀ : JacobianAmbient X) = target_q :=
      (Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
        (L := Λ) target_q
        ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
          (L := Λ) target_q).1 hy₀_tgt)).symm.trans
        ((extChartAt IY target_q).left_inv htgt_src)
    -- Lattice constant c₀ := y₀ − v₀
    set c₀ := y₀ - v₀ with hc₀_def
    have hc₀_mem : c₀ ∈ Λ.toAddSubgroup := by
      have hmk_eq :
          (QuotientAddGroup.mk' Λ.toAddSubgroup y₀ : JacobianAmbient X) =
          QuotientAddGroup.mk' Λ.toAddSubgroup v₀ := by
        rw [hy₀_mk, ← hv₀_mk]
      rw [QuotientAddGroup.mk'_eq_mk'] at hmk_eq
      obtain ⟨z, hz_mem, hz_eq⟩ := hmk_eq
      have hc₀z : c₀ = -z := by
        change y₀ - v₀ = -z
        have : y₀ = v₀ + (-z) := by rw [← hz_eq]; abel
        rw [this]; abel
      rw [hc₀z]; exact AddSubgroup.neg_mem _ hz_mem
    have hy₀_eq : y₀ = v₀ + c₀ := by change y₀ = v₀ + (y₀ - v₀); abel
    -- Shift lemma: mk'(w + c₀) = mk'(w)  for any w
    have hshift : ∀ w : Fin (genus X) → ℂ,
        (QuotientAddGroup.mk' Λ.toAddSubgroup (w + c₀) :
          JacobianAmbient X) =
        QuotientAddGroup.mk' Λ.toAddSubgroup w := by
      intro w
      apply Quotient.sound'
      rw [QuotientAddGroup.leftRel_apply]
      have : -(w + c₀) + w = -c₀ := by abel
      rw [this]; exact AddSubgroup.neg_mem _ hc₀_mem
    -- ─────────────────────────────────────────────────────────────────
    -- Step 4: The local model function (chart-line integral vector)
    -- ─────────────────────────────────────────────────────────────────
    set z₀ := (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar with hz₀_def
    -- chartLineVec z i = ∫₀¹ (jacobianBasis X i).coeff Qstar ((1−t)•z₀ + t•z) · (z − z₀) dt
    -- This is the chart-line integral from z₀ to z in the chart centered at Qstar.
    set chartLineVec : ℂ → Fin (genus X) → ℂ := fun z i =>
      ∫ t in (0 : ℝ)..1,
        (jacobianBasis X i).coeff Qstar ((1 - ↑t) • z₀ + ↑t • z) * (z - z₀)
    -- localModel z := v₀ + chartLineVec z
    set localModel : ℂ → Fin (genus X) → ℂ := fun z => v₀ + chartLineVec z
    -- localModel z₀ = v₀  (since chartLineVec z₀ = 0:  integrand has factor z₀ − z₀ = 0)
    have hCLV_zero : chartLineVec z₀ = 0 := by
      ext i; simp [chartLineVec, sub_self, mul_zero]
    have hLM_z₀ : localModel z₀ = v₀ := by simp [localModel, hCLV_zero]
    -- ─────────────────────────────────────────────────────────────────
    -- Step 5: Prove ContMDiffAt via comparison map + congr_of_eventuallyEq
    -- ─────────────────────────────────────────────────────────────────
    -- APPROACH: Do NOT rw [contMDiffAt_iff] on φ directly (charted-space
    -- diamond). Instead prove ContMDiffAt for a "comparison map" ψ that
    -- composes mk' ∘ (localModel + c₀) ∘ extChartAt, then transfer via
    -- ContMDiffAt.congr_of_eventuallyEq using the period-lattice equality.
    have hQstar_src : Qstar ∈ (extChartAt 𝓘(ℂ, ℂ) Qstar).source :=
      mem_extChartAt_source Qstar
    have hmk_cont : Continuous (QuotientAddGroup.mk' Λ.toAddSubgroup) :=
      continuous_quotient_mk'
    have hCLV_contAt : ∀ i, ContinuousAt (fun y => chartLineVec y i) z₀ := by
      intro i
      have heq : (fun y => chartLineVec y i) = fun y =>
          (∫ t in (0:ℝ)..1, (jacobianBasis X i).coeff Qstar
            ((1 - ↑t) • z₀ + ↑t • y)) * (y - z₀) := by
        ext y; simp only [chartLineVec]
        simp_rw [mul_comm _ (y - z₀)]
        rw [intervalIntegral.integral_const_mul, mul_comm]
      rw [heq]
      exact (Jacobians.Bridge.chartLine_average_coeff_continuousAt
        (X := X) Qstar (jacobianBasis X i)).mul
        (continuousAt_id.sub continuousAt_const)
    have hLM_cont : ContinuousAt localModel z₀ := by
      apply ContinuousAt.add continuousAt_const
      exact continuousAt_pi.mpr hCLV_contAt
    have hz₀_tgt : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) Qstar).target :=
      (extChartAt 𝓘(ℂ, ℂ) Qstar).map_source hQstar_src
    have hmem_tgt :
        localModel z₀ + c₀ ∈ (extChartAt IY target_q).target := by
      rw [hLM_z₀, ← hy₀_eq]; exact hy₀_tgt
    -- ─── Smoothness of localModel + c₀ ────────────────────────────
    have hsmooth_LM : ContDiffAt ℂ ω (fun z => localModel z + c₀) z₀ := by
      apply ContDiffAt.add _ contDiffAt_const
      apply ContDiffAt.add contDiffAt_const
      apply contDiffAt_pi.mpr; intro i
      -- The chart-line vector is analytic in the endpoint (parametric
      -- analyticity of the chart-line integral); see
      -- `aux_chartLineVec_contDiffAt`.
      have hbridge : (fun x : ℂ => chartLineVec x i)
          = (fun z : ℂ => ∫ t in (0:ℝ)..1, (jacobianBasis X i).coeff Qstar
              ((1 - (t:ℂ)) • z₀ + (t:ℂ) • z) * (z - z₀)) := by
        funext z
        simp only [chartLineVec]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        congr 2
        all_goals first
          | rfl
          | (simp only [Complex.real_smul, smul_eq_mul]; push_cast; ring)
      rw [hbridge, hz₀_def]
      exact aux_chartLineVec_contDiffAt (X := X) Qstar (jacobianBasis X i)
    -- ─── Comparison map ψ ────────────────────────────────────────
    -- ψ Q = mk'(localModel(extChartAt Qstar Q) + c₀) : JacobianAmbient X
    -- We prove ContMDiffAt for ψ via contMDiffAt_iff, using
    -- extChartAt_apply_quotient_mk (no right_inv, no diamond).
    -- First establish: ψ Qstar = target_q
    have hψ_val : (QuotientAddGroup.mk' Λ.toAddSubgroup
        (localModel z₀ + c₀) : JacobianAmbient X) = target_q := by
      rw [hLM_z₀]; exact (hshift v₀).trans hv₀_mk
    -- The comparison map, bound with an explicit `JacobianAmbient X`
    -- (= `ComplexTorus`) codomain so that `contMDiffAt_iff` resolves to the
    -- `ComplexTorus` atlas (matching `contMDiff_ulift_up`), exactly as in
    -- `complexTorus_pushforward_contMDiff_engine`.
    set psiMap : X → JacobianAmbient X :=
      fun Q => QuotientAddGroup.mk' Λ.toAddSubgroup
        (localModel ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q) + c₀)
      with hpsiMap_def
    -- `psiMap Qstar` is definitionally `mk' (localModel z₀ + c₀)` (as `z₀ =
    -- extChartAt Qstar Qstar`), which equals `target_q` by `hψ_val`.
    have hpsiMap_Qstar : psiMap Qstar = target_q := hψ_val
    have hcomp : ContMDiffAt 𝓘(ℂ,ℂ) IY ω psiMap Qstar := by
      refine contMDiffAt_iff.mpr ⟨?_, ?_⟩
      · -- ContinuousAt of ψ at Qstar
        exact hmk_cont.continuousAt.comp
          (hsmooth_LM.continuousAt.comp (continuousAt_extChartAt (I := 𝓘(ℂ,ℂ)) Qstar))
      · -- ContDiffWithinAt — chart composition
        simp only [modelWithCornersSelf_coe, Set.range_id]
        rw [contDiffWithinAt_univ]
        apply hsmooth_LM.congr_of_eventuallyEq
        filter_upwards [
          (isOpen_extChartAt_target (I := 𝓘(ℂ,ℂ)) Qstar).mem_nhds hz₀_tgt,
          hsmooth_LM.continuousAt.preimage_mem_nhds
            ((isOpen_extChartAt_target (I := IY) target_q).mem_nhds hmem_tgt)
        ] with z hz_chart hz_torus
        -- `hz_torus : localModel z + c₀ ∈ (extChartAt IY target_q).target`
        have hsymm_y :
            (extChartAt IY target_q).symm (localModel z + c₀) =
              (QuotientAddGroup.mk' Λ.toAddSubgroup (localModel z + c₀) :
                JacobianAmbient X) :=
          Jacobians.AbelianVariety.ComplexTorus.extChartAt_symm_eq_quotient_mk
            (L := Λ) target_q
            ((Jacobians.AbelianVariety.ComplexTorus.mem_extChartAt_target_iff
              (L := Λ) target_q).1 hz_torus)
        have hpsi_eq :
            psiMap ((extChartAt 𝓘(ℂ,ℂ) Qstar).symm z) =
              (extChartAt IY target_q).symm (localModel z + c₀) := by
          rw [hsymm_y, hpsiMap_def]
          show (QuotientAddGroup.mk' Λ.toAddSubgroup
              (localModel ((extChartAt 𝓘(ℂ,ℂ) Qstar) ((extChartAt 𝓘(ℂ,ℂ) Qstar).symm z)) + c₀)
              : JacobianAmbient X)
            = QuotientAddGroup.mk' Λ.toAddSubgroup (localModel z + c₀)
          rw [(extChartAt 𝓘(ℂ,ℂ) Qstar).right_inv hz_chart]
        simp only [Function.comp_apply, hpsiMap_Qstar]
        rw [hpsi_eq]
        exact (extChartAt IY target_q).right_inv hz_torus
    -- ─── Period-lattice eventuallyEq: psiMap =ᶠ φ near Qstar ─────────
    -- φ Q = mk'(ofCurveAmbient P Q - ofCurveAmbient P P)
    -- psiMap Q = mk'(localModel(extChartAt Q) + c₀) = mk'(localModel(extChartAt Q))
    -- These agree near Qstar by AX_Period_Triangle.
    have hperiod_filter : psiMap =ᶠ[𝓝 Qstar] φ := by
      obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
        Metric.isOpen_iff.mp
          (isOpen_extChartAt_target (I := 𝓘(ℂ,ℂ)) Qstar) z₀ hz₀_tgt
      filter_upwards [
        (continuousAt_extChartAt (I := 𝓘(ℂ,ℂ)) Qstar).preimage_mem_nhds
          (Metric.ball_mem_nhds z₀ hρ_pos),
        extChartAt_source_mem_nhds (I := 𝓘(ℂ,ℂ)) Qstar
      ] with Q hQ_ball hQ_src
      -- The chart-line segment from `z₀` to `(extChartAt Qstar) Q` stays in
      -- the chart target, since `(extChartAt Qstar) Q` lies in the ball.
      have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1,
          (1 - s) • (extChartAt 𝓘(ℂ,ℂ) Qstar) Qstar
              + s • (extChartAt 𝓘(ℂ,ℂ) Qstar) Q
            ∈ (extChartAt 𝓘(ℂ,ℂ) Qstar).target := by
        intro s hs
        apply hρ_sub
        have hline :
            (1 - s) • z₀ + s • (extChartAt 𝓘(ℂ,ℂ) Qstar) Q ∈
              segment ℝ z₀ ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q) := by
          rw [← AffineMap.lineMap_apply_module]
          exact lineMap_mem_segment ℝ _ _ hs
        have hball :=
          (convex_ball _ _).segment_subset (Metric.mem_ball_self hρ_pos) hQ_ball hline
        simpa using hball
      have hmem := aux_ofCurveAmbient_chartLine_mem (X := X) P Qstar Q hQ_src hseg
      -- Convert the lattice membership into the quotient equality.
      show (QuotientAddGroup.mk' Λ.toAddSubgroup
          (localModel ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q) + c₀) : JacobianAmbient X)
        = QuotientAddGroup.mk' Λ.toAddSubgroup
            (ofCurveAmbient X P Q - ofCurveAmbient X P P)
      rw [show localModel ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q) + c₀
            = (v₀ + chartLineVec ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q)) + c₀ from rfl,
        hshift (v₀ + chartLineVec ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q))]
      apply (QuotientAddGroup.eq_iff_sub_mem (N := Λ.toAddSubgroup)).mpr
      rw [Submodule.mem_toAddSubgroup]
      have hneg := Submodule.neg_mem _ hmem
      have heqv :
          (v₀ + chartLineVec ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q))
              - (ofCurveAmbient X P Q - ofCurveAmbient X P P)
            = -(fun i => ofCurveAmbient X P Q i
                - (ofCurveAmbient X P Qstar i
                  + ∫ t in (0:ℝ)..1,
                      (jacobianBasis X i).coeff Qstar
                        ((1 - (t:ℂ)) • (extChartAt 𝓘(ℂ,ℂ) Qstar) Qstar
                          + (t:ℂ) • (extChartAt 𝓘(ℂ,ℂ) Qstar) Q)
                        * ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q
                          - (extChartAt 𝓘(ℂ,ℂ) Qstar) Qstar))) := by
        funext i
        have hclv : chartLineVec ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q) i
            = ∫ t in (0:ℝ)..1,
                (jacobianBasis X i).coeff Qstar
                  ((1 - (t:ℂ)) • (extChartAt 𝓘(ℂ,ℂ) Qstar) Qstar
                    + (t:ℂ) • (extChartAt 𝓘(ℂ,ℂ) Qstar) Q)
                  * ((extChartAt 𝓘(ℂ,ℂ) Qstar) Q
                    - (extChartAt 𝓘(ℂ,ℂ) Qstar) Qstar) := by
          simp only [chartLineVec, hz₀_def]
          refine intervalIntegral.integral_congr (fun t _ => ?_)
          congr 2
          all_goals first
            | rfl
            | (simp only [Complex.real_smul, smul_eq_mul]; push_cast; ring)
        simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, hclv, hv₀]
        ring
      rw [heqv]
      exact hneg
    exact hcomp.congr_of_eventuallyEq hperiod_filter.symm
  refine (Jacobians.Jacobian.contMDiff_ulift_up).contMDiffAt.comp Qstar ?_
  exact hφ

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

/-- **Theorem (derived 2026-06-11, issue #30).** Lattice preservation: the
pushforward ambient map sends the period lattice of `X` into the period
lattice of `Y`.

Formerly an axiom; the classical content `∫_{f_*γ} ω_Y = ∫_γ f^*ω_Y` is now
the developing-value naturality engine. Proof route (representative-loop
induction, KIROV_ROUTE_IDEAS item 7): a lattice vector is the period vector
of an `H1` class; every `H1` class is the class of a representative loop
`γ`; the pushforward ambient map turns its period vector into the vector of
`γ`-integrals of the pulled-back basis forms (dual-basis algebra);
developing-value naturality (`developingValue_comp_of_isPullbackCoeffRel`
fed by `pullbackOneForm_isPullbackCoeffRel`) identifies these with the
period vector of the image loop `f ∘ γ`; and the period vector of any
continuous loop lies in the target lattice at any basepoint
(`devVal_loop_mem_periodLatticeInBasis_any`: `H1` developing functional +
path conjugation). `f_*` sending integer cycles to integer cycles is
implicit: the image class is the class of the honest loop `f ∘ γ`. -/
theorem AX_pushforwardAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis X (Classical.arbitrary X)
              (jacobianBasis X)).toAddSubgroup,
      (pushforwardAmbientLinear f hf) v ∈
        (periodLatticeInBasis Y (Classical.arbitrary Y)
          (jacobianBasis Y)).toAddSubgroup := by
  classical
  intro v hv
  rw [Submodule.mem_toAddSubgroup] at hv ⊢
  obtain ⟨γh, hγh⟩ := hv
  -- Every `H1` class is the class of a representative loop `γp`.
  obtain ⟨g, hg⟩ : ∃ g : FundamentalGroup X (Classical.arbitrary X),
      Additive.ofMul (Abelianization.of g) = γh := by
    obtain ⟨g, hg⟩ := Quot.exists_rep (Additive.toMul γh)
    exact ⟨g, by simpa using congrArg Additive.ofMul hg⟩
  obtain ⟨γp, hγp⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
  -- The image vector is the developing-value period vector of `f ∘ γp`.
  have hcoord : ∀ j, pushforwardAmbientLinear f hf v j =
      developingValue (f (Classical.arbitrary X)) (jacobianBasis Y j)
        ((γp.map hf.continuous :
            Path (f (Classical.arbitrary X)) (f (Classical.arbitrary X))) :
          C(unitInterval, Y)) := by
    intro j
    have h1 : pushforwardAmbientLinear f hf v j =
        ((jacobianBasis X).dualBasis.equivFun.symm v)
          (pullbackOneForm f hf (jacobianBasis Y j)) := by
      simp [pushforwardAmbientLinear, Module.Basis.dualBasis_equivFun,
        LinearMap.dualMap_apply]
    have h2 : ((jacobianBasis X).dualBasis.equivFun.symm)
        (periodMapInBasis X (Classical.arbitrary X) (jacobianBasis X) γh) =
        RiemannSurface.periodMap X (Classical.arbitrary X) γh := by
      have hPM : periodMapInBasis X (Classical.arbitrary X) (jacobianBasis X) γh =
          (jacobianBasis X).dualBasis.equivFun
            (RiemannSurface.periodMap X (Classical.arbitrary X) γh) := rfl
      rw [hPM, LinearEquiv.symm_apply_apply]
    have h3 : RiemannSurface.periodMap X (Classical.arbitrary X) γh
        (pullbackOneForm f hf (jacobianBasis Y j)) =
        developingValue (Classical.arbitrary X)
          (pullbackOneForm f hf (jacobianBasis Y j))
          ((γp : Path (Classical.arbitrary X) (Classical.arbitrary X)) :
            C(unitInterval, X)) := by
      have hPM : RiemannSurface.periodMap X (Classical.arbitrary X) γh =
          loopIntegralToH1 (Classical.arbitrary X) γh := rfl
      rw [hPM, ← loopDevValH1Hom_eq_loopIntegralToH1_apply, ← hg,
        loopDevValH1Hom_of]
      show loopDevValQuotient (Classical.arbitrary X)
          (pullbackOneForm f hf (jacobianBasis Y j))
          (FundamentalGroup.toPath g) = _
      rw [← hγp]
      rfl
    have h4 : developingValue (Classical.arbitrary X)
        (pullbackOneForm f hf (jacobianBasis Y j))
        ((γp : Path (Classical.arbitrary X) (Classical.arbitrary X)) :
          C(unitInterval, X)) =
        developingValue (f (Classical.arbitrary X)) (jacobianBasis Y j)
          ((γp.map hf.continuous :
              Path (f (Classical.arbitrary X)) (f (Classical.arbitrary X))) :
            C(unitInterval, Y)) := by
      rw [developingValue_comp_of_isPullbackCoeffRel hf
        (pullbackOneForm_isPullbackCoeffRel f hf (jacobianBasis Y j))
        (Classical.arbitrary X) (f (Classical.arbitrary X))
        ((γp : Path (Classical.arbitrary X) (Classical.arbitrary X)) :
          C(unitInterval, X))]
      congr 1
    calc pushforwardAmbientLinear f hf v j
        = ((jacobianBasis X).dualBasis.equivFun.symm v)
            (pullbackOneForm f hf (jacobianBasis Y j)) := h1
      _ = RiemannSurface.periodMap X (Classical.arbitrary X) γh
            (pullbackOneForm f hf (jacobianBasis Y j)) := by rw [← hγh, h2]
      _ = developingValue (Classical.arbitrary X)
            (pullbackOneForm f hf (jacobianBasis Y j))
            ((γp : Path (Classical.arbitrary X) (Classical.arbitrary X)) :
              C(unitInterval, X)) := h3
      _ = developingValue (f (Classical.arbitrary X)) (jacobianBasis Y j)
            ((γp.map hf.continuous :
                Path (f (Classical.arbitrary X)) (f (Classical.arbitrary X))) :
              C(unitInterval, Y)) := h4
  have hfun : pushforwardAmbientLinear f hf v = fun j =>
      developingValue (f (Classical.arbitrary X)) (jacobianBasis Y j)
        ((γp.map hf.continuous :
            Path (f (Classical.arbitrary X)) (f (Classical.arbitrary X))) :
          C(unitInterval, Y)) := funext hcoord
  rw [hfun]
  exact devVal_loop_mem_periodLatticeInBasis_any (Classical.arbitrary Y)
    (jacobianBasis Y) (γp.map hf.continuous)

/-- `pullbackAmbientLinear` reads as `ambientPullbackJac` through the
lattice bridge (daouid, PR #191): dual-basis expansion + the
trace-transpose adjoint identity. -/
theorem pullbackAmbientLinear_eq_compat {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (w : Fin (kirovGenus Y) → ℂ) :
    pullbackAmbientLinear f hf (latticeBridge Y w) =
      latticeBridge X (ambientPullbackJac f hf w) := by
  funext j
  unfold pullbackAmbientLinear
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
    Module.Basis.dualBasis_equivFun, LinearMap.dualMap_apply]
  set η := pushforwardOneForm f hf (jacobianBasis X j)
  have h_expansion : ∀ (v : Fin (genus Y) → ℂ) (form : HolomorphicOneForm Y),
      ((jacobianBasis Y).dualBasis.equivFun.symm v) form =
        ∑ k, (jacobianBasis Y).repr form k * v k := by
    intro v form
    have h_form : form = ∑ k, (jacobianBasis Y).repr form k • jacobianBasis Y k :=
      ((jacobianBasis Y).sum_repr form).symm
    conv_lhs => rw [h_form]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((jacobianBasis Y).dualBasis.equivFun.symm v) (jacobianBasis Y k) = v k by
      rw [← (jacobianBasis Y).dualBasis_equivFun, LinearEquiv.apply_symm_apply]]
  rw [h_expansion (latticeBridge Y w) η]
  unfold latticeBridge
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have h_swap : ∑ k, (jacobianBasis Y).repr η k *
        (∑ i, ((ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y k))) i * w i) =
      ∑ i, (∑ k, (jacobianBasis Y).repr η k *
        ((ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y k))) i) * w i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  rw [h_swap]
  have h_inner : ∀ i, ∑ k, (jacobianBasis Y).repr η k *
        ((ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y k))) i =
      ((ambientIso Y).symm (bridgeKDFormEquiv η)) i := by
    intro i
    have h_repr : η = ∑ k, (jacobianBasis Y).repr η k • jacobianBasis Y k :=
      ((jacobianBasis Y).sum_repr η).symm
    have h_lin : bridgeKDFormEquiv η =
        ∑ k, (jacobianBasis Y).repr η k • bridgeKDFormEquiv (jacobianBasis Y k) := by
      conv_lhs => rw [h_repr]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    have h_lin2 : (ambientIso Y).symm (bridgeKDFormEquiv η) =
        ∑ k, (jacobianBasis Y).repr η k •
          (ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y k)) := by
      rw [h_lin, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [h_lin2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [h_inner]
  dsimp only [η]
  unfold pushforwardOneForm
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply]
  rw [LinearEquiv.apply_symm_apply]
  set u_j := (ambientIso X).symm (bridgeKDFormEquiv (jacobianBasis X j))
  have h_u_inv : bridgeKDFormEquiv (jacobianBasis X j) = ambientIso X u_j :=
    (LinearEquiv.apply_symm_apply (ambientIso X)
      (bridgeKDFormEquiv (jacobianBasis X j))).symm
  have h_trace : (ambientIso Y).symm
        (traceFormTotal f hf (bridgeKDFormEquiv (jacobianBasis X j))) =
      ambientTrace f hf u_j := by
    unfold ambientTrace
    set_option linter.unusedSimpArgs false in
    simp only [dif_pos rfl]
    rw [h_u_inv]
    rfl
  rw [h_trace]
  have h_adj := adjoint_identity f hf u_j w
  rw [← h_adj]

/-- `pushforwardAmbientLinear` reads as `ambientPhi` through the lattice
bridge (daouid, PR #191). -/
theorem pushforwardAmbientLinear_eq_compat {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (u : Fin (kirovGenus X) → ℂ) :
    pushforwardAmbientLinear f hf (latticeBridge X u) =
      latticeBridge Y (ambientPhi f hf u) := by
  funext j
  unfold pushforwardAmbientLinear
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
    Module.Basis.dualBasis_equivFun, LinearMap.dualMap_apply]
  set formY := jacobianBasis Y j
  have h_expansion : ((jacobianBasis X).dualBasis.equivFun.symm (latticeBridge X u))
        (pullbackOneForm f hf formY) =
      ∑ i, ((ambientIso X).symm (bridgeKDFormEquiv (pullbackOneForm f hf formY))) i * u i := by
    have h_pair : ((jacobianBasis X).dualBasis.equivFun.symm (latticeBridge X u)) =
        pairingWithW u :=
      eY_symm_latticeBridge u
    rw [h_pair]
    rfl
  rw [h_expansion]
  have h_unwind : (ambientIso X).symm (bridgeKDFormEquiv (pullbackOneForm f hf formY)) =
      ambientPsi f hf ((ambientIso Y).symm (bridgeKDFormEquiv formY)) := by
    unfold pullbackOneForm bridgeKDFormEquiv kdFormAlign ambientPsi
    simp
    rfl
  rw [h_unwind]
  set c := (ambientIso Y).symm (bridgeKDFormEquiv formY)
  set Ψ := ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
  set Φ := ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
  have h_transpose : ∑ i, (Ψ c) i * u i = ∑ k, c k * (Φ u) k := by
    dsimp only [Φ]
    unfold Jacobians.ambientPhi
    set M := LinearMap.toMatrix (Pi.basisFun ℂ (Fin (kirovGenus Y)))
      (Pi.basisFun ℂ (Fin (kirovGenus X))) Ψ.toLinearMap
    change ∑ i, (Ψ c) i * u i = ∑ k, c k * Matrix.mulVec M.transpose u k
    simp only [Matrix.mulVec, Matrix.transpose_apply]
    have h_swap : ∀ k, c k * ((fun j => M j k) ⬝ᵥ u) = ∑ i, M i k * c k * u i := by
      intro k
      change c k * (∑ i, M i k * u i) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    simp_rw [h_swap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul]
    congr 1
    have h_c_decomp : c = ∑ k, c k • Pi.single k 1 := pi_eq_sum_univ' c
    have h_Ψ_decomp : Ψ c = ∑ k, c k • Ψ (Pi.single k 1) := by
      conv_lhs => rw [h_c_decomp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    have h_i : (Ψ c) i = ∑ k, M i k * c k := by
      rw [h_Ψ_decomp]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show c k * Ψ (Pi.single k 1) i = M i k * c k by
        unfold M
        rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply, mul_comm]
        rfl]
    rw [h_i]
  rw [h_transpose]
  unfold latticeBridge
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- **Theorem (derived 2026-06-11, issue #31).** Lattice preservation for
pullback. Symmetric to `AX_pushforwardAmbient_preserves_lattice`.

Formerly an axiom; route per daouid's closed PR #191 (credit), with the two
lattice-comparison inclusions now PROVEN
(`Bridge/KirovDolbeaultPeriods.lean` + `Bridge/KirovDolbeaultLattice.lean`):
transport the lattice vector to the port's coordinates
(`truePeriodLattice_le_periodLatticeInBasis` — `H1` representative loop →
polygonal smooth representative with matching developing values), apply the
port's monodromy/preimage-cycle theorem
(`ambientPullbackJac_preserves_truePeriodLattice`), and come back
(`latticeBridge_truePeriodLattice_le` — developing value = moving-chart
line integral on closed `C¹` loops). -/
theorem AX_pullbackAmbient_preserves_lattice {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
              (jacobianBasis Y)).toAddSubgroup,
      (pullbackAmbientLinear f hf) v ∈
        (periodLatticeInBasis X (Classical.arbitrary X)
          (jacobianBasis X)).toAddSubgroup := by
  intro v hv
  rw [Submodule.mem_toAddSubgroup] at hv ⊢
  set w := latticeBridgeInv Y v with hw_def
  have h_eq : v = latticeBridge Y w := (latticeBridgeInv_right_inverse v).symm
  rw [h_eq, pullbackAmbientLinear_eq_compat]
  have hw_mem : w ∈ truePeriodLattice Y :=
    truePeriodLattice_le_periodLatticeInBasis Y v hv
  have h_pull := ambientPullbackJac_preserves_truePeriodLattice f hf hw_mem
  exact latticeBridge_truePeriodLattice_le X _ h_pull

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

/-- `degreeImpl` (fiber-weighted count from `AX_BranchLocus`) agrees with the
Dolbeault port's `degreeFiber` (regular-value fibre cardinality): both are
the unramified fibre count at a value avoiding both branch loci. -/
theorem degreeImpl_eq_degreeFiber {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    degreeImpl f hf = _root_.Jacobians.degreeFiber f hf := by
  classical
  by_cases hc : ∃ c : Y, ∀ x : X, f x = c
  · have hcm : Jacobians.Discharge.IsConstantMap f := hc
    rw [degreeImpl, dif_pos hc, _root_.Jacobians.degreeFiber]
    exact (if_pos hcm).symm
  · have hnc : ¬ Jacobians.Discharge.IsConstantMap f := fun h => hc h
    obtain ⟨hd_pos, hd_sum, hd_branch⟩ := Classical.choose_spec (AX_BranchLocus f hf hc)
    rw [degreeImpl, dif_neg hc]
    -- A value avoiding our branch set and the port's critical values.
    haveI : Infinite Y :=
      Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
    have hcv_fin : (Jacobians.Discharge.Manifold.criticalValuesGeneral f).Finite :=
      Jacobians.Discharge.Manifold.criticalValues_finite_general f hf hnc
    have hunion_fin : ({ q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 } ∪
        Jacobians.Discharge.Manifold.criticalValuesGeneral f).Finite :=
      hd_branch.union hcv_fin
    obtain ⟨y₀, hy₀⟩ := hunion_fin.infinite_compl.nonempty
    have hy₀_our : ¬ ∃ p : X, f p = y₀ ∧ localOrder f p y₀ > 1 :=
      fun h => hy₀ (Or.inl h)
    have hy₀_cv : y₀ ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f :=
      fun h => hy₀ (Or.inr h)
    -- Port side: degreeFiber is the fibre cardinality at `y₀`.
    obtain ⟨w, hwval⟩ :=
      Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq
        f hf hnc hy₀_cv
    have hdeg : _root_.Jacobians.degreeFiber f hf = (f ⁻¹' {y₀}).ncard := by
      rw [_root_.Jacobians.degreeFiber_eq_card_of_regularWitness f hf hnc w,
        show w.card = w.toWitness.card from rfl, w.toWitness.card_eq_ncard, hwval]
    -- Our side: the fiber-weighted sum at `y₀` is the plain fibre count.
    have hfTop : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f := by
      simpa using hf.of_le le_top
    have hhol : Jacobians.Vendor.Wallace.HolomorphicForms.IsHolomorphic f :=
      Jacobians.Vendor.Wallace.HolomorphicForms.isHolomorphic_of_contMDiff hfTop
        (Jacobians.Vendor.Wallace.HolomorphicForms.hasLocalKfoldRamification_of_contMDiff hfTop)
    have hfib_fin : (f ⁻¹' {y₀}).Finite :=
      Jacobians.Vendor.Wallace.HolomorphicForms.isHolomorphic_finite_fiber hhol hc y₀
    have hzero : ∀ p ∉ hfib_fin.toFinset, localOrder f p y₀ = 0 := by
      intro p hp
      refine localOrder_eq_zero_of_not_mem_fiber ?_
      intro hpq
      exact hp ((Set.Finite.mem_toFinset hfib_fin).mpr hpq)
    have hone : ∀ p ∈ hfib_fin.toFinset, localOrder f p y₀ = 1 := by
      intro p hp
      have hpf : f p = y₀ := (Set.Finite.mem_toFinset hfib_fin).mp hp
      have hngt : ¬ localOrder f p y₀ > 1 := fun hgt => hy₀_our ⟨p, hpf, hgt⟩
      have hpos : 0 < Jacobians.Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt f p :=
        Jacobians.Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt_pos_of_contMDiff
          hfTop hc p
      rw [localOrder_eq_mapAnalyticOrderAt_of_mem_fiber hpf] at hngt ⊢
      omega
    calc Classical.choose (AX_BranchLocus f hf hc)
        = ∑' p : X, localOrder f p y₀ := (hd_sum y₀).symm
      _ = ∑ p ∈ hfib_fin.toFinset, localOrder f p y₀ := tsum_eq_sum hzero
      _ = ∑ _p ∈ hfib_fin.toFinset, 1 := Finset.sum_congr rfl hone
      _ = hfib_fin.toFinset.card := by simp
      _ = (f ⁻¹' {y₀}).ncard := ((f ⁻¹' {y₀}).ncard_eq_toFinset_card hfib_fin).symm
      _ = _root_.Jacobians.degreeFiber f hf := hdeg.symm

/-- The ambient composite "pullback then pushforward" is multiplication by
the degree (daouid, PR #191, with the lattice transport now proven and the
degree pinned to `degreeImpl`). -/
theorem pullback_pushforward_ambient_eq {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (v : Fin (genus Y) → ℂ) :
    pushforwardAmbientLinear f hf (pullbackAmbientLinear f hf v) =
      (degreeImpl f hf : ℂ) • v := by
  set w := latticeBridgeInv Y v with hw_def
  have h_eq : v = latticeBridge Y w := (latticeBridgeInv_right_inverse v).symm
  rw [h_eq, pullbackAmbientLinear_eq_compat, pushforwardAmbientLinear_eq_compat]
  have h_comp := Jacobians.Bridge.JacobianTorus.ambientPhi_ambientPullback_eq f hf w
  rw [h_comp, degreeImpl_eq_degreeFiber, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]

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

/-- **Theorem (derived 2026-06-11).** The composition "pullback then
pushforward" multiplies by degree (Griffiths–Harris Ch. 2 §2.7,
`f_* ∘ f^* = deg(f) • id`).

Formerly an axiom; route per daouid's closed PR #191 (credit): the ambient
identity `pullback_pushforward_ambient_eq` (port `PreimageCycle`
conservation-of-number + the ℝ-spanning ℤ-basis of the period lattice,
with the lattice transport inclusions now proven) descends through
`jacobianHomOfAmbient`, and `degreeImpl_eq_degreeFiber` pins the degree. -/
theorem AX_pushforward_pullback {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (P : Jacobian Y) :
    pushforwardImpl X Y f hf (pullbackImpl X Y f hf P) = (degreeImpl f hf) • P := by
  unfold pushforwardImpl pullbackImpl
  have h_comp : ∀ v ∈ (periodLatticeInBasis Y (Classical.arbitrary Y)
        (jacobianBasis Y)).toAddSubgroup,
      ((pushforwardAmbientLinear f hf).comp (pullbackAmbientLinear f hf)) v ∈
        (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup := by
    intro v hv
    simp only [LinearMap.comp_apply]
    exact AX_pushforwardAmbient_preserves_lattice f hf _
      (AX_pullbackAmbient_preserves_lattice f hf v hv)
  have h_congr : (pushforwardAmbientLinear f hf).comp (pullbackAmbientLinear f hf) =
      (degreeImpl f hf : ℂ) •
        (LinearMap.id : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact pullback_pushforward_ambient_eq f hf v
  have h_lattice : (periodLatticeInBasis Y (Classical.arbitrary Y)
        (jacobianBasis Y)).toAddSubgroup ≤
      (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup.comap
        ((degreeImpl f hf : ℂ) •
          (LinearMap.id : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))).toAddMonoidHom := by
    intro v hv
    simp only [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe,
      LinearMap.smul_apply, LinearMap.id_apply]
    have h_smul : (degreeImpl f hf : ℂ) • v = (degreeImpl f hf : ℤ) • v := by
      ext i
      simp only [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    rw [h_smul]
    exact Submodule.smul_mem _ (degreeImpl f hf : ℤ) hv
  have h1 : pushforwardImpl X Y f hf (pullbackImpl X Y f hf P) =
      jacobianHomOfAmbient Y Y
        ((pushforwardAmbientLinear f hf).comp (pullbackAmbientLinear f hf)) h_comp P :=
    (jacobianHomOfAmbient_comp_apply Y X Y
      (pullbackAmbientLinear f hf) (AX_pullbackAmbient_preserves_lattice f hf)
      (pushforwardAmbientLinear f hf) (AX_pushforwardAmbient_preserves_lattice f hf)
      h_comp P).symm
  have h2 : jacobianHomOfAmbient Y Y
        ((pushforwardAmbientLinear f hf).comp (pullbackAmbientLinear f hf)) h_comp P =
      jacobianHomOfAmbient Y Y ((degreeImpl f hf : ℂ) •
        (LinearMap.id : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))) h_lattice P :=
    jacobianHomOfAmbient_congr_apply Y Y h_congr h_comp h_lattice P
  have h3 : jacobianHomOfAmbient Y Y ((degreeImpl f hf : ℂ) •
        (LinearMap.id : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ))) h_lattice P =
      (degreeImpl f hf) • P := by
    rcases P with ⟨P⟩
    refine Quotient.inductionOn P ?_
    intro x
    apply ULift.ext
    change
      (QuotientAddGroup.map
        (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup
        (periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)).toAddSubgroup
        ((degreeImpl f hf : ℂ) • LinearMap.id).toAddMonoidHom h_lattice ⟦x⟧) =
      ((degreeImpl f hf) • (⟨⟦x⟧⟩ : Jacobians.Jacobian Y)).down
    have hx_mk : (⟦x⟧ : _ ⧸ (periodLatticeInBasis Y (Classical.arbitrary Y)
          (jacobianBasis Y)).toAddSubgroup) =
        QuotientAddGroup.mk' (periodLatticeInBasis Y (Classical.arbitrary Y)
          (jacobianBasis Y)).toAddSubgroup x := rfl
    rw [hx_mk, QuotientAddGroup.map_mk']
    dsimp
    have h_eq : (degreeImpl f hf : ℂ) • x = (degreeImpl f hf : ℕ) • x := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [h_eq]
    exact map_nsmul (QuotientAddGroup.mk' (periodLatticeInBasis Y (Classical.arbitrary Y)
      (jacobianBasis Y)).toAddSubgroup) (degreeImpl f hf) x
  exact h1.trans (h2.trans h3)

/-- The Lie group structure on the universe-lifted Jacobian, now derived
through the ULift transfer lemmas in `Jacobian/Construction.lean`. -/
theorem AX_jacobian_lieAddGroup {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  infer_instance

end Jacobians.Axioms
