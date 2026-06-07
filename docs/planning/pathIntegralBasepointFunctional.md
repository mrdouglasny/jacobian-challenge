> **✅ DISCHARGED — de-opaqued to a real `def`.** This opaque axiom is now a concrete `noncomputable def` (`Jacobians/Axioms/AbelJacobiMap.lean`); this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# `pathIntegralBasepointFunctional` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:98`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~1 focused week, ~150 LOC (thin wrapper redirecting to `Jacobians.Bridge.kirovBackedFunctional`; multi-chart infrastructure lives under `bridgePath`)
**Blocked by:** `bridgePath` (Kirov-side multi-chart path infrastructure); load-bearing for the *combination* with `AX_pathIntegral_local_antiderivative`, and downstream for `AX_ofCurve_contMDiff`, `AX_ofCurve_inj`, `ofCurveAmbient`, `ofCurveImpl`.

**Statement (verbatim):**
```lean
axiom pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ
```

**Why it's an axiom right now:** The path-integral functional `(P₀, P) ↦ (ω ↦ ∫_{P₀}^P ω)` requires (i) a chosen piecewise smooth path from `P₀` to `P`, (ii) chart-local integration of `coeff ∘ φ⁻¹ · (φ ∘ γ)'`, (iii) chart-cover partition refinement so the answer is independent of the cover, and (iv) ℂ-linearity. The Kirov vendor library (`Jacobians/Vendor/Kirov/LineIntegral.lean`) already supplies the chart-local `pathSpeed`, the multi-chart `lineIntegral`, and its `lineIntegral_add` / `lineIntegral_smul` linearity lemmas. The Kirov bridge (`Jacobians/Bridge/KirovLineIntegral.lean`) already packages these into `kirovBackedFunctional`. The path-selection infrastructure (smooth representative `bridgePath`) is the only missing input, and it is owned by `bridgePath.md` (Kirov-side, canonical). This plan therefore reduces to a thin redirection.

**Gemini critique addressed:**
- Completely scrapped the former "Route A" (which attempted to shuffle the axiom into six new `bridgePath*` Kirov vendor axioms) — *superseded again*: see cross-plan patch below; we now adopt the Kirov bridge as the canonical backend rather than building scratch multi-chart infrastructure.
- Added explicit citations to standard Riemann surface texts (Forster, *Lectures on Riemann Surfaces* Ch 1 §9) for the underlying mathematics implemented in the Kirov vendor library.
- Added an escalation trigger for fixing the non-standard `IsManifold` typeclass.

**Proof recipe**

This recipe is a thin wrapper around the Kirov bridge. The underlying mathematics (Forster, *Lectures on Riemann Surfaces*, Chapter 1 §9) is already realised in `Jacobians/Vendor/Kirov/LineIntegral.lean` and packaged in `Jacobians/Bridge/KirovLineIntegral.lean`.

1. **Consume the Kirov-side path infrastructure.** Once `bridgePath.md` discharges `bridgePath : (P₀ P : X) → ℝ → X` and its companion smoothness/integrability lemmas to definitions (`Jacobians/Bridge/BridgePath.lean`), the Kirov bridge's `kirovBackedFunctional` (`Jacobians/Bridge/KirovLineIntegral.lean:301`) becomes a real `def` taking endpoints `(P₀, P)` and returning a `HolomorphicOneForm X →ₗ[ℂ] ℂ`. Linearity is already provided by `Jacobians.Vendor.Kirov.lineIntegral_add` and `lineIntegral_smul`.

2. **Redirect the axiom to the Kirov-backed functional.** In `Jacobians/Axioms/AbelJacobiMap.lean`, replace the `axiom pathIntegralBasepointFunctional` at lines 98–101 with
   ```lean
   noncomputable def pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
       [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] (P₀ P : X) :
       HolomorphicOneForm X →ₗ[ℂ] ℂ :=
     Jacobians.Bridge.kirovBackedFunctional (X := X) P₀ P
   ```

3. **Downstream propagation.** `ofCurveAmbient` (`Jacobians/Axioms/AbelJacobiMap.lean:220–223`) and `ofCurveImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:229–233`) already consume `pathIntegralBasepointFunctional` opaquely; no changes required beyond unfolding the `def` where elaboration demands it.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom pathIntegralBasepointFunctional` (lines 98–101) with the Kirov-bridge `def` above.
- *(No new file in `Jacobians/RiemannSurface/`: the scratch `pathIntegralAnalyticArc` route is retired — see cross-plan patch.)*

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.ofCurveImpl` no longer lists `pathIntegralBasepointFunctional`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The axiom statement uses `[IsManifold 𝓘(ℂ, ℂ) ω X]` which is not standard Mathlib v4.30 syntax. If downstream users or the Kirov bridge strictly demand `[HasGroupoid X (contDiffGroupoid ℂ ⊤)]` (or the holomorphic equivalent) to interface with Mathlib's manifold library, escalate to change the axiom signature.
- If `bridgePath.md` slips and `kirovBackedFunctional` remains tied to `axiom bridgePath`, this plan inherits the slip; coordinate landing with `bridgePath` before flipping `pathIntegralBasepointFunctional` from `axiom` to `def`.

---
**Vetting trail.** Critique: `_vetting/pathIntegralBasepointFunctional.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Path-integration backend unified on the Kirov bridge; scratch `pathIntegralAnalyticArc` route retired.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
