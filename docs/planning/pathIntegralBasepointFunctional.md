# `pathIntegralBasepointFunctional` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:98`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~3–4 focused weeks, ~600–900 LOC (open/closed connectivity path construction, multi-chart integration, cover independence)
**Blocked by:** none upstream (no other axiom in this repo blocks it); load-bearing for the *combination* with `AX_pathIntegral_local_antiderivative`, and downstream for `AX_ofCurve_contMDiff`, `AX_ofCurve_inj`, `ofCurveAmbient`, `ofCurveImpl`.

**Statement (verbatim):**
```lean
axiom pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ
```

**Why it's an axiom right now:** The path-integral functional `(P₀, P) ↦ (ω ↦ ∫_{P₀}^P ω)` requires (i) a chosen piecewise analytic path from `P₀` to `P`, (ii) chart-local integration of `coeff ∘ φ⁻¹ · (φ ∘ γ)'`, (iii) chart-cover partition refinement so the answer is independent of the cover, and (iv) ℂ-linearity. The current Lean infrastructure (`pathIntegralOnChart` in `Jacobians/RiemannSurface/PathIntegral.lean:78–83`) covers only step (ii) on a single chart. Building out the required multi-chart integration is a bounded missing piece of infrastructure.

**Gemini critique addressed:**
- Completely scrapped the former "Route A" (which attempted to shuffle the axiom into six new `bridgePath*` Kirov vendor axioms).
- Replaced the formally nightmarish continuous-path mollification approach with a mathematically rigorous open/closed connectivity argument to construct piecewise analytic paths directly.
- Added explicit citations to standard Riemann surface texts (Forster, *Lectures on Riemann Surfaces* Ch 1 §9).
- Addressed the handling of potentially disconnected chart overlaps by explicitly introducing Lebesgue number lemma partition refinement on the parameter interval.
- Added an escalation trigger for fixing the non-standard `IsManifold` typeclass.

**Proof recipe**

This requires bounded missing infrastructure for path integrals of 1-forms on manifolds, directly following **Forster, *Lectures on Riemann Surfaces*** (Chapter 1, §9 on integration of 1-forms).

1. **Infrastructure piece 1: Piecewise Analytic Paths.**
   Bypass continuous paths entirely. Define the set $E = \{ x \in X \mid \exists \text{ piecewise analytic path from } P_0 \text{ to } x \}$. Prove $E = X$ via the standard topological argument in 4 sub-steps:
   - *Sub-step A:* Prove $E$ is non-empty ($P_0 \in E$ trivially).
   - *Sub-step B:* Prove $E$ is open. For any $x \in E$, the chart around $x$ gives a neighborhood homeomorphic to an open ball in ℂ. Open balls are convex, allowing any $y$ in the chart to connect to $x$ via a straight, analytic line segment.
   - *Sub-step C:* Prove $E$ is closed. If $x \in \overline{E}$, the chart around $x$ intersects $E$ at some point $y$; connect $y$ to $x$ via a straight line in the chart.
   - *Sub-step D:* Conclude $E = X$ because $X$ is connected. *(This connectedness-to-path-existence theorem is the next discrete deliverable).*

2. **Infrastructure piece 2: Partitioned Path Integration.**
   - For a chosen analytic path, pull back the finite open chart cover of the path's image to `[0,1]` via `IsCompact.elim_finite_subcover`.
   - Apply the Lebesgue number lemma to partition the parameter interval `0 = t_0 < t_1 < \dots < t_n = 1` fine enough that each segment maps entirely into a single chart.
   - Define `pathIntegralAnalyticArc` by summing the existing primitive `pathIntegralOnChart` (`Jacobians/RiemannSurface/PathIntegral.lean:78–83`) over the partition pieces.

3. **Cover Independence.**
   Prove the integral is independent of chart cover and partition. On a chart overlap, the chain rule + cocycle identity via `SatisfiesCotangentCocycle` (`Jacobians/RiemannSurface/OneForm.lean:89`) ensures chart-local integrands match. The Lebesgue number partition guarantees evaluation strictly on simply connected sub-intervals in the parameter space, fully resolving any ambiguities from disconnected chart overlaps.

4. **Linearity and Functional Discharge.**
   - Define `pathIntegralBasepointFunctional` by evaluating `pathIntegralAnalyticArc` on the path retrieved from Step 1.
   - Prove ℂ-linearity via `intervalIntegral.integral_add` / `integral_const_mul` applied piece-by-piece.
   - Update downstream dependents `ofCurveAmbient` (`Jacobians/Axioms/AbelJacobiMap.lean:220–223`) and `ofCurveImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:229–233`) to consume the definition, transparently retiring the axiom.

**Files touched**
- `Jacobians/RiemannSurface/PathIntegral.lean` — add the piecewise analytic path construction, Lebesgue number partition, and `pathIntegralAnalyticArc` infrastructure.
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom pathIntegralBasepointFunctional` (lines 98–101) with the new definition.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.ofCurveImpl` no longer lists `pathIntegralBasepointFunctional`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The axiom statement uses `[IsManifold 𝓘(ℂ) ω X]` which is not standard Mathlib v4.30 syntax. If downstream users or the newly built infrastructure strictly demand `[HasGroupoid X (contDiffGroupoid ℂ ⊤)]` (or the holomorphic equivalent) to interface with Mathlib's manifold library, escalate to change the axiom signature.
- If the Lebesgue number lemma on intervals is missing or insufficiently developed in Mathlib to map sub-intervals cleanly into chart domain subsets, escalate before building bespoke metric topology helpers.

---
**Vetting trail.** Critique: `_vetting/pathIntegralBasepointFunctional.md`. Verdict: reject. Revised: 2026-06-03.