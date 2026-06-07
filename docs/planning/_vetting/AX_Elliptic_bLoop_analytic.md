> **✅ DISCHARGED — 2026-06-07.** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_Elliptic_bLoop_analytic`

**Model:** gemini-3.1-pro-preview
**Duration:** 30.2s
**Source axiom:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed discharge plan.

### 1. Route Classification
**Incorrect.** The route is classified as `provable-from-other-axioms`, but this tag is reserved for axioms that are deduced from *other remaining challenge axioms*. This proof does not rely on any other unproved axioms; it simply uses the `ComplexTorus` API defined in the project and Mathlib's manifold/calculus library. The correct route is **`mathlib-now`** (or `needs-infra` if significant `ComplexTorus` chart API is missing, but the plan correctly notes that the chart formulas already exist).

### 2. Effort Estimate
**Accurate.** The estimate of 3 (~60–100 LOC, half a day to a day) is spot on, especially given the excellent proposal to use a shared helper lemma for both the A-cycle and B-cycle. 

### 3. Proof Recipe
The recipe is logically sound and correctly identifies the core manifold calculation (pulling back the quotient map through the chart to reveal a simple affine translation). However, there are a few tactical improvements needed:

* **Step 5 (Analyticity of the affine map):** The recipe states "transfer via `AnalyticAt.congr`". To actually prove `r ↦ (r:ℂ) * ω₂ - c` is analytic over `ℝ`, you should point out that the coercion `r ↦ (r:ℂ)` is exactly `Complex.ofRealAm`, which is an `ℝ`-linear isometry (a `ContinuousLinearMap`). Therefore, its analyticity is provided immediately by `ContinuousLinearMap.analyticAt`. Multiplication by `ω₂` and subtraction of `c` are handled by `AnalyticAt.mul_const` (or `ContinuousLinearMap.analyticAt` again) and `AnalyticAt.sub`. 
* **Step 6 (Shared helper design):** The proposed `analyticAt_lattice_affine_arc` lemma is unnecessarily hardcoded to `(ellipticLattice ω₁ ω₂ h)`. It is much better math-engineering to state this for **any** `ComplexTorus L` and an arbitrary vector `v : ℂ`:
  ```lean
  private lemma analyticAt_torus_affine_arc {L : AddSubgroup ℂ} [DiscreteTopology L] [Rk2 L]
      (v : ℂ) (u : ℝ) (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    AnalyticAt ℝ
      (fun r : ℝ =>
        (extChartAt 𝓘(ℂ) ((QuotientAddGroup.mk' L : ℂ → _) ((u:ℂ) * v)))
        ((QuotientAddGroup.mk' L : ℂ → _) ((r:ℂ) * v))) u
  ```
  This cleanly decouples the manifold/chart logic from the specific `ω₁, ω₂` elliptic curve generators, and immediately solves both `aLoop` and `bLoop`. Note also the use of `𝓘(ℂ)` instead of `𝓘(ℂ, ℂ)` depending on the Mathlib 4 version's notation for `modelWithCornersSelf ℂ ℂ`.

### 4. Textbook Citations
N/A. This is a local chart verification that follows immediately from the definition of a quotient manifold. No textbook citation is needed.

### 5. What's Missing or Wrong
* **Classification:** As noted, `provable-from-other-axioms` is wrong. It is `mathlib-now`.
* **Coupling:** The shared helper lemma shouldn't know about `Elliptic ω₁ ω₂ h`. It should be a lemma about `ComplexTorus`.
* **Boundary points:** The `IsAnalyticArc` documentation states checking at "every interior point". Be absolutely sure that `AnalyticArc.partition` doesn't implicitly require one-sided analyticity (or extensions to an open neighborhood of the closed interval `[0, 1]`). If the project's `IsAnalyticArc` strictly requires `u ∈ Ioo 0 1`, then the plan is perfectly aligned.

### 6. Recommendation
**Revise.** Fix the route classification and generalize the helper lemma to `ComplexTorus` so it doesn't hardcode the curve's generators.

VERDICT: revise — Change route to `mathlib-now` and abstract the shared helper lemma to apply to any `ComplexTorus` and arbitrary complex vector `v` rather than hardcoding the `ω₁`/`ω₂` elliptic generators.
