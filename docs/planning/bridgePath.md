# `bridgePath` — discharge recipe


> ✅ **DISCHARGED 2026-06-04** (branch `phase2-bridgepath`). Converted from `axiom` to a real `def`/`theorem` backed by `Jacobians/Bridge/BridgePath.lean` (smooth path-connectedness of a connected complex 1-manifold). See [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) → Recently discharged. The recipe below is retained as historical record.


**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:164`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~3–4 focused weeks, ~800+ LOC, mostly a new helper file `Jacobians/Bridge/BridgePath.lean` plus infrastructure for convex charts and flat reparameterization
**Blocked by:** none (this is the keystone — once it is a real `def`, the other five `bridgePath*` axioms in this file collapse to short derivations)

**Statement (verbatim):**
```lean
/-- A chosen smooth path from `P₀` to `P` in `X`. -/
axiom bridgePath (P₀ P : X) : ℝ → X
```

**Why it's an axiom right now:** This is the structural path-selection axiom introduced by the Kirov path-integral bridge (`KirovLineIntegral.lean:23–44`, `:108–114`, `:156–161`). Our `pathIntegralBasepointFunctional` takes a pair of endpoints `(P₀, P)`, but Kirov's `lineIntegral` takes a parameterized path `γ : ℝ → X`; closing the gap requires a function `(P₀, P) ↦ (ℝ → X)` whose value is a smoothly concatenated path from `P₀` to `P`. The docstring at `:108–114` is explicit that `bridgePath` and `bridgePath_lineIntegrable` are the two load-bearing axioms. The existence of a continuous path follows from topological properties, but producing an everywhere-smooth representative requires manifold infrastructure currently missing in Mathlib (covers by convex chart balls and flat-at-endpoint reparameterizations).

**Scope note (canonical Kirov-side input).** The multi-chart infrastructure built here — convex-chart-ball cover refinement, flat-at-endpoints reparameterization, smooth concatenation — is the *single canonical* path-selection input feeding `Jacobians.Bridge.kirovBackedFunctional`, which in turn backs `pathIntegralBasepointFunctional` (see `pathIntegralBasepointFunctional.md`). It is **not** a parallel project to a hypothetical scratch `pathIntegralAnalyticArc`; that scratch route has been retired.

**Proof recipe**

This recipe fulfills the bounded infrastructure requirement of proving that a connected topological manifold is smoothly path-connected (cf. **John M. Lee, *Introduction to Smooth Manifolds*, Proposition 2.15**). It builds `bridgePath` in multiple layers:

1. **Establish Topological Path-Connectedness.** Mathlib does not provide a free `ChartedSpace.locPathConnected` instance. Manually construct a `LocPathConnectedSpace X` instance by transferring the local path-connectedness of $\mathbb{C}$ through the chart basis (since `ChartedSpace` guarantees local homeomorphisms). Then, promote `ConnectedSpace X` + `LocPathConnectedSpace X` to `PathConnectedSpace X` and obtain a continuous base path:
   ```lean
   let γ₀ : Path P₀ P := PathConnectedSpace.somePath P₀ P
   ```

2. **Refine Cover with Convex Chart Balls (The Convexity Gap).** The raw image of `extChartAt` is an arbitrary open subset of $\mathbb{C}$, which is not necessarily convex. 
   - Cover the compact image of `γ₀` in `X` with chart neighborhoods whose images in $\mathbb{C}$ are strictly open balls (which are convex).
   - Use the Lebesgue number lemma on the pullback of this cover to `[0, 1]` to extract a finite sequence of compact sub-intervals `[tᵢ, tᵢ₊₁]` covering `[0, 1]`. On each sub-interval, `γ₀` stays entirely within one of these convex chart balls.

3. **Flat-at-Endpoints Reparameterization (The Junction Corner Gap).** 
   - On each sub-interval `[tᵢ, tᵢ₊₁]`, replace `γ₀` with the straight line between `γ₀ tᵢ` and `γ₀ tᵢ₊₁` in chart coordinates. Because the chart image is a convex ball, this straight line cannot exit the chart domain.
   - Standard generic concatenation (`Path.trans`) scales intervals linearly and will create non-differentiable corners at the junctions. To fix this, build a bounded infrastructure piece: a flat-at-endpoints $C^1$ reparameterization polynomial, e.g., $\phi(s) = 3s^2 - 2s^3$ for $s \in [0, 1]$.
   - Pre-compose the straight-line segment on each sub-interval with this $\phi$. This ensures the left and right derivatives at every junction point $tᵢ$ are exactly zero.

4. **Concatenation and Extension.** 
   - Concatenate these reparameterized, derivative-vanishing segments to form a single, everywhere-differentiable path on `[0, 1]`.
   - Extend the path to `ℝ → X` (constant before 0 and after 1) using `Path.extend`. 
   - The result is `bridgePathOfPath γ₀`, which is continuous, endpoint-correct, and everywhere `DifferentiableAt`.

5. **Package and Replace.**
   - Define `noncomputable def bridgePath (P₀ P : X) : ℝ → X := bridgePathOfPath (PathConnectedSpace.somePath P₀ P)` in `Jacobians/Bridge/BridgePath.lean`.
   - In `KirovLineIntegral.lean:164`, replace the `axiom` with `export Jacobians.Bridge.BridgePath (bridgePath)`.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — **new file.** Contains the infrastructure for convex chart ball covers, the flat polynomial reparameterization $\phi(s)$, `bridgePathOfPath`, `bridgePath`, and the companion theorems that retire the other five axioms in the block at `KirovLineIntegral.lean:164–217`.
- `Jacobians/Bridge/KirovLineIntegral.lean` — replace the six `axiom` declarations (`:164`, `:167`, `:182`, `:188`, `:191`, `:212`) with `theorem`s (or `export`s from the new file).
- `Jacobians.lean` (root module) — add `import Jacobians.Bridge.BridgePath`.

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms Jacobians.Bridge.kirovBackedFunctional` (`KirovLineIntegral.lean:301`) no longer lists `bridgePath` or its five companion axioms.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 6.

**Risk / escalation triggers**
- If the Lebesgue number lemma extraction over the convex chart balls hits missing API for generic topological spaces vs metric spaces in Mathlib's topology library, escalate.
- If proving that the piecewise concatenation of flat-reparameterized segments satisfies `DifferentiableAt ℝ` everywhere runs into overly hostile Mathlib calculus edge-cases at the junctions, escalate for a tactical workaround.

### Gemini critique addressed:
- **Route and Effort updated:** Reclassified to `needs-infra` and recalibrated Effort to 8 (~3-4 weeks, ~800+ LOC) due to the required missing manifold infrastructure.
- **The Convexity Gap addressed:** Modified the proof to refine the open cover using chart neighborhoods whose images are convex open balls, guaranteeing straight lines cannot exit the chart domain.
- **The Junction Corner Gap addressed:** Added a flat-at-endpoints polynomial reparameterization step (e.g., $3s^2 - 2s^3$) prior to concatenation to force junction derivatives to zero, preventing non-differentiable corners.
- **Textbook citation added:** Included the explicit reference to John M. Lee, *Introduction to Smooth Manifolds*, Proposition 2.15.
- **Mathlib instances corrected:** Clarified that `LocPathConnectedSpace X` must be manually transferred through the chart basis, rather than relying on a non-existent free instance.

---
**Vetting trail.** Critique: `_vetting/bridgePath.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Path-integration backend unified on the Kirov bridge; scratch `pathIntegralAnalyticArc` route retired.
