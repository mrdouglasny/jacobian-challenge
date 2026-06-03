# Gemini 3.1 Pro critique — `bridgePath_lineIntegrable`

**Model:** gemini-3.1-pro-preview
**Duration:** 122.8s
**Source axiom:** `Jacobians/Bridge/KirovLineIntegral.lean`
**Verdict:** **reject**

---

### 1. Route classification
**provable-from-other-axioms** is the correct classification. The integrability is a derived property of the regularity of the `bridgePath` construction.

### 2. Effort 1..10
The estimate of **4** (~50–120 LOC) is too optimistic. Chart-localization and manifold API wrangling in Mathlib to bypass discontinuous global charts is notoriously painful. Expect an effort of **6** (~150–300 LOC). 

### 3. Proof recipe
The strategy proposed in **Step 6 is fundamentally broken**. You propose splitting the integrand and proving the continuity of its two factors:
1. `have hSpeed : Continuous (pathSpeed γ)`
2. `have hSec : Continuous (fun y => ...toFun y)`

This is mathematically and definitionally impossible in Mathlib. Both `pathSpeed γ t` and `toFun y` are defined in terms of the preferred chart `chartAt (γ t)`. In Mathlib's manifold architecture, `chartAt` is an arbitrary choice function that can (and will) jump discontinuously as `γ t` varies. When the chart jumps, the coordinate representations of the velocity vector and the 1-form jump discontinuously by the transition Jacobian and its inverse. 

Thus, **both factors are genuinely globally discontinuous**. You will never prove `hSpeed` or `hSec`, and `fun_prop` cannot rescue you from multiplying two discontinuous functions.

### 4. Textbook citations
N/A. This is entirely an artifact of Mathlib's topological fiber bundle and local chart architecture.

### 5. What's missing or wrong
- **False intermediate goals:** The tactic body in Step 6 is a trap. Mathlib's `ContMDiffSection.continuous` proves continuity of the section into the bundle's `TotalSpace`, *not* continuity of the local coordinate representation `toFun y` into `E →L[ℝ] ℂ`. Similarly, `pathSpeed` into `ℂ` is genuinely discontinuous.
- **Missing fixed-chart localization:** The only continuous object here is the *integrand* (the pairing of the 1-form and the velocity), because the jumping Jacobians cancel out (chart-independence of the pairing). To prove the integrand is continuous, you must localize. For any $t_0$, pick a **fixed** chart $c$ around $\gamma(t_0)$ (e.g., the chart `Pᵢ` from your piece), express both the 1-form and velocity in $c$, prove *those* fixed-chart representations are continuous on a neighborhood of $t_0$, and then prove their product equals the Kirov integrand using `pathSpeed_comp_eq_mfderiv` and the corresponding Kirov 1-form transition lemma.
- **Misunderstanding chart-line pieces:** In Step 2, you assume that on a chart-line piece, `pathSpeed` behaves smoothly. Even if $\gamma(t)$ is entirely inside the domain of `extChartAt Pᵢ`, the preferred chart `chartAt (γ t)` can still jump wildly inside that piece. The chart-line construction gives you continuity in $P_i$'s chart, not in `chartAt (γ t)`.

### 6. Recommendation
**Reject**. The proposed tactic state contains provably false goals. Revise the plan to prove the continuity of the integrand directly via local fixed-chart trivializations, completely abandoning any attempt to prove `Continuous (pathSpeed γ)`. Ensure you have the 1-form transition lemma available from Kirov's API to cancel the Jacobians before you start writing code.

VERDICT: reject — The plan attempts to prove global continuity of chart-dependent factors (velocity and 1-form) which jump discontinuously in Mathlib; you must instead prove continuity of the paired integrand locally in a fixed chart.
