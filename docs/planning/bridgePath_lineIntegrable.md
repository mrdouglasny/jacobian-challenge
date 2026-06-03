# `bridgePath_lineIntegrable` — discharge recipe

**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:212`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 6 &nbsp;&nbsp; **Est:** ~1 focused week, ~150–300 LOC, in `Jacobians/Bridge/BridgePath.lean`
**Blocked by:** `bridgePath_chart_differentiable` (and transitively `bridgePath`)

**Statement (verbatim):**
```lean
/-- **Integrability of the bridged line-integrand** along the chosen path.

For every holomorphic 1-form `form : HolomorphicOneForm X` and every
base pair `(P₀, P)`, the integrand `t ↦ (bridgeForm form)(γ t)(γ'(t))`
of `Vendor.Kirov.lineIntegral` along `γ := bridgePath P₀ P` is
interval-integrable on `[0, 1]`.

This is needed to invoke `Vendor.Kirov.lineIntegral_add`, which requires
integrability hypotheses for both summands. In a `C¹` regime this would
follow from continuity of the integrand (continuous image of a compact
interval is bounded, hence integrable), but the
`bridgePath_chart_differentiable` axiom only gives `DifferentiableAt`
chart-locally — not continuous differentiability — so `pathSpeed γ`
need not be continuous in `t` and the integrability has to be assumed
separately.

Discharge plan: produce `bridgePath` as a `C¹`-or-better chart-local
path via `PathConnectedSpace.somePath` + smoothing. Then the integrand
is continuous and this axiom becomes a derived theorem. -/
axiom bridgePath_lineIntegrable (P₀ P : X) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        (bridgePath (X := X) P₀ P t)
        (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P₀ P) t))
      MeasureTheory.volume 0 1
```

**Why it's an axiom right now:** Together with `bridgePath` itself, this is the second of the two **load-bearing** axioms in this file (per `#print axioms kirovBackedFunctional`, see docstring at `KirovLineIntegral.lean:108–114`). It is needed by `kirovBackedFunctional.map_add'` (`:307–315`), which invokes `Jacobians.Vendor.Kirov.lineIntegral_add` (`Vendor/Kirov/LineIntegral.lean:111`); `lineIntegral_add` takes two `IntervalIntegrable` hypotheses (`:112–115`). The reason it cannot already be derived: `bridgePath_chart_differentiable` only gives `DifferentiableAt` (not `C¹`). Furthermore, in Mathlib's manifold architecture, the preferred chart `chartAt (γ t)` jumps discontinuously, meaning both `pathSpeed` and the 1-form's local representation are globally discontinuous. The axiom bridges this by asserting that the *paired integrand* is nonetheless `IntervalIntegrable` on `[0, 1]`. Once we prove the integrand is continuous (by computing the pairing locally in a fixed chart, where the jumping Jacobians cancel out), this axiom becomes a derived theorem.

**Proof recipe**

The strategy is to prove the global integrand is everywhere locally continuous by evaluating it in a fixed local chart, avoiding Mathlib's discontinuous `chartAt` jumps, and then invoking `Continuous.intervalIntegrable` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:503`).

1. **The discontinuity of Mathlib charts.** Mathlib's preferred chart `chartAt (H := ℂ) (γ t)` jumps discontinuously as $t$ varies. Because `pathSpeed γ` (`Vendor/Kirov/LineIntegral.lean:68`) and the bundle coordinate representation `(bridgeForm form).toFun` (`KirovHolomorphic.lean:328`) are defined in terms of `chartAt`, they are *both genuinely globally discontinuous*. Attempting to prove `Continuous (pathSpeed γ)` is a trap and mathematically impossible.

2. **Localize to a fixed chart.** To prove the paired integrand $t \mapsto (\text{bridgeForm form})(\gamma(t))(\text{pathSpeed } \gamma \; t)$ is continuous on $[0,1]$, reduce via `continuous_iff_continuousAt` to showing it is continuous in a neighborhood of any $t_0 \in [0,1]$. For a given $t_0$, pick a **fixed** chart $c$ around $\gamma(t_0)$ (specifically, the chart `extChartAt 𝓘(ℂ, ℂ) Pᵢ` from the chart-line piece containing $t_0$, per `KirovLineIntegral.lean:263`).

3. **Express factors in the fixed chart.** In the fixed chart $c$, define the fixed-chart velocity $\frac{d}{dt} (c \circ \gamma)$ and the fixed-chart 1-form representation.
   - The fixed-chart velocity is continuous in a neighborhood of $t_0$ because `bridgePath` uses a smooth-bump reparametrization (`bridgePath_chart_differentiable`).
   - The fixed-chart 1-form representation is continuous because the form is a `ContMDiffSection`.

4. **Cancel the Jacobians.** In the neighborhood of $t_0$, express the Kirov integrand (which uses the jumping `chartAt`) as a product. Use `Vendor.Kirov.pathSpeed_comp_eq_mfderiv` (`Vendor/Kirov/LineIntegral.lean:506`) to relate the jumping velocity to the fixed-chart velocity. Use the corresponding 1-form transition lemma from Kirov's API to relate the jumping 1-form representation to the fixed-chart representation. The transition Jacobians (the `mfderiv` of the chart changes and its inverse) will exactly cancel out because the pairing of a 1-form and a tangent vector is coordinate-independent.

5. **Apply global integrability.** Because the global integrand equals the pairing of continuous fixed-chart representations on a neighborhood of $t_0$, it is continuous at $t_0$. Since this is true for all $t_0 \in [0, 1]$, the integrand is continuous on the compact interval `[0, 1]`. 
   Apply `Continuous.intervalIntegrable` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:503`):
   ```lean
   theorem bridgePath_lineIntegrable (P₀ P : X) (form : HolomorphicOneForm X) :
       IntervalIntegrable
         (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
           (bridgePath P₀ P t)
           (Jacobians.Vendor.Kirov.pathSpeed (bridgePath P₀ P) t))
         MeasureTheory.volume 0 1 := by
     refine Continuous.intervalIntegrable ?_ 0 1
     rw [continuous_iff_continuousAt]
     intro t₀
     -- Pick fixed chart covering t₀, transition out of chartAt, cancel Jacobians, 
     -- and use continuity of the fixed-chart representations
     sorry
   ```

6. **Replace `axiom` with `theorem` at `KirovLineIntegral.lean:212`.** Move into `Jacobians/Bridge/BridgePath.lean`.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — add `theorem bridgePath_lineIntegrable` and the fixed-chart localization helper lemmas (~150–300 LOC).
- `Jacobians/Bridge/KirovLineIntegral.lean` — delete `axiom bridgePath_lineIntegrable` at `:212` and the surrounding docstring at `:193–211`.

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms Jacobians.Bridge.kirovBackedFunctional` (`KirovLineIntegral.lean:301`) no longer lists `bridgePath_lineIntegrable` (this axiom is currently load-bearing in `map_add'`, see `:307–315`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- **Missing Kirov API for 1-form transitions:** If Kirov's API does not already include the 1-form coordinate transition lemma (the dual to `pathSpeed_comp_eq_mfderiv`), it must be proved to cancel the Jacobians. If defining this transition lemma requires unwinding deep Mathlib bundle internals not exposed by Kirov, escalate.
- If the fixed-chart velocity is discontinuous because the smooth-bump reparametrization in `bridgePath` was not correctly implemented as $C^1$ across chart-line boundaries, escalate to revise the `bridgePath` construction.

## Gemini critique addressed:
- **Effort & LOC recalibrated:** Updated effort from 4 to 6 and LOC to ~150-300, recognizing that wrangling Mathlib's manifold API to bypass discontinuous global charts is highly non-trivial.
- **Abandoned mathematically impossible goal:** Removed the false tactic goal that attempted to prove `Continuous (pathSpeed γ)` and `Continuous ((bridgeForm form).toFun y)`. Acknowledged that Mathlib's `chartAt` makes these factors jump discontinuously.
- **Adopted fixed-chart localization:** Completely rewrote the proof strategy to localize to a *fixed* chart at each $t_0$, proving continuity of the fixed-chart representations and using transition lemmas to demonstrate that the chart-jumping Jacobians cancel when paired.
---
**Vetting trail.** Critique: `_vetting/bridgePath_lineIntegrable.md`. Verdict: reject. Revised: 2026-06-03.