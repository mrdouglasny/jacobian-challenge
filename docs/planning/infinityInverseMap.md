# `infinityInverseMap` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:48`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~1–2 focused weeks, ~250 LOC (one new helper file `OddAtlas/InfinityInverse.lean` plus the discharge in `InfinityChart.lean`)
**Blocked by:** none (it is the *foundation* of the OA2 chart-at-infinity block; the other six OA2 axioms `infinityChart`, `infinityChart_mem_source`, `infinityChart_compat_affineLiftProjX`, `affineLiftProjX_compat_infinityChart`, `infinityChart_compat_affineLiftProjY`, `affineLiftProjY_compat_infinityChart` all reduce to this once it lands)

**Statement (verbatim):**
```lean
/-- The local inverse `t ↦ (x(t), y(t))` on a punctured disk near
`t = 0`, mapping into `HyperellipticAffine H`. Concretely, with
`g := (deg f - 1) / 2`, we have `x = 1/t²·(1 + O(t))` and
`y = 1/t^{2g+1}·(1 + O(t))` after normalizing by `lc(f)`. Domain:
`{ t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < someRadius }`. -/
axiom infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ℂ → HyperellipticAffine H
```

**Why it's an axiom right now:** The docstring (`InfinityChart.lean:43–47`) spells out the construction completely — the uniformizer is `t = y / x^{g+1}` and inverting it defines the behavior on a punctured disk — but the *analytic inversion* step has not been formalized in this repo. Load-bearing pieces: (i) the odd-degree hypothesis `h : Odd H.f.natDegree`, used to pin down the integer exponent `g = (deg f − 1)/2`; (ii) the squarefree hypothesis `H.h_squarefree` (`Hyperelliptic/Basic.lean:30`), which forces `lc(f) ≠ 0` and rules out higher-order vanishing at infinity; (iii) the Mathlib 1D analytic inversion machinery from `Mathlib.Analysis.Analytic.Inverse` which inverts an analytic map whose derivative is non-zero. The docstring header of `InfinityChart.lean:19–26` also flags "No general 'chart at the added point' lemma in Mathlib", making this a pure project obligation.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 (lines 60–95) and the standard algebraic geometry reductions (e.g., **Miranda, *Algebraic Curves and Riemann Surfaces*, §III.1 Example 1.6** and **Mumford, *Tata Lectures on Theta II*, Ch. IIIa §3**). Instead of a raw multi-variable formal series, we eliminate $y$ algebraically and apply the 1D Analytic Inverse Function Theorem.

1. **Infra prerequisite — a `HyperellipticAffine.InfinityInverse` helper file.** Create `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityInverse.lean`. Imports: `Mathlib.Analysis.Analytic.Inverse` (for the 1D analytic inverse function theorem API), `Mathlib.Analysis.Analytic.Basic` (for `AnalyticAt`), `Mathlib.Analysis.SpecialFunctions.Pow.Complex` (for `Complex.sqrt`), `Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart` (for `HyperellipticAffine`).

2. **Algebraic reduction and the reciprocal polynomial.** Set `g := (H.f.natDegree − 1) / 2` (an honest `ℕ`). By defining the uniformizer $t = y/x^{g+1}$, we eliminate $y = t x^{g+1}$. Substituting this into the curve equation $y^2 = f(x)$ gives $t^2 x^{2g+2} = f(x)$. Letting $z = 1/x$, this becomes $t^2 = z^{2g+2} f(1/z)$.
   - Define the reversed polynomial $P(z) = z^{2g+1} f(1/z)$ (in Lean, using `Polynomial.reverse`).
   - Notice that $t^2 = z P(z)$.
   - Evaluate at $z = 0$: $P(0) = c = H.f.leadingCoeff$. Since $H.f \neq 0$, $c \neq 0$.

3. **Define the 1D analytic map.** Substitute $z = w^2$ to get $t^2 = w^2 P(w^2)$, which naturally extracts to $t(w) = w \sqrt{P(w^2)}$.
   - Define $t(w) = w \sqrt{P(w^2)}$ using an analytic branch of `Complex.sqrt` near $c$.
   - Because $P(w^2)$ is a polynomial and $P(0) = c \neq 0$, the composition $\sqrt{P(w^2)}$ is analytic at $w=0$.
   - Thus, $w \mapsto t(w)$ is `AnalyticAt ℂ 0`.

4. **Apply the 1D Analytic Inverse Function Theorem.** Compute the derivative at the origin: $t'(0) = \sqrt{c} \neq 0$.
   - Invoke Mathlib's 1D analytic inverse API (`Mathlib.Analysis.Analytic.Inverse`) to invert $t(w)$.
   - This produces an analytic local inverse $w(t)$ valid on a disk around $t=0$, with $w(0) = 0$ and $w'(0) = 1/\sqrt{c}$.
   - Extract a positive radius `r > 0` on which $w(t)$ converges and is non-zero for $t \neq 0$.

5. **Recover Coordinates.** For $0 < ‖t‖ < r$, define $x(t) = 1/w(t)^2$ and $y(t) = t \cdot x(t)^{g+1}$.
   - Verify the curve relation: $y(t)^2 = t^2 x(t)^{2g+2} = t^2 / w(t)^{4g+4}$.
   - Since $t(w)^2 = w^2 P(w^2) = w^{4g+4} f(1/w^2)$, substituting $w = w(t)$ gives $t^2 = w(t)^{4g+4} f(x(t))$.
   - Therefore, $y(t)^2 = f(x(t))$, showing the map lands in the hyperelliptic curve.

6. **Bundle and discharge.** Define the total function:
   ```lean
   noncomputable def infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
       ℂ → HyperellipticAffine H := fun t =>
     if ht : 0 < ‖t‖ ∧ ‖t‖ < someRadius H h then
       ⟨(xCoord H h t, yCoord H h t), curveRelation H h t ht⟩
     else Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))
   ```
   The `else` branch safely picks the nonempty witness from `Hyperelliptic/Basic.lean:84`. In `InfinityChart.lean:48–49`, replace the axiom with this `noncomputable def`. Export companion lemmas `infinityInverseMap_analyticOn`, `infinityInverseMap_x_eq`, and `infinityInverseMap_y_eq` for downstream compat proofs.

**Next discrete deliverable.** **Steps 2–4 alone** — define the reciprocal polynomial $P(z)$, set up the 1D analytic map $t(w) = w \sqrt{P(w^2)}$, and apply the Analytic Inverse Function Theorem to construct $w(t)$ with its radius. This is a self-contained ~150 LOC PR devoid of `HyperellipticAffine` packaging.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom infinityInverseMap ...` (lines 47–49) with the `noncomputable def` body. Same signature; no downstream changes required.
- (new) `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityInverse.lean` — houses Steps 1–5 (`someRadius`, `xCoord`, `yCoord`, `curveRelation`, `infinityInverseMap_analyticOn`).
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; `infinityChart_compat_affineLift` (lines 83–105) and `affineLift_compat_infinityChart` (lines 108–130) start to consume the analytic API from `InfinityInverse.lean` once the dependent OA2 compat axioms are discharged.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.InfinityChart` succeeds with the axiom replaced by a `def` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.infinityChart` no longer lists `infinityInverseMap` (the *other* OA2 axioms still appear until they too are discharged, but `infinityInverseMap` is gone from the transitive closure).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If resolving branch cuts for the analytic composition of `Complex.sqrt` near $c$ causes continuity/analyticity issues with Mathlib's square root, we might need to manually supply the binomial series for $\sqrt{P(w^2)}$. Escalate if proving `AnalyticAt ℂ 0 t` gets stuck.
- If the radius-of-convergence extracted from the analytic inverse theorem cannot easily be bounded uniformly below by a positive constant `r > 0` (valid for the chosen $H$), and requires altering the domain signature of the axiom, escalate before changing the signature.

### Gemini critique addressed:
- Discarded the mathematically nonsensical multivariate $\Phi = 0$ implicit function setup.
- Eliminated $y$ algebraically using the uniformizer $t = y/x^{g+1}$, changing variables to $x = 1/w^2$ to reduce the curve equation exactly to $t^2 = w^2 P(w^2)$.
- Replaced the flawed `FormalMultilinearSeries.rightInv` compositional approach with Mathlib's high-level 1D analytic inverse function theorem (`Mathlib.Analysis.Analytic.Inverse`) applied to $t(w) = w \sqrt{P(w^2)}$.
- Removed false escalation triggers about "multi-variable inversion", as the system reduces purely to 1D inversion.

---
**Vetting trail.** Critique: `_vetting/infinityInverseMap.md`. Verdict: reject. Revised: 2026-06-03.