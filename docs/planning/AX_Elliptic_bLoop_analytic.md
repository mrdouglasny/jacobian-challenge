# `AX_Elliptic_bLoop_analytic` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:90`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~1 focused day, ~60–100 LOC (shares helper with `AX_Elliptic_aLoop_analytic`)
**Blocked by:** none (mirror of `AX_Elliptic_aLoop_analytic`, same ComplexTorus chart lemmas)

**Statement (verbatim):**
```lean
axiom AX_Elliptic_bLoop_analytic :
    IsAnalyticArc (Elliptic ω₁ ω₂ h) (bLoopExtend ω₁ ω₂ h) {0, 1}
```

**Why it's an axiom right now:** Identical situation to `AX_Elliptic_aLoop_analytic`. The B-cycle `bLoopExtend r := ⟦(r:ℂ) * ω₂⟧` (`Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:64-65`) is affine in `r` once read through the `ComplexTorus` chart, but the `IsAnalyticArc` predicate (`Jacobians/RiemannSurface/AnalyticArc.lean:54-59`) was packaged as a `True`-replacement axiom pending the same atlas-local description used in `AX_Elliptic_aLoop_analytic`.

**Proof recipe**

This is `mathlib-now` and structurally identical to `AX_Elliptic_aLoop_analytic`; only the lattice generator changes from `ω₁` to `ω₂`. The two should share a generalized helper proven by a small auxiliary lemma parameterized by `v : ℂ` on an arbitrary `ComplexTorus`.

1. **Unpack `IsAnalyticArc`** at `Jacobians/RiemannSurface/AnalyticArc.lean:54-59`. Partition `{0, 1}` has the unique interval `(0, 1)`, so reduce to `u ∈ Set.Ioo 0 1` and analyze the chart pullback.

2. **Locate `bLoopExtend u`.** By definition (`Witnesses.lean:64-65`),
   `bLoopExtend ω₁ ω₂ h u = QuotientAddGroup.mk' L.toAddSubgroup ((u:ℂ) * ω₂)` with `L := ellipticLattice ω₁ ω₂ h`. Call this `p`.

3. **Use the ComplexTorus chart formula.** Same citations as the A-cycle recipe — `chart_apply_mk` (`Jacobians/AbelianVariety/ComplexTorus.lean:151-156`), `extChartAt_apply_quotient_mk` (`Jacobians/AbelianVariety/ComplexTorus.lean:265-268`), `extChartAt_symm_eq_quotient_mk` (`Jacobians/AbelianVariety/ComplexTorus.lean:164-171`), and the `chartTarget` open-ball description (`ComplexTorus.lean:108-109`). For `r` in a small neighborhood of `u`, `(r:ℂ) * ω₂` lies in `chartTarget L p` (continuity argument).

4. **Affine formula.**
   ```lean
   f =ᶠ[𝓝 u] fun r : ℝ => (r : ℂ) * ω₂ - c
   ```
   for `c := liftPoint L p - (u:ℂ) * ω₂`, exactly as in step 4 of `AX_Elliptic_aLoop_analytic.md`. This is the same translation-by-lattice-element argument that drives `transition_fderiv_apply_one` at `Jacobians/AbelianVariety/ComplexTorus.lean:273-340`.

5. **Conclude analyticity.** The coercion `r ↦ (r:ℂ)` is exactly `Complex.ofRealAm`, which is an `ℝ`-linear isometry. Therefore, its analyticity is provided immediately by `ContinuousLinearMap.analyticAt`. Multiplication by `ω₂` and subtraction of `c` are handled by `AnalyticAt.mul_const` and `AnalyticAt.sub`. Transfer to the original pullback via `AnalyticAt.congr`.

6. **Recommended refactor — shared helper.** Introduce a general lemma decoupled from the specific `Elliptic` generators:
   ```lean
   private lemma analyticAt_torus_affine_arc {L : AddSubgroup ℂ} [DiscreteTopology L] [Rk2 L]
       (v : ℂ) (u : ℝ) (hu : u ∈ Set.Ioo (0:ℝ) 1) :
     AnalyticAt ℝ
       (fun r : ℝ =>
         (extChartAt 𝓘(ℂ) ((QuotientAddGroup.mk' L : ℂ → _) ((u:ℂ) * v)))
         ((QuotientAddGroup.mk' L : ℂ → _) ((r:ℂ) * v))) u
   ```
   Place this in `ComplexTorus.lean` (or a helper file) and instantiate with `v := ω₁` for `aLoop` and `v := ω₂` for `bLoop`. This cleanly abstracts the manifold/chart logic away from the elliptic curve and halves total LOC vs. duplicating the proof.

7. **Replace `axiom` with `theorem`** at `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:90-91`. Signature unchanged; `bArc` (`Witnesses.lean:108-119`) and `bLoop` (`Witnesses.lean:143-160`) continue to consume it.

**Files touched**
- `Jacobians/AbelianVariety/ComplexTorus.lean` — add the shared helper `analyticAt_torus_affine_arc`.
- `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` — replace `axiom AX_Elliptic_bLoop_analytic` (lines 90–91) with a `theorem` invoking the new helper.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Elliptic.Witnesses` succeeds.
- `#print axioms Jacobians.ProjectiveCurve.bArc` no longer lists `AX_Elliptic_bLoop_analytic`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (or by 2 if discharged jointly with `AX_Elliptic_aLoop_analytic`).

**Risk / escalation triggers**
- Privacy of `chartTarget` / `liftPoint` / `chartRadius` in `ComplexTorus.lean` preventing the helper proof.
- `AnalyticArc.partition` unexpectedly demanding one-sided analyticity rather than strict `Ioo 0 1` interior points (if the documentation diverges from definition).

### **`Gemini critique addressed:`**
- Reclassified route from `provable-from-other-axioms` to `mathlib-now`, as the theorem relies purely on existing Mathlib API and the local `ComplexTorus` setup.
- Expanded step 5 to explicitly document the required calculus tactics: `Complex.ofRealAm`, `ContinuousLinearMap.analyticAt`, `AnalyticAt.mul_const`, and `AnalyticAt.sub`.
- Abstracted the proposed shared helper (`analyticAt_torus_affine_arc`) to apply to any `ComplexTorus L` and an arbitrary vector `v : ℂ`, moving it logically to `ComplexTorus.lean` instead of hardcoding `ω₁` and `ω₂`.

---
**Vetting trail.** Critique: `_vetting/AX_Elliptic_bLoop_analytic.md`. Verdict: revise. Revised: 2026-06-03.