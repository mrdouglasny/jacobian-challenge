# `AX_Elliptic_aLoop_analytic` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:86`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~1 focused day, ~60–100 LOC
**Blocked by:** none

**Statement (verbatim):**
```lean
axiom AX_Elliptic_aLoop_analytic :
    IsAnalyticArc (Elliptic ω₁ ω₂ h) (aLoopExtend ω₁ ω₂ h) {0, 1}
```

**Why it's an axiom right now:** `IsAnalyticArc` (`Jacobians/RiemannSurface/AnalyticArc.lean:54-59`) requires checking, for every interior `u ∈ Ioo s t` of the partition `{0, 1}`, that the chart pullback `r ↦ extChartAt 𝓘(ℂ, ℂ) (aLoopExtend u) (aLoopExtend r)` is real-analytic at `u`. The witness `aLoopExtend r = ⟦(r:ℂ) * ω₁⟧` (`Witnesses.lean:60-61`) is affine in `r` after lifting through the `ComplexTorus` chart, but the formal verification was deferred pending a clean atlas-local description of `(extChartAt 𝓘(ℂ, ℂ) p).symm` and `extChartAt 𝓘(ℂ, ℂ) p`. Those lemmas now exist as `extChartAt_symm_eq_quotient_mk` (`Jacobians/AbelianVariety/ComplexTorus.lean:164-171`) and `extChartAt_apply_quotient_mk` (`Jacobians/AbelianVariety/ComplexTorus.lean:265-268`), so the axiom is purely a packaging gap.

**Proof recipe**

This is `mathlib-now`: the chart-pullback is locally the affine map `r ↦ r * ω₁ + c` for a fixed constant `c`, and affine maps `ℝ → ℂ` are real-analytic.

1. **Unpack `IsAnalyticArc`.** Open the definition at `Jacobians/RiemannSurface/AnalyticArc.lean:54-59`. Instead of artificially restricting to `u ∈ Set.Ioo (0:ℝ) 1`, prove analyticity for an arbitrary `u : ℝ`. `aLoopExtend` is analytic on all of `ℝ`, so establishing `AnalyticAt ℝ f u` everywhere trivially satisfies whatever boundary/interior conditions `IsAnalyticArc` demands.

2. **Locate the point `aLoopExtend u`.** By definition (`Witnesses.lean:60-61`),
   `aLoopExtend ω₁ ω₂ h u = QuotientAddGroup.mk' L.toAddSubgroup ((u:ℂ) * ω₁)` where `L := ellipticLattice ω₁ ω₂ h`. Call this point `p`. We need analyticity at `u` of
   `f : ℝ → ℂ, f r := extChartAt 𝓘(ℂ, ℂ) p (aLoopExtend ω₁ ω₂ h r)`.

3. **Invoke the shared helper.** Rather than constructing a specialized wrapper, invoke the generalized helper `analyticAt_torus_affine_arc {L : AddSubgroup ℂ} [DiscreteTopology L] [Rk2 L]` defined per the recipe in `AX_Elliptic_bLoop_analytic.md` (step 6) and placed in `Jacobians/AbelianVariety/ComplexTorus.lean`. The helper abstracts the manifold/chart logic uniformly for both A-cycle and B-cycle proofs. Instantiate with `L := (ellipticLattice ω₁ ω₂ h).toAddSubgroup` and `v := ω₁`.

4. **Affine formula on the neighborhood (handled inside the helper).** The helper internally establishes that for `r` in a small real neighborhood of `u`,
   ```lean
   f =ᶠ[𝓝 u] fun r : ℝ => (r : ℂ) * ω₁ - c
   ```
   where `c` is the local lattice offset. No specialized wrapper lemma is needed at the A-cycle site.

5. **Conclude analyticity (handled inside the helper).** The helper expresses `r ↦ (r:ℂ) * v` via `ContinuousLinearMap.analyticAt` on a continuous `ℝ`-linear map, subtracts the constant `c` using `AnalyticAt.sub`, and transfers back to the chart pullback via `AnalyticAt.congr`. At the A-cycle call site, simply apply the helper with `v := ω₁`.

6. **Replace `axiom` with `theorem`** at `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:86-87`. The signature is unchanged; `aArc` (`Witnesses.lean:94-105`) and `aLoop` (`Witnesses.lean:123-140`) continue to consume it.

**Files touched**
- `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` — replace `axiom AX_Elliptic_aLoop_analytic` (lines 86–87) with a `theorem` that invokes the shared helper `analyticAt_torus_affine_arc`.
- `Jacobians/AbelianVariety/ComplexTorus.lean` — no edits at the A-cycle site; the shared helper `analyticAt_torus_affine_arc` is added per the `AX_Elliptic_bLoop_analytic` recipe.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Elliptic.Witnesses` succeeds.
- `#print axioms Jacobians.ProjectiveCurve.aArc` no longer lists `AX_Elliptic_aLoop_analytic`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `ContinuousLinearMap.analyticAt` is somehow unavailable or difficult to apply to this specific scalar multiplication instance, escalate to a human.
- If the shared helper `analyticAt_torus_affine_arc` (defined per `AX_Elliptic_bLoop_analytic.md`) cannot be instantiated cleanly at the A-cycle call site (e.g., due to typeclass resolution friction on `(ellipticLattice ω₁ ω₂ h).toAddSubgroup`), escalate.

### Gemini critique addressed:
- Changed Route from `provable-from-other-axioms` to `mathlib-now`.
- Generalized the initial reduction (Step 1) to an arbitrary `u : ℝ` instead of restricting to the open interval, correctly recognizing global real-analyticity.
- Promoted the `ContinuousLinearMap.analyticAt` formulation to the primary proof method (Step 5), eliminating the hallucinated `Complex.analyticAt_ofReal`.
- Turned the optional mitigation for `ComplexTorus.lean` privacy boundaries into a mandatory public wrapper lemma addition (Steps 3 & 4).

---
**Vetting trail.** Critique: `_vetting/AX_Elliptic_aLoop_analytic.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Dropped the specialized `extChartAt_eq_sub_lift_lattice_offset` wrapper in favor of invoking the generalized `analyticAt_torus_affine_arc` helper from `AX_Elliptic_bLoop_analytic`, per `_vetting/CROSS_PLAN_CONSISTENCY.md` Finding 1.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
