# `contDiffOn_symm_toOpenPartialHomeomorph` — discharge recipe

**Location:** `Jacobians/GeneralResults/InverseFunctionTheorem.lean:9`
**Route:** mathlib-now (after a Gemini-recommended signature change — original axiom statement was mathematically false; see "Gemini critique addressed") &nbsp;&nbsp; **Effort:** 6 (vetted ↑ from 4) &nbsp;&nbsp; **Est:** ~3 focused days, ~150 LOC spread across this file and downstream consumers
**Blocked by:** none

**Statement (verbatim):**
```lean
-- REVISED REQUIRED (original statement was mathematically false):
theorem contDiffOn_symm_toOpenPartialHomeomorph
    {f : ℂ → ℂ} {a : ℂ} {f' : ℂ ≃L[ℂ] ℂ}
    (hf : ContDiffAt ℂ ω f a) (hf' : HasFDerivAt f (f' : ℂ →L[ℂ] ℂ) a) (hn : ω ≠ 0) :
    let e := hf.toOpenPartialHomeomorph f hf' hn
    ∃ V ⊆ e.target, IsOpen V ∧ f a ∈ V ∧ ContDiffOn ℂ ω e.symm V
```

**Why it's an axiom right now:** The original axiom attempted to bundle an upgrade to global smoothness on the entire `e.target` of the inverse branch. However, as `toOpenPartialHomeomorph` constructs its domain radius based purely on Lipschitz bounds, `e.source` is oblivious to the analyticity radius of `f`. Thus, the original statement asserting smoothness on all of `e.target` was mathematically false. It remains an axiom placeholder until the statement is weakened to an existential over a valid sub-neighborhood, and downstream consumers are adjusted.

**Gemini critique addressed:**
- **Route reclassified:** Changed from `mathlib-now` to `revise` because the original statement was false and requires a signature change.
- **Effort recalibrated:** Increased from 4 to 6 (and 1 day to 3 days) to account for the necessary refactoring of downstream consumers that relied on the full-target output.
- **Signature fixed:** Replaced the full-target `ContDiffOn` requirement with the recommended `∃ V ⊆ e.target...` localized version.
- **Recipe replaced:** Discarded the logically broken tactic script and the unhelpful "Option (b)" Mathlib PR. Wrote a new recipe that explicitly intersects the IFT ball with the analyticity neighborhood to construct `V`.

**Proof recipe**

1. Replace the existing mathematically false `axiom` in `Jacobians/GeneralResults/InverseFunctionTheorem.lean` with the revised `theorem` signature above.

2. Unfold `e := hf.toOpenPartialHomeomorph f hf' hn`. Note that `a ∈ e.source` and `e a = f a ∈ e.target`. Since `n = ω`, `hf` yields `AnalyticAt ℂ f a`. By `AnalyticAt.exists_ball_analyticOn` (or similar in `Mathlib/Analysis/Analytic/Basic.lean`), extract an open neighborhood `U` containing `a` on which `f` is `AnalyticOn`.

3. Construct the valid source neighborhood `W`. Define `W := e.source ∩ U ∩ {x | fderiv ℂ f x ≠ 0}`.
   - `W` is open because it's the intersection of open sets: `e.source` is open (`e.open_source`), `U` is open, and `fderiv ℂ f` is continuous on analytic domains (cite `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:261` for `AnalyticOnNhd.fderiv`).
   - `a ∈ W` because `a ∈ e.source`, `a ∈ U`, and `hf'` ensures `fderiv ℂ f a = f' ≠ 0`.

4. Define the target sub-neighborhood `V := e.target ∩ e.symm ⁻¹' W`.
   - `V ⊆ e.target` trivially holds.
   - `IsOpen V` holds by continuity of `e.symm` on `e.target` (cite `Mathlib/Topology/OpenPartialHomeomorph/Defs.lean:57` for `OpenPartialHomeomorph.continuousOn_symm`).
   - `f a ∈ V` because `f a = e a` and `e.symm (e a) = a ∈ W`.

5. Prove `ContDiffOn ℂ ω e.symm V` using `IsOpen.contDiffOn_iff` (cite `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:948` for `IsOpen.contDiffOn_iff`). For any `y ∈ V`, let `x = e.symm y`. By definition, `x ∈ W`, meaning `x ∈ e.source`, `x ∈ U` (so `f` is analytic at `x`), and `fderiv ℂ f x ≠ 0`.
   - Analyticity implies smoothness: cite `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:976` (`AnalyticAt.contDiffAt`).
   - Differentiability gives `HasFDerivAt f (fderiv ℂ f x) x`.
   - Wrap the non-zero scalar derivative `fderiv ℂ f x` as an equiv `ℂ ≃L[ℂ] ℂ`.
   - Apply Mathlib's pointwise symmetric rule (cite `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:893–900` for `OpenPartialHomeomorph.contDiffAt_symm`) to conclude `ContDiffAt ℂ ω e.symm y`.

6. **Downstream Fixes**: Traverse the project for callers of `contDiffOn_symm_toOpenPartialHomeomorph` (`squareLocalHomeomorph_zero_notMem_source` and `polynomialLocalHomeomorph_no_critical_in_source` in `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean`). Update them to extract `V` from this theorem's existential, and restrict their own working target sets to `V` instead of assuming full smoothness on `e.target`.

**Files touched**
- `Jacobians/GeneralResults/InverseFunctionTheorem.lean` — replace `axiom contDiffOn_symm_toOpenPartialHomeomorph` with the revised `theorem` signature and the correct existential proof.
- `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` — update `squareLocalHomeomorph_zero_notMem_source` and `polynomialLocalHomeomorph_no_critical_in_source` to handle the weakened `∃ V` signature.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm` succeeds.
- `#print axioms contDiffOn_symm_toOpenPartialHomeomorph` no longer lists itself (i.e., the declaration is now a theorem).
- `#print axioms` of the downstream consumers (`squareLocalHomeomorph_zero_notMem_source`, etc.) no longer lists `contDiffOn_symm_toOpenPartialHomeomorph`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Downstream consumers (`squareLocalHomeomorph_zero_notMem_source`, etc.) inherently require the strict global Lipschitz radius provided by `toOpenPartialHomeomorph` and cannot be straightforwardly localized to `V`.
- The 1-D `fderiv ≠ 0` → `ℂ ≃L[ℂ] ℂ` packaging requires an existing Mathlib constructor; if none of `LinearEquiv.smulOfNeZero`, `ContinuousLinearEquiv.equivOfInverse`, or `Units.continuousLinearEquiv` can be made to fit in ≤ 10 lines, escalate.

---
**Vetting trail.** Critique: `_vetting/contDiffOn_symm_toOpenPartialHomeomorph.md`. Verdict: reject. Revised: 2026-06-03.