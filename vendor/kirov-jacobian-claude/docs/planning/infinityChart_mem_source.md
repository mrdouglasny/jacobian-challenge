# `infinityChart_mem_source` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:62`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~1 hour, ~5 LOC (a one-liner once `infinityChart` is a real `def`)
**Blocked by:** `infinityChart`

**Statement (verbatim):**
```lean
/-- The infinity chart is defined at the point `∞`. -/
axiom infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source
```

**Why it's an axiom right now:** Pure consequence of the *future* definition of `infinityChart`: once `infinityChart` is a real `noncomputable def` (per `docs/planning/infinityChart.md`) whose `source` is constructed to *contain* `∞` (the docstring at `InfinityChart.lean:53` explicitly states "sending a neighborhood of `OnePoint.infty` to a neighborhood of `0 ∈ ℂ`, with `OnePoint.infty ↦ 0`"), this becomes immediate — `∞` is in `source` essentially by definition. The axiom only exists because `infinityChart` itself is an axiom: `axiom` cannot be unfolded, so `(infinityChart H h).source` has no extensional content yet.

**Proof recipe**

1. **Prerequisite — `infinityChart` is real.** Wait for `docs/planning/infinityChart.md` to be discharged. The recipe for `infinityChart` (Steps 3 + 7) constructs `source` so that it contains `∞`: specifically, in the formulation suggested there, `source := (infinityForward H h) ⁻¹' (Metric.ball 0 r) ∩ ((↑) '' (smoothLocusY H) ∪ {∞})`, and `infinityForward H h ∞ = 0 ∈ Metric.ball 0 r` since `r > 0`.

2. **Pick the discharge tactic based on the concrete `source` formulation.**
   - **If the recipe of `infinityChart` exposes a `@[simp]` lemma `infinityChart_source_eq` of the form `(infinityChart H h).source = ... ∪ {∞}`**, the proof is:
     ```lean
     theorem infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
         (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source := by
       rw [infinityChart_source_eq]
       exact Or.inr rfl     -- or `Set.mem_union_right _ rfl`, etc.
     ```
   - **If `source` is built via `(infinityForward H h) ⁻¹' (Metric.ball 0 r)` directly** (no helper simp lemma), the proof is:
     ```lean
     theorem infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
         (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source := by
       change infinityForward H h ∞ ∈ Metric.ball (0 : ℂ) (someRadius H h)
       simp [infinityForward, OnePoint.rec, Metric.mem_ball, someRadius_pos]
     ```
     citing `someRadius_pos : 0 < someRadius H h` (the positive-radius output from Step 3c of the `infinityInverseMap` recipe).

3. **Pattern reference.** This mirrors the existing `affineChartProjX_mem_source` at `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/AffineChart.lean:234` and `affineChartProjY_mem_source` at `:378` — both are short proofs that the chart contains its base point, both rely on a `ContDiffAt.mem_toPartialHomeomorph_source` cite or a direct unfolding of the source set definition.

4. **Discharge.** In `InfinityChart.lean:61–63`, replace
   ```lean
   axiom infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
       (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source
   ```
   with the `theorem` body from Step 2 (either branch). Signature unchanged.

**Next discrete deliverable.** The full discharge (Steps 2 + 4) is a single ~5 LOC PR. No sub-deliverables.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom infinityChart_mem_source ...` (lines 61–63) with a `theorem` body.
- (no other files)

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.InfinityChart` succeeds with the axiom replaced by a `theorem` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instChartedSpace` no longer lists `infinityChart_mem_source` (the consumer is `OddAtlas.lean:147`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `infinityChart` recipe's final `source` formulation makes `∞ ∈ source` not literally trivial (e.g. requires showing the chosen radius `someRadius H h > 0`, and the radius helper lemma is not exported), **escalate** — the cleanup is in the `infinityChart` recipe's API, not here, and the right fix is to add the missing `@[simp]` or radius-positivity helper to `InfinityChart.lean` rather than to do real work inside this recipe.
- If the recipe of `infinityChart` ends up defining `source := ∅` as a placeholder (e.g. while only partially discharged), this axiom *cannot* be proved as a `theorem` — escalate immediately rather than introducing a `sorry`.

**Cross-plan patch (2026-06-03):** Namespace standardised on Mathlib's `PartialHomeomorph` (the stale `OpenPartialHomeomorph` references were hallucinated).
