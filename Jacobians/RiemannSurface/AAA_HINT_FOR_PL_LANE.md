# ⚠ MESSAGE TO THE PL-APPROX AGENT (from the coordinating session) — read me, do NOT commit me

You are on the right track. An expert review (Gemini deep-think) just certified your
piecewise-linear-in-charts route as **"mathematically bulletproof, the definitive path."**
Keep going — no Whitney, no Grauert, no re-architecture needed. Two things:

## 1. The ONE subtlety, and its exact fix (this is probably what you're fighting)

If `IsAnalyticArcStrong`'s witness requires the affine segment to be real-analytic on an
**open interval extending slightly past** `[tᵢ, tᵢ₊₁]`, the extended segment must not exit
the chart. **Do NOT apply the Lebesgue-number lemma to the maximal chart domains.** Instead:

- Take each chart biholomorphic to an open disk of radius 2, `D₂`.
- Let `Vⱼ := preimage of the concentric disk of radius 1`, `D₁`.
- Apply the **Lebesgue-number lemma to the shrunken cover `{Vⱼ}`**.
- A segment whose endpoints lie in `Vⱼ` lies entirely in the **strictly convex `D₁`**, and
  its slight analytic extension past the endpoints stays safely inside `D₂` (a valid chart
  domain). So the witness `f` (the affine map, or its read-through-another-chart =
  holomorphic-transition ∘ affine) is real-analytic on an open `U ⊇ Icc` inside the chart.

Mathlib handles the metric pieces well (`Metric.ball` convexity, Lebesgue number,
`IsCompact.exists_...`). The affine segment is `degree-1 polynomial` ⇒ `AnalyticOnNhd ℝ` on
all of ℝ; composed with a holomorphic chart transition it stays real-analytic.

## 2. Reassurances / guardrails

- `AnalyticLoop`/`AnalyticArc` is **piecewise**-analytic — **corners ARE allowed** at the
  finite partition points. Do not try to make the loop globally smooth or globally analytic;
  that's the trap that needs Whitney/Grauert. Corners at the segment junctions are fine.
- The homotopy engine is already proven and standard-3: `Path.homotopic_of_extChartLocal`
  (two paths in one chart with connecting segments inside the target ⇒ homotopic) and
  `Path.homotopic_of_chain`. Use the shrunken cover so the `hseg` hypothesis (segments stay
  in the chart target) is automatic from convexity of `D₁`.
- **Goal:** `AnalyticLoopsGenerateH1 x₀` UNCONDITIONAL, `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` only (no `AX_PeriodCycleBasis`, no Whitney/Grauert
  hypothesis). That single unconditional standard-3 result is the deliverable.
- If you genuinely cannot close some sub-step, name it as a precise lemma with status —
  do NOT introduce a `sorry` or a new `axiom`.

Full context: `docs/planning/AXIOM_FREE_REMAINING_ISSUE.md` §3.5 and §8 (on `origin/main`).
