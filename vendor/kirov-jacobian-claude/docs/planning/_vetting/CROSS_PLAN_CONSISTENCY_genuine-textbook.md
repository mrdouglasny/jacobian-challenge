# Cross-plan consistency audit — 5 `genuine-textbook` plans

**Model:** gemini-3.1-pro-preview  (extended thinking)
**Duration:** 123.1s
**Plans audited:** 5
**Date:** 2026-06-03

---

## Finding 1 — Incompatible `IsManifold` model space signatures
**Plans involved:** `AX_pushforward_pullback`, `PlaneCurve.instIsManifold`
**Class:** signature
**Evidence:** 
`AX_pushforward_pullback` expects the complex manifold model space to be written as the single-argument `𝓘(ℂ)`:
```lean
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
```
`PlaneCurve.instIsManifold` provides the manifold instance using the two-argument Mathlib standard `𝓘(ℂ, ℂ)` (which represents `modelWithCornersSelf ℂ ℂ`):
```lean
axiom PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)
```
**Recommendation:** Standardize the model-with-corners notation across the project. Choose either the single-argument alias `𝓘(ℂ)` (if locally defined) or the explicit two-argument notation `𝓘(ℂ, ℂ)` to ensure generic manifold theorems like `AX_pushforward_pullback` successfully apply to concrete spaces like `PlaneCurve H` during typeclass synthesis without unification failures.

CROSS-PLAN VERDICT: 1 findings (1 actionable) — The plans reveal a structural signature split in the project's model-space notation (`𝓘(ℂ)` vs `𝓘(ℂ, ℂ)`) that will prevent generic manifold theorems from applying to concrete curves.
