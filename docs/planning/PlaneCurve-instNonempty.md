# `PlaneCurve.instNonempty` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:178`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~30 minutes, ~5 LOC (once `PlaneCurve` is a real `def`)
**Blocked by:** `PlaneCurve`, `AX_PlaneCurveAffine_nonempty` (now a **theorem**, PR #92 — a usable lemma, not a blocking axiom)

**Statement (verbatim):**
```lean
axiom PlaneCurve.instNonempty (H : PlaneCurveData) : Nonempty (PlaneCurve H)
attribute [instance] PlaneCurve.instNonempty
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. The affine patch is already inhabited by `AX_PlaneCurveAffine_nonempty` (now a **theorem**, PR #92) at `PlaneCurve.lean:103–106`; the unified `PlaneCurve H` is its compactification, so the affine point maps to a point of `PlaneCurve H` via the canonical inclusion-into-central-chart map.

**Proof recipe**

1. Discharge after the required infrastructure `PlaneCurve` (`docs/planning/PlaneCurve.md`, effort 8) lands as the three-chart pushout/quotient. The prereq/model is the two-summand `HyperellipticEvenProj` quotient at `Jacobians/ProjectiveCurve/Hyperelliptic/Even.lean` extended to three summands `Sum (Sum AffineZ AffineY) AffineX`. Whatever the exact encoding, there will be a canonical map `centralCoe : PlaneCurveAffine H → PlaneCurve H` (the inclusion of the `z ≠ 0` patch).
2. Post-infra discharge sequence in one line:
   ```lean
   instance PlaneCurve.instNonempty (H : PlaneCurveData) :
       Nonempty (PlaneCurve H) :=
     Nonempty.map (centralCoe H) (AX_PlaneCurveAffine_nonempty H)
   ```
   (Or use a direct construction bypassing `map`: `let ⟨x⟩ := AX_PlaneCurveAffine_nonempty H; ⟨centralCoe H x⟩`).
3. The required `AX_PlaneCurveAffine_nonempty H : Nonempty (PlaneCurveAffine H)` is at `Jacobians/ProjectiveCurve/PlaneCurve.lean:103` (now a **theorem**, PR #92 — the construction above still works, just no longer axiom-backed) and already declared `[instance]` at line 106, so even `inferInstance` may close the goal once `centralCoe` is available.
4. Model recipe: the analogous `Nonempty (HyperellipticOdd H h)` instance, which lifts `Nonempty (HyperellipticAffine H)` through `OnePoint`'s coercion (the three-chart pattern uses inclusion of any one summand — the `z`-summand is the simplest).
5. Replace `axiom PlaneCurve.instNonempty` with `instance` in `PlaneCurve.lean`, drop the `attribute [instance]` at line 179.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 178–179 with a one-line `instance` lifting `AX_PlaneCurveAffine_nonempty` through the central-chart inclusion.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurveData.genus` no longer lists `PlaneCurve.instNonempty`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- None substantive; this is a one-line transport. If `PlaneCurve` somehow lands with an encoding that has no `PlaneCurveAffine H → PlaneCurve H` inclusion (e.g. a purely projective Proj-construction), substitute the equivalent map (`PlaneCurveProjective H → PlaneCurve H`) and use `AX_PlaneCurveAffine_nonempty` to construct the projective point first.

### **`Gemini critique addressed:`**
- Reclassified **Route** from `provable-from-other-axioms` to `needs-infra`, as the proof is fundamentally blocked by the construction of the pushout infrastructure and the `centralCoe` inclusion map.
- Fixed the reversed Lean 4 dot-notation syntax for `Nonempty.map` in the proof recipe. Replaced `(AX_PlaneCurveAffine_nonempty H).map (centralCoe H)` with the proper Mathlib-compliant application order: `Nonempty.map (centralCoe H) (AX_PlaneCurveAffine_nonempty H)`.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instNonempty.md`. Verdict: revise. Revised: 2026-06-03.