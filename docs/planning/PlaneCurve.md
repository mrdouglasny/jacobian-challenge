# `PlaneCurve` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:161`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~5 minutes, 3 LOC
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Axiom-stub.** The smooth projective plane curve `{F = 0} ⊂ ℙ²`
as a type.

Classical construction: glue three affine charts `z ≠ 0`, `y ≠ 0`,
`x ≠ 0` along their pairwise overlaps. The resulting space is a
compact, connected, Hausdorff complex 1-manifold of genus
`(d - 1)(d - 2) / 2` (Plücker). Axiomatized with properly formulated
typeclass instances until the three-chart pushout is constructed. -/
axiom PlaneCurve (H : PlaneCurveData) : Type
```

**Why it's an axiom right now:** Initial logic and parameters are validated at `PlaneCurve.lean:128–151`. The axiom exists solely because previous iterations erroneously conflated the base topological definition of the curve in `ℙ²` with its manifold atlas assembly. 

**Proof recipe**

1. Define `PlaneCurve` as a subtype of `Projectivization` using `.rep` directly to eliminate quantification bridging:
```lean
def PlaneCurve (H : PlaneCurveData) : Type :=
  { p : Projectivization ℂ (Fin 3 → ℂ) // MvPolynomial.eval p.rep H.F.val = 0 }
```
2. Standard processing applied.
3. Replace `axiom PlaneCurve` with `def PlaneCurve` in `Jacobians/ProjectiveCurve/PlaneCurve.lean:161`.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace `axiom PlaneCurve` with the concrete `def` leveraging Mathlib's projective space API.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurve.instTopologicalSpace` (`PlaneCurve.lean:163`) no longer lists `PlaneCurve`; same for the other instance axioms in `PlaneCurve.lean:163–187` and downstream consumers (`Axioms/PluckerFormula.lean:55`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Mathlib API drift involving `Projectivization.rep` signatures.
- Signature change: If `PlaneCurve` ends up taking additional explicit hypotheses, downstream consumers break.

**Gemini critique addressed:**
- Reclassified route to `mathlib-now` and effort to `1`, separating the `Type` definition from the manifold structure.
- Adopted Option C exclusively to anchor the curve within `ℙ²`, preserving classical intersection theory.
- Fixed Lean 4 syntax by utilizing `Projectivization.rep` to circumvent invalid implication bindings.
- Excised the 600-LOC atlas assembly (former Steps 1-2) to downstream sub-plans.

## Sub-plans needed
- `PlaneCurve.instChartedSpace`: The three affine charts, pairwise transitions, and smooth manifold structure must be orchestrated here instead of the base `Type` axiom.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve.md`. Verdict: revise. Revised: 2026-06-03.