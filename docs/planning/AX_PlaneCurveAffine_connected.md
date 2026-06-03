# `AX_PlaneCurveAffine_connected` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:113`
**Route:** genuine-textbook &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** ~3-4 focused months, ~3000 LOC (requires massive missing topology/geometry infrastructure)
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** For a smooth plane curve of degree `≥ 3`
the affine patch is connected (irreducible variety in the classical
topology). For `d = 1, 2` (line, conic), may be one or two connected
components. This axiom is for `d ≥ 3`; callers at smaller degree
should use the genus-0 `ProjectiveLine` directly. -/
axiom AX_PlaneCurveAffine_connected (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_connected
```

**Why it's an axiom right now:** The docstring (`PlaneCurve.lean:108–112`) claims this is a "classical fact" but contains a crucial confusion between real and complex topology: it states $d=1,2$ may have 1 or 2 components. While true over $\mathbb{R}$, over $\mathbb{C}$ a smooth conic is $\mathbb{P}^1$ (a sphere) and its affine patch is a sphere minus 1 or 2 points, which is always connected. The affine patch of a smooth curve is connected for *all* $d \ge 1$. Connecting algebraic irreducibility to topological connectedness over $\mathbb{C}$ via monodromy requires a massive amount of missing topology and complex geometry infrastructure (covering spaces, path-lifting, fundamental groups, analytic continuation). It is axiomatized to unblock downstream API without a multi-month detour into Riemann surface covering theory.

**Proof recipe**

Follow **Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 2** (for smooth projective curves as connected Riemann surfaces) and general manifold topology. The algebraic/monodromy dictionary is a massive missing infrastructure gap in Mathlib, so we rely entirely on the real 2-manifold approach to avoid covering space theory.

1. **Correct the docstring.** The docstring at `Jacobians/ProjectiveCurve/PlaneCurve.lean:108–112` must be rewritten immediately. Remove the erroneous claim that conics have 1 or 2 components over $\mathbb{C}$. State clearly that smooth affine plane curves over $\mathbb{C}$ are connected for all $d \ge 1$, and remove the restriction that the axiom is only for $d \ge 3$.
2. **Topology lemma — finite punctures in 2D.** Formalize a general topology lemma in Mathlib: removing a finite set of points from a connected manifold of real dimension $\ge 2$ leaves it connected.
3. **Projective curve as a connected real 2-manifold.** Formalize that the projective smooth plane curve (using `H.h_smooth` at `PlaneCurve.lean:52` and `1 ≤ d` at `PlaneCurve.lean:47`) is a connected compact Riemann surface, and hence a connected real 2-manifold.
4. **Affine patch as a complement of finite points.** Show that `PlaneCurveAffine H` is exactly the projective curve minus the set of points at infinity (the intersection with the line $Z = 0$). By Bézout, this intersection is a finite set of points. (Support with `isClosed_carrier` at `PlaneCurve.lean:82` and `AX_PlaneCurveAffine_nonempty` at `PlaneCurve.lean:103`).
5. **Discharge.** Combine the pieces to replace the axiom at `PlaneCurve.lean:113` with a theorem. Provide `ConnectedSpace (PlaneCurveAffine H)` for all $d \ge 1$, satisfying the axiom exactly as written (which already lacks a $d \ge 3$ hypothesis) without breaking downstream API.

**Next discrete deliverable.** **Sub-step 2 alone** — Formalizing the purely topological lemma that a connected real 2-manifold minus a finite set of points remains connected. This is a standalone, highly valuable PR to Mathlib's topology/manifold library.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — fix the docstring at `PlaneCurve.lean:108–112`, eventually replace the axiom with a theorem.
- (new Mathlib PR) `Mathlib/Topology/Manifolds/` — new infrastructure for connectedness of punctured manifolds.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurve.instConnectedSpace` no longer lists `AX_PlaneCurveAffine_connected`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Proving the projective curve itself is connected (Sub-step 3) is a major project; if this requires GAGA or the Riemann Existence Theorem machinery not currently scoped, escalate to a human to leave this permanently axiomatized for the duration of the Jacobian challenge.

**Gemini critique addressed:**
- **Route and Effort Reclassification:** Upgraded from `provable-from-other-axioms` (Effort 5) to `genuine-textbook` (Effort 10, 3-4 months) to reflect the massive missing topology/geometry infrastructure identified in the critique.
- **Fundamental Approach Changed:** Abandoned the critically flawed monodromy/analytic-continuation approach (which lacked Mathlib fundamentals) in favor of the critique's recommended "real 2-manifold" topological approach.
- **Docstring/Math Error Corrected:** Addressed the confusion between real and complex topology regarding conics having 1 or 2 components. Added an explicit sub-step to fix the docstring and avoided needlessly restricting the signature to $d \ge 3$.

---
**Vetting trail.** Critique: `_vetting/AX_PlaneCurveAffine_connected.md`. Verdict: reject. Revised: 2026-06-03.