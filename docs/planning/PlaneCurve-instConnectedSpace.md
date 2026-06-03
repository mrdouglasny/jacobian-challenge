# `PlaneCurve.instConnectedSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:174`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~2–3 focused days, ~50 LOC (once `PlaneCurve` lands)
**Blocked by:** `PlaneCurve`, `AX_PlaneCurveAffine_connected`

**Statement (verbatim):**
```lean
axiom PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instConnectedSpace
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. The classical-topology connectedness of a smooth projective plane curve follows from the connectedness of its standard affine charts (already an axiom: `AX_PlaneCurveAffine_connected` at `PlaneCurve.lean:113–116`) and the fact that these charts have nonempty pairwise intersections.

**Proof recipe**

1. Discharge after `PlaneCurve` (`docs/planning/PlaneCurve.md`, effort 8) lands as a space covered by three affine charts. Let's call their images in the projective curve $U_x, U_y, U_z$.
2. The discharge relies on the union of overlapping connected sets:
   - Step A — Each chart image is **connected** as the continuous image of `PlaneCurveAffine H` (or permutations of variables), which is connected by `AX_PlaneCurveAffine_connected` at `Jacobians/ProjectiveCurve/PlaneCurve.lean:113`. Cite `isConnected_range` (Mathlib `Mathlib/Topology/Connected/Basic.lean`).
   - Step B — The pairwise overlaps ($U_x \cap U_y$, etc.) are **nonempty**. Finding a single point in an overlap (e.g., coordinates where $X \neq 0 \wedge Y \neq 0$) is an elementary algebraic evaluation. This avoids closures and density entirely.
   - Step C — Since the charts cover the space, are individually connected, and pairwise intersect, their union (the whole space) is connected via Mathlib's `IsConnected.union`.
3. Tactic-level sketch:
   ```lean
   instance PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
       ConnectedSpace (PlaneCurve H) := by
     -- Assuming U_x, U_y, U_z are the three standard affine chart ranges
     have hX : IsConnected U_x := isConnected_range (chartX_continuous H)
     have hY : IsConnected U_y := isConnected_range (chartY_continuous H)
     have hZ : IsConnected U_z := isConnected_range (chartZ_continuous H)
     -- algebraic witnesses for overlap
     have hXY_nonempty : (U_x ∩ U_y).Nonempty := chartX_inter_chartY_nonempty H
     have hXY : IsConnected (U_x ∪ U_y) := hX.union hY hXY_nonempty
     have hXYZ_nonempty : ((U_x ∪ U_y) ∩ U_z).Nonempty := chartXY_inter_chartZ_nonempty H
     have hUniv : IsConnected Set.univ := by
       have hCover : U_x ∪ U_y ∪ U_z = Set.univ := planeCurve_covered H
       rw [← hCover]
       exact hXY.union hZ hXYZ_nonempty
     exact isConnected_univ_iff.mp hUniv
   ```
   (Adjust to the specific manifold/atlas API chosen for `PlaneCurve`).
4. Replace `axiom PlaneCurve.instConnectedSpace` with `instance` in `PlaneCurve.lean`, drop the `attribute [instance]` at line 176.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 174–176 with an `instance` proved by `IsConnected.union` over the three overlapping affine charts.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurveData.genus` no longer lists `PlaneCurve.instConnectedSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `AX_PlaneCurveAffine_connected` ever weakens to a `d ≥ 3`-only statement (it already excludes `d = 1, 2` per `PlaneCurve.lean:108–112`), this recipe must be guarded by the same degree hypothesis, and `d = 1, 2` need their own connectedness route (the line is `ProjectiveLine`, the conic is `ProjectiveLine` after `ℙ¹ ≅ smooth conic`).
- If finding explicit algebraic points to witness chart overlaps (`chartX_inter_chartY_nonempty`) is surprisingly difficult due to the curve equation, fall back to a generic algebraic geometry lemma showing Zariski-open sets in irreducible varieties always intersect.

### Gemini critique addressed:
- **Removed false compactness claim:** Removed the mathematically incorrect assertion that compactness of the ambient space is required to prove the affine patch is dense.
- **Promoted overlapping charts strategy:** Replaced the closure/density strategy with the critique's recommended fallback—taking the union of overlapping connected open charts. This completely bypasses formalizing that cofinite sets are dense (`centralChart_dense`).
- **Fixed `IsConnected` API hallucination:** Updated the tactic sketch to correctly treat `IsConnected` as a `Prop` rather than a `Set`, utilizing `isConnected_range`, `IsConnected.union`, and `isConnected_univ_iff.mp` according to proper Lean 4 Mathlib idioms.
- **Updated Blockers:** Removed `PlaneCurve.instCompactSpace` from the "Blocked by" list and estimate, as compactness is no longer part of the proof path.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instConnectedSpace.md`. Verdict: revise. Revised: 2026-06-03.