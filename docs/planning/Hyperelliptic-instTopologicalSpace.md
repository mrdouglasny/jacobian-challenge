# `Hyperelliptic.instTopologicalSpace` — discharge recipe

**SUBSUMED:** This instance is constructed inside the `Hyperelliptic` plan (Step 3). This file exists only to maintain the per-axiom ROADMAP row.

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:61`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 0 &nbsp;&nbsp; **Est:** subsumed
**Blocked by:** `Hyperelliptic`

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instTopologicalSpace
```

**Proof recipe**

Follows from `Hyperelliptic.md` Step 3 (`TopologicalSpace.induced (Equiv.cast <| dif_pos h) inferInstance`); no separate work.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — handled atomically with the `Hyperelliptic` landing.

**Acceptance**
- Discharged in the same commit that lands `Hyperelliptic.md`.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instTopologicalSpace.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Duplicate-effort resolved — `Hyperelliptic-instTopologicalSpace` is now an indexing stub pointing at `Hyperelliptic.md`'s Step 3.
