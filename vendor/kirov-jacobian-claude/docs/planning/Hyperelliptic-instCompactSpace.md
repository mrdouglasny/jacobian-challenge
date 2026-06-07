# `Hyperelliptic.instCompactSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:68`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~30 minutes, ~6 LOC
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`, `Hyperelliptic.instTopologicalSpace`

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instCompactSpace (H : HyperellipticData) :
    CompactSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instCompactSpace
```

**Why it's an axiom right now:** Stub mirroring `instTopologicalSpace`. Both parity branches are compact (`HyperellipticOdd` via `OnePoint`'s `CompactSpace` instance, `Basic.lean:149`; `HyperellipticEven = HyperellipticEvenProj`, compactness proved at `Even.lean:424–425`). Compactness transports through a homeomorphism.

**Proof recipe**

1. Discharge by parity dispatch, lifting through the homeomorphism axioms `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`). Mathlib's `Homeomorph.compactSpace` (or `Homeomorph.symm`) transports the instance:
   ```lean
   theorem Hyperelliptic.instCompactSpace (H : HyperellipticData) :
       CompactSpace (Hyperelliptic H) := by
     by_cases h : Odd H.f.natDegree
     · exact (AX_Hyperelliptic_oddEquiv H h).symm.compactSpace
     · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
       exact (AX_Hyperelliptic_evenEquiv H h).symm.compactSpace
   ```
2. Target instances:
   - `CompactSpace (HyperellipticOdd H h)` at `Hyperelliptic/Basic.lean:149` (via `OnePoint`).
   - `CompactSpace (HyperellipticEven H h)` at `Hyperelliptic.lean:36–39`, which delegates to `CompactSpace (HyperellipticEvenProj H)` proved at `Hyperelliptic/Even.lean:424` (requires `Fact (¬ Odd H.f.natDegree)`).
3. Replace `axiom Hyperelliptic.instCompactSpace` with an `instance` definition; drop the redundant `attribute [instance]` at `Hyperelliptic.lean:70`.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace lines 68–70 with an `instance` proved by parity dispatch + `Homeomorph.symm.compactSpace`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instCompactSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Homeomorph.compactSpace` is not the exact Mathlib name at the current pin (alternative: `CompactSpace.of_homeomorph`, or transferring via `IsCompact.image` on `Set.univ`), substitute the equivalent — the underlying fact is invariance under homeomorphism.
- If the `Even.lean:424` proof temporarily regresses to `sorry`, this recipe is blocked on its restoration.
