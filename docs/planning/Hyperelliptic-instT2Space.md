# `Hyperelliptic.instT2Space` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:65`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~30 minutes, ~6 LOC
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`, `Hyperelliptic.instTopologicalSpace`

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instT2Space (H : HyperellipticData) : T2Space (Hyperelliptic H)
attribute [instance] Hyperelliptic.instT2Space
```

**Why it's an axiom right now:** Stub mirroring `instTopologicalSpace`. Both parity branches are Hausdorff (`HyperellipticOdd` via `OnePoint`'s T2 instance, `Basic.lean:146`; `HyperellipticEven = HyperellipticEvenProj`, T2 proved at `Even.lean:1192`–end of proof). Transport across a homeomorphism preserves T2.

**Proof recipe**

1. Discharge by parity dispatch, lifting through the homeomorphism axioms `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`). Mathlib's `Homeomorph.t2Space` / `Homeomorph.symm.t2Space` transfers `T2Space` along a homeo:
   ```lean
   instance instT2Space (H : HyperellipticData) :
       T2Space (Hyperelliptic H) := by
     by_cases h : Odd H.f.natDegree
     · exact (AX_Hyperelliptic_oddEquiv H h).symm.t2Space
     · exact (AX_Hyperelliptic_evenEquiv H h).symm.t2Space
   ```
2. Target instances:
   - `T2Space (HyperellipticOdd H h)` at `Hyperelliptic/Basic.lean:146` (via `OnePoint`).
   - `T2Space (HyperellipticEven H h)` at `Hyperelliptic.lean:31–34`, which delegates to `T2Space (HyperellipticEvenProj H)` proved at `Hyperelliptic/Even.lean:1192`. Lean's typeclass resolution resolves the target inherently via the underlying type.
3. Replace `axiom Hyperelliptic.instT2Space` with an `instance` definition; drop the `attribute [instance]` at `Hyperelliptic.lean:66`.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace lines 65–66 with an `instance` proved by parity dispatch + `Homeomorph.symm.t2Space`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instT2Space`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Homeomorph.t2Space` is not the exact Mathlib lemma name at the current pin (alternative spellings: `Homeomorph.t2Space_iff`, `T2Space.of_homeo`), substitute the equivalent — the structural argument (T2 is invariant under homeomorphism) is bulletproof.

**Gemini critique addressed:**
- Replaced the `theorem` keyword with `instance` in the code block to ensure proper typeclass resolution without unidiomatic attributes.
- Deleted the redundant `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩` from the Even branch in the proof snippet.
- Removed text in Step 2 and the risk triggers regarding the `Fact` shim, as typeclass synthesis succeeds directly via the standard arguments of exported `HyperellipticEven` instances.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instT2Space.md`. Verdict: revise. Revised: 2026-06-03.