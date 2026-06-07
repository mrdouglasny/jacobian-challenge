# `Hyperelliptic.instNonempty` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:76`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~20 minutes, ~5 LOC
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instNonempty (H : HyperellipticData) : Nonempty (Hyperelliptic H)
attribute [instance] Hyperelliptic.instNonempty
```

**Why it's an axiom right now:** Stub mirroring the other instance stubs. Both parity branches are nonempty (`HyperellipticOdd` via `OnePoint`'s `Nonempty` instance, `Basic.lean:152`; `HyperellipticEven = HyperellipticEvenProj`, nonempty proved at `Even.lean:287`). Nonemptiness transports along any function — in particular along the homeomorphism axioms.

**Proof recipe**

1. Discharge by parity dispatch, lifting through `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`). Since `Homeomorph` coerces to a function, `Nonempty.map` is the idiomatic way to push instances backwards through the equivalence:
   ```lean
   instance Hyperelliptic.instNonempty (H : HyperellipticData) :
       Nonempty (Hyperelliptic H) := by
     by_cases h : Odd H.f.natDegree
     · exact Nonempty.map (AX_Hyperelliptic_oddEquiv H h).symm inferInstance
     · exact Nonempty.map (AX_Hyperelliptic_evenEquiv H h).symm inferInstance
   ```
2. Target instances:
   - `Nonempty (HyperellipticOdd H h)` at `Hyperelliptic/Basic.lean:152` (via `OnePoint`).
   - `Nonempty (HyperellipticEven H h)` at `Hyperelliptic.lean:46–48`, which delegates to `Nonempty (HyperellipticEvenProj H)` proved at `Hyperelliptic/Even.lean:287`.
3. Replace `axiom Hyperelliptic.instNonempty` with the above `instance` definition; drop the `attribute [instance]` at `Hyperelliptic.lean:77`.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace lines 76–77 with an `instance` proved by parity dispatch + `Nonempty.map`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instNonempty`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If Lean fails to synthesize `inferInstance` in the `exact Nonempty.map ...` call, replace it with `(by infer_instance)` or fall back to extracting a witness explicitly: `obtain ⟨x⟩ := inferInstance (α := HyperellipticOdd H h); exact ⟨(AX_Hyperelliptic_oddEquiv H h).symm x⟩` (and analogous for the even branch).
- If either parity-side `Nonempty` instance regresses, this recipe blocks until restoration.

**`Gemini critique addressed:`**
- Changed definition from `theorem` to `instance` to properly register the `Nonempty` typeclass and eliminate downstream synthesis failures.
- Replaced the hallucinated `Equiv.nonempty` API call with idiomatic `Nonempty.map ... inferInstance`, utilizing `Homeomorph`'s coercion to function.
- Removed the unnecessary `haveI : Fact ...` wrapper in the even parity branch, as the downstream instance expects a standard explicit argument.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instNonempty.md`. Verdict: revise. Revised: 2026-06-03.