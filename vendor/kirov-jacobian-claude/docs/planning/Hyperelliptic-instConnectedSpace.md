# `Hyperelliptic.instConnectedSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:72`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~30 minutes, ~6 LOC
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`, `Hyperelliptic.instTopologicalSpace`, `AX_HyperellipticAffine_connected` (transitively, through the odd branch)

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instConnectedSpace (H : HyperellipticData) :
    ConnectedSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instConnectedSpace
```

**Why it's an axiom right now:** Stub mirroring `instTopologicalSpace`. Both parity branches are connected (`HyperellipticOdd` via `OnePoint`'s `ConnectedSpace` instance, `Basic.lean:155`, which transitively relies on `AX_HyperellipticAffine_connected`; `HyperellipticEven = HyperellipticEvenProj`, connectedness proved at `Even.lean:328–329`). Connectedness transports through homeomorphism.

**Proof recipe**

1. Discharge by parity dispatch, lifting through `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`). Mathlib's `Homeomorph.connectedSpace` / `Homeomorph.symm.connectedSpace` transfers `ConnectedSpace` along a homeo:
   ```lean
   theorem Hyperelliptic.instConnectedSpace (H : HyperellipticData) :
       ConnectedSpace (Hyperelliptic H) := by
     by_cases h : Odd H.f.natDegree
     · exact (AX_Hyperelliptic_oddEquiv H h).symm.connectedSpace
     · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
       exact (AX_Hyperelliptic_evenEquiv H h).symm.connectedSpace
   ```
2. Target instances:
   - `ConnectedSpace (HyperellipticOdd H h)` at `Hyperelliptic/Basic.lean:155` (via `OnePoint`, ultimately resting on `AX_HyperellipticAffine_connected`).
   - `ConnectedSpace (HyperellipticEven H h)` at `Hyperelliptic.lean:41–44`, which delegates to `ConnectedSpace (HyperellipticEvenProj H)` proved at `Hyperelliptic/Even.lean:328` (requires `Fact (¬ Odd H.f.natDegree)`).
3. Replace `axiom Hyperelliptic.instConnectedSpace` with an `instance` definition; drop the `attribute [instance]` line at `Hyperelliptic.lean:74`.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace lines 72–74 with an `instance` proved by parity dispatch + `Homeomorph.symm.connectedSpace`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instConnectedSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Homeomorph.connectedSpace` is not the exact Mathlib name at the current pin (alternative: `IsConnected.image` on `Set.univ`, or `ConnectedSpace.of_continuous_surjective` via `e.continuous` + `e.surjective`), substitute the equivalent — invariance under homeomorphism is the load-bearing fact.
- The odd branch is itself blocked on `AX_HyperellipticAffine_connected` (`Hyperelliptic/Basic.lean`, effort 6) for axiom-cleanness — this recipe can land while that axiom is still live, but `#print axioms` will list it as a dependency.
