# `Hyperelliptic.instTopologicalSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:61`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 2 &nbsp;&nbsp; **Est:** ~30 minutes (post-infra), ~10 LOC
**Blocked by:** `Hyperelliptic`

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instTopologicalSpace (H : HyperellipticData) :
    TopologicalSpace (Hyperelliptic H)
attribute [instance] Hyperelliptic.instTopologicalSpace
```

**Why it's an axiom right now:** Stub forced by the axiomatic `Hyperelliptic` type. Both parity branches already carry `TopologicalSpace` instances (`HyperellipticOdd` at `Hyperelliptic/Basic.lean:143`, `HyperellipticEven` at `Hyperelliptic/Even.lean:282`); the unified instance must wait for the actual structural definition of the `Hyperelliptic` type to be completed, as a topology cannot be bootstrapped from homeomorphism axioms without creating a cyclic dependency.

**Proof recipe**

1. Wait for the `Hyperelliptic` type itself to be implemented as a real `def` (this is the bounding infrastructure piece).
2. The prerequisite topological spaces for the parity branches already exist: `TopologicalSpace (HyperellipticOdd H h)` (`Hyperelliptic/Basic.lean:143`) and `TopologicalSpace (HyperellipticEven H h)` (`Hyperelliptic/Even.lean:282`), which is ultimately from `HyperellipticEvenProj`.
3. Post-infra discharge: Define the unified topology structurally based on how the `Hyperelliptic` type is implemented:
   - If `Hyperelliptic` is an inductive type (like `Sum`), lift the topology using Lean's standard topological constructors (e.g., `instTopologicalSpaceSum`).
   - If `Hyperelliptic` is a structure wrapping a `dite` or a dependent parity dispatch, define the instance by cases on `Odd H.f.natDegree` and use `TopologicalSpace.induced` mapping into the respective parity branch.
4. Replace `axiom Hyperelliptic.instTopologicalSpace` with `instance Hyperelliptic.instTopologicalSpace` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean` (and drop the now-redundant `attribute [instance]` line at `:63`).

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace lines 61–63 with a real `instance` defined structurally on the new `Hyperelliptic` type.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Jacobians/ProjectiveCurve/Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instTopologicalSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The underlying `Hyperelliptic` type definition becomes computationally intractable for typeclass inference, requiring a redesign of how parity is unified.
- The parity branch topologies (`HyperellipticOdd` or `HyperellipticEven`) are found to be missing or failing typeclass inference when the unification is attempted.

### Gemini critique addressed:
- **Route reclassification:** Changed route from `provable-from-other-axioms` to `needs-infra` since the instance fundamentally requires the concrete structural definition of `Hyperelliptic`.
- **Cyclic dependency eliminated:** Removed the fatal flaw of attempting to bootstrap a `TopologicalSpace` from a `Homeomorph` axiom (since `Homeomorph` requires the `TopologicalSpace` to already exist).
- **Effort recalibrated:** Set effort to 2, strictly blocked by the `Hyperelliptic` definition itself.
- **Recipe rewritten:** The recipe now correctly directs the developer to wait for the definition of `Hyperelliptic` and to build the topological space structurally on top of it.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instTopologicalSpace.md`. Verdict: reject. Revised: 2026-06-03.