# `AX_Hyperelliptic_oddEquiv` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:93`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~2 days, ~50 LOC — topological dependent casts require careful instance matching to avoid motive errors.
**Blocked by:** `Hyperelliptic`, `Hyperelliptic.instTopologicalSpace`

**Statement (verbatim):**
```lean
axiom AX_Hyperelliptic_oddEquiv (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticOdd H h
```

**Why it's an axiom right now:** The unified type `Hyperelliptic H` is itself an `axiom` (`Hyperelliptic.lean:59`) precisely to dodge a typeclass-resolution failure on the would-be `dite`-based real `def`. Until the underlying type is real, no Lean-level equality of `Hyperelliptic H` with `HyperellipticOdd H h` is available, so the homeomorphism is asserted axiomatically as a "pin" that fixes the intended content (per the docstring at `Hyperelliptic.lean:50-58`). Once `Hyperelliptic` becomes the parity-dispatched `dite`, this homeomorphism is essentially the identity, but dependent topology casts make proving it strictly nontrivial.

**Proof recipe**

1. Discharge `Hyperelliptic` (`Hyperelliptic.md`) and `Hyperelliptic.instTopologicalSpace`. **Crucial Coordination:** The `Hyperelliptic.instTopologicalSpace` definition MUST be defined using the exact same `dite` over `Odd H.f.natDegree` as the base `Hyperelliptic` type. This ensures the topological spaces align definitionally in the branches.
2. A direct `rw [dif_pos h]` on the goal `Hyperelliptic H ≃ₜ HyperellipticOdd H h` will fail with the error **"motive is not type correct"**. This is because `Homeomorph α β` has implicit instance parameters `@Homeomorph α β (instTopology α) (instTopology β)`; rewriting `α` leaves the un-rewritten `instTopology α` stranded.
3. Instead, explicitly construct the `Homeomorph` by building the underlying `Equiv` via `Equiv.cast` and manually providing the continuity proofs:
   ```lean
   theorem AX_Hyperelliptic_oddEquiv
       (H : HyperellipticData) (h : Odd H.f.natDegree) :
       Hyperelliptic H ≃ₜ HyperellipticOdd H h := by
     -- Establish the type equality from the dite branch
     have hEq : Hyperelliptic H = HyperellipticOdd H h := by
       dsimp [Hyperelliptic]
       rw [dif_pos h]
     -- Construct the underlying equivalence
     let e : Hyperelliptic H ≃ HyperellipticOdd H h := Equiv.cast hEq
     -- Build the Homeomorph
     exact {
       toEquiv := e
       continuous_toFun := by
         -- With instTopologicalSpace sharing the exact dite, 
         -- this reduces to continuity of the identity/cast.
         -- Use cast_eq / HEq topology transport lemmas here.
         sorry
       continuous_invFun := by
         sorry
     }
   ```
4. Complete the `continuous_toFun` and `continuous_invFun` proofs. If `HyperellipticOdd H h`'s native instance (`Hyperelliptic/Basic.lean:143-144`) is properly matched by the `dite` in `Hyperelliptic.instTopologicalSpace`, these proofs can typically be solved by `subst hEq` (if generalized correctly) or by proving a helper lemma about `continuous_cast` when the topologies are propositionally equal.
5. Replace `axiom AX_Hyperelliptic_oddEquiv` (lines 91–94) with `theorem AX_Hyperelliptic_oddEquiv` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean`. Downstream consumers (notably the five `instX` recipes, the `instChartedSpace`/`instIsManifold` recipes, and `genus_Hyperelliptic_eq` chains) are unaffected since the API is unchanged.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace `axiom AX_Hyperelliptic_oddEquiv` at lines 91–94 with the explicitly constructed `theorem` resolving the `Homeomorph`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `AX_Hyperelliptic_oddEquiv`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `continuous_toFun` / `continuous_invFun` proofs become stuck due to intractable `HEq` topology casts, **escalate immediately**. The fallback is to abandon `dite` on types entirely and define `Hyperelliptic H` as a standard `Sum` type (or subtype). Since only one parity is valid per curve, the coinduced sum topology avoids dependent topology casts entirely.
- If the signature of `Hyperelliptic` changes (e.g. takes the parity hypothesis as an explicit argument), this homeomorphism becomes trivial-by-`rfl` directly.

### Gemini critique addressed:
- **Effort & Est recalibrated:** Increased Effort to 4 to reflect the notorious difficulty of dependent type/topology casts in Lean 4.
- **Motive error resolved:** Replaced the logically flawed `rw [dif_pos h]` step with an explicit construction of the `Homeomorph` structure using `Equiv.cast`.
- **Continuity fields added:** Explicitly included `continuous_toFun` and `continuous_invFun` requirements, demanding exact coordination with `Hyperelliptic.instTopologicalSpace`'s `dite` structure so the proofs are actually possible.
- **Fallback clarified:** Updated the risk section to identify `Sum` as mathematically cleaner for Lean precisely because it sidesteps these `HEq` topological issues.

**Note (signature pinning, 2026-06-03):** This axiom remains a topological `Homeomorph` (`≃ₜ`), *not* a biholomorphism. Cast-based homeomorphisms across the parity `dite` are already nontrivial; layering analytic structure on top here would over-couple this recipe with manifold infrastructure. Downstream consumers that need analytic transport (notably `AX_Hyperelliptic_genus`) must promote this `≃ₜ` to a biholomorphism *locally* at their use-site via a manifold-transport lemma — they may not assume an analytic upgrade lives in this base axiom.

---
**Vetting trail.** Critique: `_vetting/AX_Hyperelliptic_oddEquiv.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Equivalence signature pinned as Homeomorph (`≃ₜ`); `AX_Hyperelliptic_genus` promotes locally via manifold transport rather than changing this base signature.