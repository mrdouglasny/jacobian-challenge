# Gemini 3.1 Pro critique — `Hyperelliptic`

**Model:** gemini-3.1-pro-preview
**Duration:** 131.1s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

An excellent, highly structural plan to bypass Lean 4's typeclass synthesis limitations around dependent if-then-else (`dite`). However, your proof recipe contains a few fatal Lean 4 anti-patterns regarding how data classes and `dite` equalities interact. 

Here is the critique:

1. **Route classification**: **needs-infra** is correct. This is purely architectural plumbing to resolve a known limitation of typeclass resolution on conditional types.
2. **Effort**: **5** is accurate. The boilerplate is contained, but handling the type equalities rigorously will require a bit more manual term-mode construction than you have estimated.
3. **Proof recipe**: Contains two critical logic flaws in Steps 3 and 4 (detailed below). 
4. **Textbook citations**: N/A. This is entirely an artifact of Lean 4's type theory.
5. **What's missing or wrong**:
   - **Data vs. Prop distinction (Step 3)**: You suggest using `rw` / `simp only [Hyperelliptic]` to lift all five instances. This is a fatal anti-pattern for `TopologicalSpace`. `TopologicalSpace` is a **data class**. If you use `rw` to rewrite the type inside a data class, Lean generates an `Eq.mpr` (or `Eq.rec`) that wraps the data fields (like `IsOpen`). This induces "cast hell," completely shattering definitional equalities and making it impossible to reason about open sets. 
     *Fix:* For `Prop`-valued classes (`T2Space`, `CompactSpace`, `ConnectedSpace`, `Nonempty`), your `rw` strategy is perfectly safe. For `TopologicalSpace`, you **must** build the instance in term mode without tactics, pulling back the topology along the underlying equivalence: 
     `TopologicalSpace.induced (Equiv.cast <| dif_pos h) inferInstance` (and similarly for `dif_neg`).
   - **Definitional equality of `dite` (Step 4)**: You state you will prove the homeomorphisms via `by_cases`-based `Homeomorph.refl`. This will not typecheck. In Lean, `dite (Odd H.f.natDegree) A B` does **not** definitionally reduce to `A` just because `h : Odd H.f.natDegree` is in the local context; it only reduces propositionally via the theorem `dif_pos h`. 
     *Fix:* You cannot use `Homeomorph.refl`. You must manually construct the homeomorphism using `Equiv.cast (dif_pos h)` as the underlying equivalence. Because you will have defined the topology via `induced` (as corrected in Step 3), the continuity proofs will be trivial.
   - **Downstream warning (Step 5)**: `ChartedSpace` is also a data class (it contains the manifold atlas). You cannot use `rw` there either. You will need to pull back the charted space along the homeomorphisms established in Step 4.

6. **Recommendation**: Revise. Implement the typecast topology fix for Step 3 and the explicit `Equiv.cast` homeomorphism fix for Step 4.

VERDICT: revise — Fix Steps 3 and 4 to avoid using `rw` on data classes (which causes `Eq.rec` hell) and to account for the fact that `dite` does not reduce definitionally in the local context.
