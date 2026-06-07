# Gemini 3.1 Pro critique — `AX_Hyperelliptic_oddEquiv`

**Model:** gemini-3.1-pro-preview
**Duration:** 42.7s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

Here is a critical review of the proposed discharge plan:

1. **Route classification**: `provable-from-other-axioms` is correct. The proof relies entirely on how the underlying `Hyperelliptic` type and its `TopologicalSpace` instance are finally defined.

2. **Effort 1..10**: The estimate of **2** is significantly under-calibrated. "Definitional once `Hyperelliptic` lands" is a trap. `dite` on types in Lean 4 mixed with typeclasses (like `TopologicalSpace`) leads straight to dependent-type hell. This is an **Effort 4** task due to the required topological casts.

3. **Proof recipe**: 
   - **Step 2 is logically flawed in Lean.** You cannot simply `rw [dif_pos h]` on a goal of type `Hyperelliptic H ≃ₜ HyperellipticOdd H h`. The type `Homeomorph α β` has implicit instance parameters: `@Homeomorph α β (instTopology α) (instTopology β)`. If you rewrite `α`, the rewrite will fail with the dreaded **"motive is not type correct"** error because `instTopology α` expects the un-rewritten type.
   - **Step 3 is incomplete.** `Homeomorph` is a structure that requires more than just `toFun` and `invFun`. The recipe completely omits the `continuous_toFun` and `continuous_invFun` fields. Proving that `cast (dif_pos h)` is continuous is highly non-trivial unless the `TopologicalSpace (Hyperelliptic H)` instance is *also* defined via `dite` *and* you use `HEq` or specific topology-transport lemmas to show the instances align. 

4. **Textbook citations**: N/A. This is a purely Lean-architectural lemma.

5. **What's missing or wrong**:
   - The plan treats `Homeomorph` as if it were `Equiv`, ignoring the topological fields in Step 3.
   - It ignores the fact that `Hyperelliptic.instTopologicalSpace` is currently an axiom. The continuity proofs in Step 3 will be strictly impossible unless the discharge of `Hyperelliptic.instTopologicalSpace` explicitly coordinates with this lemma (e.g., by being defined via the exact same `dite`).
   - The fallback to `Quotient (Sum ...)` in the risk section is actually mathematically cleaner for Lean than `dite` on types, as it avoids `HEq` topology casts entirely (using the coinduced sum topology). If `dite` fails, you should use `Sum` (since only one branch is actually valid per curve, you don't even need a quotient, just a subtype or standard sum).

6. **Recommendation**: Revise. The recipe must account for the `motive is not type correct` dependent-rewrite failure, explicitly include the `continuous_toFun` and `continuous_invFun` proofs, and define the exact coordination required with the `Hyperelliptic.instTopologicalSpace` definition to make those continuity proofs go through.

VERDICT: revise — The `rw [dif_pos h]` step will fail with "motive is not type correct" due to the implicit `TopologicalSpace` instances in `Homeomorph`, and the fallback in Step 3 omits the required (and notoriously difficult) continuity proofs for dependent type casts.
