# Gemini 3.1 Pro critique — `Hyperelliptic-instTopologicalSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 34.6s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**: **Incorrect**. The plan claims `provable-from-other-axioms`, but it should be `needs-infra` (specifically, blocked by the real definition of the `Hyperelliptic` type). You cannot extract a topology from a homeomorphism axiom when stating the homeomorphism axiom requires the topology to already exist.
2. **Effort 1..10**: **Ill-calibrated**. The proposed approach is technically impossible in Lean, making the current effort infinite. Once the `Hyperelliptic` type is properly defined, the effort to define its topology will be a 1 or 2. 
3. **Proof recipe**: **FATALLY FLAWED due to a cyclic dependency**. The recipe proposes to define `Hyperelliptic.instTopologicalSpace` using `AX_Hyperelliptic_oddEquiv`. However, in Lean 4, `Homeomorph α β` (denoted `α ≃ₜ β`) explicitly requires `[TopologicalSpace α]` and `[TopologicalSpace β]` as typeclass arguments. If you attempt to define the instance using the `Homeomorph`, where does the `Homeomorph` axiom get the topology for its domain? It either fails to elaborate, or you create a strict cycle. You absolutely cannot use a `Homeomorph` to bootstrap the very topology its signature relies upon. 
4. **Textbook citations**: N/A. This is a purely Lean-architectural issue.
5. **What's missing or wrong**:
   - The author fundamental misunderstands how `Homeomorph` is defined in Mathlib. It is a structure that *extends* `Equiv`, assuming the topologies already exist; it does not generate them.
   - The plan attempts to artificially decouple the discharge of `Hyperelliptic.instTopologicalSpace` from the un-stubbing of the `Hyperelliptic` type. This is impossible. This instance **must** be defined simultaneously with the `Hyperelliptic` type. 
   - When `Hyperelliptic` is turned into a proper `def` (e.g., an inductive type or a one-field structure wrapping the parity dispatch to avoid the mentioned `dite` typeclass inference issues), the `TopologicalSpace` instance must be built structurally on that definition.
6. **Recommendation**: **Reject**. Do not attempt to use `AX_Hyperelliptic_oddEquiv` to define this instance. Wait for `Hyperelliptic` to be implemented as a real `def`, and write a genuine instance that matches its underlying data structure.

VERDICT: reject — The proof recipe creates a fatal cyclic dependency because Lean's `Homeomorph` requires the `TopologicalSpace` instance to already exist in order to be stated.
