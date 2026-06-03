# Gemini 3.1 Pro critique — `Hyperelliptic-instConnectedSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 46.1s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **accept**

---

This is a textbook example of a well-scoped, thoroughly researched axiom discharge plan. The route classification is completely accurate: this is purely structural plumbing between axioms (the homeomorphisms) and existing topological instances. 

Here is the critique:

1. **Route classification**: `provable-from-other-axioms` is exactly right. The connectedness of the unified type trivially reduces to the connectedness of its parity-dispatch components via the homeomorphism axioms.
2. **Effort**: 1 is perfectly calibrated. This is a trivial bridging proof that will take a few minutes.
3. **Proof recipe**: The recipe is logically sound and correctly identifies the dependencies. 
   * **Minor Syntax Flaw**: In your code block, you used `theorem Hyperelliptic.instConnectedSpace ...`, but your text correctly states "Replace `axiom`... with an `instance` definition". If you drop the `attribute [instance]` line as planned, you *must* use `instance` instead of `theorem`, otherwise typeclass synthesis will lose access to the fact.
   * **Mathlib Risk Mitigation**: Your risk assessment regarding `Homeomorph.connectedSpace` is spot-on. In Mathlib 4, `ConnectedSpace` is a `Prop`-valued typeclass containing `isPreconnected_univ` (and extending `Nonempty`). There is no dot-notation theorem `Homeomorph.connectedSpace`. The canonical transfer is often done manually via `e.symm.range_eq_univ` + `isPreconnected_range e.symm.continuous`. (Note: the `Nonempty` field of the class is already handled by `Hyperelliptic.instNonempty` which is present in the file).
4. **Textbook citations**: N/A for formal structural gluing.
5. **What's missing or wrong**: Nothing structural. Just change `theorem` to `instance` in your snippet to match your own text, and be prepared to write a 3-liner using `isPreconnected_range` if the direct transfer lemma isn't mapped in Mathlib 4.30.

VERDICT: accept — The plan correctly identifies that transferring the property via the already-axiomatized parity homeomorphisms is the exact right path, requiring only a minor correction to use `instance` instead of `theorem` in the code block.
