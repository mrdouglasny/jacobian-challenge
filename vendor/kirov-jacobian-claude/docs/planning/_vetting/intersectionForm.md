# Gemini 3.1 Pro critique — `intersectionForm`

**Model:** gemini-3.1-pro-preview
**Duration:** 60.6s
**Source axiom:** `Jacobians/Axioms/IntersectionForm.lean`
**Verdict:** **reject**

---

Here is the critique of the proposed axiom-discharge plan:

1. **Route classification**: The `needs-infra` classification is correct in spirit, but functionally vastly understated. This is a massive `genuine-textbook` black hole that effectively amounts to formalizing half of an algebraic topology textbook.
2. **Effort 1..10**: The estimate is utterly delusional. 3–4 weeks and 600–900 LOC to formalize singular cohomology, cup/cap products, manifold orientations, fundamental classes, Poincaré duality, and the Hurewicz theorem is pure fantasy. This is a 10/10 effort that requires 15,000+ LOC and many months (if not years) of expert work. 
3. **Proof recipe**: The recipe is mathematically standard but formally unmoored from reality. 
   - **Step 3 (Orientation/Fundamental Class)** trivially invokes $H_2(M; \mathbb{Z}) \cong \mathbb{Z}$. In Lean, this requires building local homology, orientation sheaves/coverings, and excision arguments. Mathlib cannot currently glue local manifold orientations into a singular fundamental class.
   - **Step 4 (Cup Product)** handwaves the Alexander-Whitney diagonal, which is notoriously combinatorial and brutal to formalize (often requiring acyclic models to prove associativity/graded-commutativity cleanly).
   - **Step 5 (Hurewicz)** casually assumes you can build the bridge between `FundamentalGroup` and singular 1-simplices, and prove it factors through the abelianization to yield an isomorphism. This is a massive missing theorem on its own.
4. **Textbook citations**: Hatcher and Griffiths-Harris are the correct mathematical references, but citing them hides the immense, gaping formalization chasm beneath the plan.
5. **What's missing or wrong**: The plan treats deep, structural theorems of algebraic topology as small lemmas. Singular homology in Mathlib is currently rudimentary. To reach Poincaré duality, you need a massive build-out of relative homology, long exact sequences, cap products, and direct limits over compact subsets. The "Risk" trigger ("if it spirals past ~1500 LOC") is guaranteed to hit before you even finish defining the orientation sheaf.
6. **Recommendation**: Reject. Acknowledge that the topological intersection form cannot be built from scratch in a short-term challenge project. Keep `intersectionForm` and its companion properties as axioms (or bundle them into a typeclass like `HasIntersectionForm`), which correctly delegates the missing topological infrastructure and preserves the logical integrity of the project.

VERDICT: reject — The plan massively underestimates the difficulty of formalizing Poincaré duality and cup products from scratch, which is a multi-month, 15,000+ LOC undertaking far beyond the scope of discharging a single axiom.
