# Gemini 3.1 Pro critique — `AX_pushforward_contMDiff`

**Model:** gemini-3.1-pro-preview
**Duration:** 77.2s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed discharge plan.

1. **Route classification**: **Incorrect**. You classified this as `provable-from-other-axioms` and claimed it is blocked by `AX_pushforwardAmbient_preserves_lattice`. This fundamentally misunderstands how Lean handles axioms. An `axiom` is just a constant in the environment. The function `pushforwardImpl` is already fully defined and typechecks *today* (by passing the unproven axiom as a term). You can prove its smoothness right now without knowing *why* the axiom is true. The correct route is **`needs-infra`** (or `mathlib-now`), because the core task is building generic manifold infrastructure for torus quotients. It is strictly unblocked. 

2. **Effort 1..10**: **4** is calibrated, perhaps tilting to a 5. Manually charting out quotient manifolds in Mathlib is notoriously tedious, and you are building a generic functoriality lemma for `ComplexTorus`.

3. **Proof recipe**:
   - The overall reduction to `ComplexTorus`-level smoothness (Steps 1, 2, and 4) is correct.
   - **Logical Gap in Step 3**: You claim that the local lift of the quotient map is "literally `L : V → W`... up to a constant lattice-translation correction". Mathematically, yes. In Lean, this is a massive trap. To prove the translation is constant, you must explicitly construct the difference map `x ↦ lift(map(x)) - L(x)`, prove that it is continuous, prove that it lands in the lattice, and invoke a theorem that a continuous map from a connected space to a discrete space is (locally) constant. Your recipe completely skips this topological rigidity argument, which is where 80% of the pain of this proof will actually live.
   - You correctly identified the risk of global gluing if the charts don't behave nicely, which is a good failsafe. 

4. **Textbook citations**: N/A. This is purely a formalization infrastructure task about smooth structures on quotient manifolds. 

5. **What's missing or wrong**:
   - The route and blocker status are completely wrong. Remove the blocker.
   - The plan for Step 3 glosses over the topological rigidity argument required to prove that the difference between the local lift and the linear map is a constant. You need to explicitly plan to prove that a continuous map into a discrete subgroup is locally constant. 

6. **Recommendation**: **Revise**. Fix the route classification to `needs-infra`, remove the dependency blocker since axioms act as valid constants, and flesh out the topological rigidity step required to make Step 3 actually compile in Mathlib.

VERDICT: revise — Change the route to `needs-infra` and remove the blocker (since Lean can reason about definitions containing axioms immediately), and explicitly add the topological locally-constant argument needed for Step 3.
