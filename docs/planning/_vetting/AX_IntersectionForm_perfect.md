# Gemini 3.1 Pro critique — `AX_IntersectionForm_perfect`

**Model:** gemini-3.1-pro-preview
**Duration:** 71.4s
**Source axiom:** `Jacobians/Axioms/IntersectionForm.lean`
**Verdict:** **reject**

---

An expert review of your axiom-discharge plan for `AX_IntersectionForm_perfect` reveals a severe disconnect between the proposed proof steps and the actual state of Mathlib v4.30.

Here is the detailed critique:

1. **Route classification:** `needs-infra` is technically correct, but the scope of the missing infrastructure is so vast that treating this as a local project-level task is a misclassification. This is a major Mathlib-wide blocker. 
2. **Effort:** 7 (~2 weeks, 250–400 LOC) is a **hallucinatory underestimate**. You are off by at least two orders of magnitude. Formalizing the Universal Coefficient Theorem (UCT) for singular cohomology, defining cap products, orientability, fundamental classes, and proving Poincaré Duality for topological manifolds is an Effort 10+ undertaking that would take a dedicated team of experts many months, if not years.
3. **Proof recipe:**
   - The mathematical logic (Poincaré Duality + UCT = Perfect Pairing) is the correct textbook path.
   - **Logical gap (Finite Generation):** To actually extract a symplectic basis over $\mathbb{Z}$ (which you note this axiom is meant to enable), you need $H_1(X, \mathbb{Z})$ to be a *finitely generated free abelian group*. Your plan completely ignores the topological fact that compact manifolds have finitely generated homology. Without finite generation, unimodularity does not imply the existence of a finite symplectic basis. Finiteness of homology for compact manifolds is entirely missing from Mathlib.
   - **Lean Script Errors:** In Step 5, you write `hEv.comp hPD` expecting it to yield a `.bijective` field. The composition of two `AddEquiv`s in Lean is done via `AddEquiv.trans`, which trivially provides the bijectivity you need without falling back to `Function.Bijective_comp` on coerced `AddMonoidHom`s.
4. **Textbook citations:** Hatcher §3.3 (Thm 3.30) for Poincaré Duality and §3.1 (Thm 3.2) for UCT are exactly the right mathematical references for this argument.
5. **What's missing or wrong:**
   - **UCT & Ext:** You state that if UCT isn't in Mathlib, building `Ext` over $\mathbb{Z}$ will take ~200 LOC. You need the homological algebra mapping cone/short exact sequence machinery for the UCT of *chain complexes of free abelian groups*, not just the algebraic definition of `Ext`. This alone is a massive missing chunk.
   - **Poincaré Duality:** You treat `poincareDuality x₀` as something you can just conjure in a new file `PoincareDuality.lean`. Mathlib v4.30 does not have cap products, manifold orientations, local homology for fundamental classes, or any semblance of Poincaré Duality for singular homology. 
   - **Route alternatives:** You note the CW-complex polygon-gluing route as an escalation trigger. Be aware that the classification of surfaces (and proving a Riemann surface admits a triangulation/CW structure) is *also* entirely missing from Mathlib.

**Recommendation:** Reject. You must completely revise the effort estimate to an Effort 10 (multi-month epic) and drastically expand the dependency tree. Alternatively, if project rules allow, you should factor Poincaré Duality and Finite Generation of Homology out into their own formal axioms so this specific file's scope is strictly limited to the algebraic UCT-to-Intersection-Form deduction.

VERDICT: reject — The plan hallucinates that Poincaré Duality and the Universal Coefficient Theorem are trivial ~400 LOC extensions, ignoring that these are massive, multi-year missing Mathlib milestones.
