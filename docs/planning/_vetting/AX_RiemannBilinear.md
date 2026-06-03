# Gemini 3.1 Pro critique — `AX_RiemannBilinear`

**Model:** gemini-3.1-pro-preview
**Duration:** 32.5s
**Source axiom:** `Jacobians/Axioms/RiemannBilinear.lean`
**Note:** flag: mathlib-now but Hodge+Stokes are missing infra
**Verdict:** **revise**

---

Here is a referee-level critique of the proposed axiom-discharge plan:

1. **Route classification**: Re-classifying from `mathlib-now` to `genuine-textbook` is **correct**. The Riemann bilinear relations require a massive amount of missing machinery (integration of differential forms on complex manifolds, Stokes' theorem on domains with piecewise smooth boundaries, Hodge positivity). 

2. **Effort estimate**: **8 is calibrated, perhaps slightly optimistic**. Building out integration of differential forms, pullbacks, and the planar divergence theorem for a $4g$-gon with identified edges in Lean is an enormous undertaking. This is easily 6+ months of focused work.

3. **Proof recipe**: There is a **fatal logical cycle between Steps 3 and 4**. 
   - In Step 3 (α-normalization), you claim that if the A-period matrix $A$ satisfies $A \cdot v = 0$, then the resulting form $\omega_v$ has all A-periods zero, and hence $\langle \omega_v, \omega_v \rangle_{\text{Hodge}} = 0$ "(by Mumford II.2 eq. (4))". 
   - However, Mumford's equation (4) *is* the application of the general Riemann bilinear identity (Step 4) to $\omega_v$ and $\bar{\omega}_v$. The general identity $\int_X \omega \wedge \eta = \sum (A_i(\omega) B_i(\eta) - B_i(\omega) A_i(\eta))$ is precisely what proves that vanishing A-periods implies a vanishing area integral! 
   - You **cannot** invert the A-period matrix until you have proved the general Stokes theorem / bilinear identity on the fundamental polygon for *arbitrary* closed 1-forms. Step 4 is the heavy lifting and must logically precede Step 3. 

4. **Textbook citations**: **Excellent and accurate.** Mumford, Forster, and Griffiths-Harris are exactly the right sources for these specific steps.

5. **What's missing or wrong**:
   - **Order of operations:** You must first prove the general bilinear identity (current Step 4) for an arbitrary unnormalized basis $\omega'_j$. Then you use it to show that the A-periods determine a holomorphic 1-form uniquely (because vanishing A-periods forces the positive-definite Hodge norm to 0). *Then* you invert $A$ to obtain the normalized basis $c\omega$ (current Step 3), and finally you apply the general identity to the normalized basis to get symmetry and positivity of $\tau$ (Steps 5 and 6). 
   - **Mathlib reality check on Stokes:** The plan glosses over how `MeasureTheory.divergence_thm` will be used. Mathlib's divergence theorem is for the Bochner integral in flat Euclidean space. To apply it to a Riemann surface, you will need to formalize the pullback of differential forms to a planar domain (the $4g$-gon) and handle piecewise smooth boundaries. This isn't just a "bridge"—it is building the entire theory of differential form integration from scratch. The plan should acknowledge that `Path.lineIntegral` is insufficient here; you need integration of 2-forms and 1-forms over standard simplices/polygons.

6. **Recommendation**: **Revise.** You must reorder the steps so the general bilinear identity (Stokes) is proved first to justify the invertibility of the A-period matrix. Additionally, update the "Next discrete deliverable" to recognize that pulling back forms to a planar polygon is required before any integration-by-parts can occur.

VERDICT: revise — The proof recipe contains a logical cycle because A-matrix inversion (Step 3) requires the general bilinear identity (Step 4) to relate periods to the Hodge norm.
