> **✅ DISCHARGED (retired).** This axiom no longer exists in the kernel — the single-valued ℂ open-path "FTC" it asserted is FALSE for Abel–Jacobi and was deleted (path-independence lives at H1 via `loopIntegralToH1`). This plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_pathIntegral_local_antiderivative`

**Model:** gemini-3.1-pro-preview
**Duration:** 37.8s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

An expert review of your axiom-discharge plan for `AX_pathIntegral_local_antiderivative` reveals a fatal logical gap regarding path independence, as well as an unacceptable proposal to introduce a new axiom. 

Here is the detailed critique:

1. **Route classification:** The classification as `genuine-textbook` is plausible, but this leans heavily into `needs-infra` because proving FTC for manifold-valued line integrals involves navigating complex Mathlib API gaps (smoothness, chart derivatives, and integral properties). 

2. **Effort estimate:** 7 is likely a severe underestimate (~3 weeks is optimistic). Dealing with the chain rule, differentiation under the integral (or FTC for `intervalIntegral`), and managing smooth/analytic structures across Kirov's library will take longer, especially given the missing mathematical piece identified below.

3. **Proof recipe (Logical Gaps & Kicking the Can):** 
   - **Fatal Flaw in 3a (Kicking the can):** Proposing to add a property axiom `bridgePath_chartLine_concat_eventually` completely defeats the purpose of an axiom discharge plan. You cannot discharge an axiom by simply inventing a new one that asserts exactly what you need to finish the proof. 
   - **Fatal Flaw in 3b (Missing Math / Path Independence):** If you redefine `bridgePath P₀ Q` to just be "some path", the integral from $P_0$ to $Q$ will not trivially decompose into $\int_{P_0}^P + \int_{P}^Q$ (along a straight chart line). `bridgePath P₀ Q` and the concatenated path `bridgePath P₀ P + chartLine P Q` are two *different paths*. To equate their integrals, you mathematically **must** prove that the line integral of a holomorphic 1-form is locally independent of the path (which requires Cauchy's Theorem / local exactness / closedness of holomorphic forms on convex chart balls). The plan completely ignores this massive requirement. Without local path independence, you cannot perform the substitution necessary to evaluate the derivative at $P$.

4. **Textbook citations:** Mumford and Griffiths-Harris are correct for the high-level geometry, but they handwave the analytic details (which are the real blockers in Lean). Forster (Ch. I §10–13) is a better citation here precisely because it handles chart-local integration and Cauchy's theorem—which your Lean plan forgot to incorporate.

5. **What's missing or wrong:**
   - You cannot legally equate the integral over a generic global `bridgePath P₀ Q` with the integral over `bridgePath P₀ P` plus a local chart-line unless you have local homotopy invariance of integrals for holomorphic 1-forms.
   - If Kirov's library does not already have local exactness/Cauchy's theorem for complex line integrals, this task is blocked by major missing infrastructure.
   - You cannot just locally redefine `bridgePath` to use chart-lines "near P", because `pathIntegralBasepointFunctional` takes $P_0$ and $Q$, and has no canonical knowledge of the intermediate point $P$ around which you are taking the derivative. 

6. **Recommendation:** Reject. You must revise the plan to explicitly address how you will prove or bypass local path independence (Cauchy's theorem for convex chart balls) in order to legitimately split the path integral, and you must entirely scrap the suggestion in 3a to introduce a new axiom.

VERDICT: reject — The plan illegally proposes swapping the axiom for a new one (step 3a) and completely misses the local path-independence / Cauchy theorem infrastructure required to legitimately split the path integral in step 3b.
