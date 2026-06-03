# Gemini 3.1 Pro critique — `Hyperelliptic-instIsManifold`

**Model:** gemini-3.1-pro-preview
**Duration:** 76.5s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the discharge plan for `Hyperelliptic.instIsManifold`:

1. **Route classification**: `needs-infra` is correct. The proof is standard differential geometry/algebraic curve theory but is blocked by missing Mathlib infrastructure (specifically, IFT API for `PartialHomeomorph` inverses) and project-specific transition chart lemmas.

2. **Effort 1..10**: 8 is appropriate for the true difficulty, but the **500 LOC estimate is delusional** if you actually attempt the method proposed in Block A. If you fix the mathematical approach in Block A, ~800 LOC is realistic. 

3. **Proof recipe**:
   - **Block A (The Trap)**: The proposed method—"`Laurent`-style power-series inversion of `t ↦ 1/(lc(f) t²)·(1 + O(t))`"—is a formalization death wish. Lean 4 / Mathlib's formal power series and analytic functions API is not built for seamless explicit inversion and asymptotic `O(t)` reasoning. Doing this manually will cost you thousands of lines of hell. **Do not do this.** 
     *Instead:* use the Analytic Implicit Function Theorem on the algebraic equations. With the standard uniformizer $t = x^g/y$ and $u = 1/x$, the curve equation gives $t^2 F(u) - u = 0$ where $F$ is a polynomial and $F(0) \neq 0$. The derivative with respect to $u$ at $(0,0)$ is non-zero. IFT immediately implies $u(t)$ is analytic, whence $x(t) = 1/u(t)$ is analytic for $t \neq 0$. This avoids series manipulation entirely.
   - **Block B**: Spot on. You have correctly identified that `contDiffOn_symm_toOpenPartialHomeomorph` (looping `ContDiffAt.to_localInverse` over the source) is the critical missing Mathlib glue.
   - **Block C**: You correctly note that the transport resolves to the identity on $\mathbb{C}$, but your phrasing implies you might build custom analytic transport lemmas. You don't need to. If `Hyperelliptic.instChartedSpace` is defined as a strict topological pullback (e.g., pulling back the atlas via `Homeomorph`), the transition maps of the domain are of the form `(e.trans phi).symm.trans (e.trans psi)`. This algebraically simplifies via associativity and `e.symm.trans e = id` directly to `phi.symm.trans psi`. The transition maps are propositionally identical partial homeomorphs on $\mathbb{C}$. No analytic transport is needed at all.

4. **Textbook citations**: Missing. You are reinventing the wheel for Block A. Cite **Miranda, "Algebraic Curves and Riemann Surfaces" (Chapter II.1)**, which clearly maps out the purely algebraic IFT setup for local coordinates at branch points.

5. **What's missing or wrong**:
   - **Laurent series trap**: As stated above, Block A proposes a technically inferior and massively painful formalization path.
   - **ChartedSpace Dependency**: The plan assumes `Hyperelliptic.instChartedSpace` will be discharged first. For Block C to work trivially, `instChartedSpace` *must* be defined as a strict pullback of the odd/even charted spaces. If the charted space is constructed from scratch, Block C will fail.

6. **Recommendation**: Revise. Rewrite Block A to explicitly use the Implicit Function Theorem on the rational curve equations instead of formal power series inversion, and explicitly require `instChartedSpace` to be defined as an atlas pullback to trivialize Block C.

VERDICT: revise — The plan correctly identifies the missing Mathlib IFT infrastructure, but proposes a disastrous "Laurent-style series inversion" approach for Block A that must be replaced by the algebraic Implicit Function Theorem.
