# Gemini 3.1 Pro critique — `infinityInverseMap`

**Model:** gemini-3.1-pro-preview
**Duration:** 83.3s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`
**Verdict:** **reject**

---

1. **Route classification**: Incorrect as stated. While the result is indeed `provable-from-other-axioms`, the plan assumes it requires low-level formal series manipulation and hints at needing multi-variable infra. In reality, Mathlib already has the high-level analytic inverse function theorem (`Mathlib.Analysis.Analytic.Inverse`) which makes this accessible right now without hand-rolling implicit function theorems.

2. **Effort 1..10**: The estimate of 4 is accurate for the *correct* approach. However, if you attempted to follow the proposed plan, the effort would explode to an 8 because you would hit a brick wall trying to build a multivariate formal implicit function theorem from the compositional inverse API.

3. **Proof recipe**: Fatally flawed and logically disconnected. 
   - **The algebraic gap:** Step 3a sets up a single equation $v^2 = f(u)$ to solve for *two* unknown series $\hat{x}(t)$ and $\hat{y}(t)$. This is underdetermined. You completely forgot to enforce the uniformizer relation $t = y/x^{g+1}$, which is necessary to eliminate $y$.
   - **The API hallucination:** Step 3b attempts to apply `FormalMultilinearSeries.rightInv` to the equation $\Phi(t, \hat{x}, \hat{y}) = 0$. This is mathematically nonsensical. `rightInv` computes the *compositional inverse* (Lagrange inversion) of a series, yielding $G$ such that $F(G(x)) = x$. It does **not** solve multivariate implicit polynomial equations. You are conflating the Implicit Function Theorem with compositional inversion.

4. **Textbook citations**: Miranda and Mumford are the correct standard references for the geometry of the hyperelliptic chart at infinity, but they do not advocate the mangled 2-variable power series algebra proposed in Step 3.

5. **What's missing or wrong**:
   - You failed to eliminate $y$. By defining the uniformizer $t = y/x^{g+1}$, you have $y = t x^{g+1}$.
   - Substituting this into $y^2 = f(x)$ gives $t^2 x^{2g+2} = f(x)$. Letting $z = 1/x$, this becomes $t^2 = z^{2g+2}f(1/z)$. 
   - Define the polynomial $P(z) = z^{2g+1}f(1/z)$. Then $t^2 = z P(z)$. Notice that $P(0) = c \neq 0$.
   - Let $z = w^2$. Then $t^2 = w^2 P(w^2)$, so $t = w \sqrt{P(w^2)}$.
   - You have completely ignored the high-level Analytic Inverse Function Theorem in Mathlib. The map $w \mapsto t(w) = w \sqrt{P(w^2)}$ is an analytic function from $\mathbb{C} \to \mathbb{C}$ with derivative $\sqrt{c} \neq 0$ at $w=0$. You can invert it directly using Mathlib's 1D analytic inverse API. There is absolutely no need to manually extract radii from `FormalMultilinearSeries`.

6. **Recommendation**: Reject. The recipe must be completely rewritten. Discard the multivariate $\Phi=0$ setup and the raw formal multilinear series. Instead, use the substitution $y = t x^{g+1}$ and $x = 1/w^2$ to reduce the curve equation to the 1D analytic map $t(w) = w \sqrt{P(w^2)}$, and apply Mathlib's analytic inverse function theorem to find $w(t)$. The escalation triggers concerning "multi-variable inversion" are ghosts created by a bad algebraic setup.

VERDICT: reject — The proof recipe sets up an underdetermined system by failing to eliminate y, and hallucinates that Mathlib's compositional inverse API can solve multivariate implicit equations; it must be rewritten to use the 1D analytic inverse function theorem on the reduction t = w√(P(w²)).
