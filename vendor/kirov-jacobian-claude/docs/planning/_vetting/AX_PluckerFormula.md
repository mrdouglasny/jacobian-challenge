# Gemini 3.1 Pro critique — `AX_PluckerFormula`

**Model:** gemini-3.1-pro-preview
**Duration:** 49.4s
**Source axiom:** `Jacobians/Axioms/PluckerFormula.lean`
**Verdict:** **reject**

---

Here is a rigorous referee critique of the proposed axiom-discharge plan.

### 1. Route classification
The proposed route of `needs-infra` is fundamentally misleading because it misidentifies *which* infra is appropriate. By routing through scheme-theoretic sheaf cohomology and adjunction, the plan actually just kicks the can to new helper lemmas that act as axioms. The correct route should be `genuine-textbook`, but using a different, elementary textbook proof (explicit differential forms or Riemann-Hurwitz) that leverages the existing manifold/complex-analytic infra rather than requiring massive new algebraic machinery.

### 2. Effort estimate
The estimate of **7 (2-3 weeks, ~400 LOC)** is a complete delusion. Developing the theory of line bundles on projective space, exact sequences of ideal sheaves, long exact sequences in sheaf cohomology, and Bott/Serre vanishing to prove $H^1(\mathbb{P}^2, \mathcal{O}(-3)) = 0$ is a colossal undertaking. Even if simplified for $\mathbb{P}^2$, doing this rigorously from scratch in Lean 4 is a multi-month or multi-year effort involving thousands of LOC, not 400. 

### 3. Proof recipe
- **Fatal GAGA gap:** The project defines `genus` via the complex-analytic `HolomorphicOneForm X` (relying on `ContDiff` / `Manifold` infrastructure). The proof recipe uses exact sequences of algebraic ideal sheaves. There is no automatic bridge between algebraic scheme cohomology and analytic sheaf cohomology in Mathlib (GAGA). You cannot just equate analytic global sections with algebraic ones without proving it.
- **Kicks the can:** Step 5 introduces `PlaneCurve.adjunction_canonical` and `PlaneCurve.H0_restrict_iso`. These are the actual theorems. The plan simply asserts them as "helper lemmas" without explaining how they will be proven, meaning the plan doesn't discharge the axiom—it just splits it into two harder, unprovable axioms.
- **Overkill:** Using the full adjunction formula and sheaf cohomology exact sequences to find the genus of a plane curve is massive overkill and ignores the explicit data of `PlaneCurveData`.

### 4. Textbook citations
Citing Mumford's *Red Book* (pure abstract scheme theory) is inappropriate for an API based on complex manifolds. G&H Ch 2.4 (hyperplane sections) is similarly too heavy. The correct reference is Miranda's *Algebraic Curves and Riemann Surfaces* (Ch VII.1) or G&H Ch 1.1, where the genus of a smooth plane curve is computed directly by constructing an explicit basis of holomorphic differentials (via the Poincaré residue) or by generic projection and Riemann-Hurwitz.

### 5. What's missing or wrong
- **Analytic vs. Algebraic conflation:** You cannot casually "take cohomology" of $0 \to \mathcal{O}_{\mathbb{P}^2}(-3) \to \mathcal{O}_{\mathbb{P}^2}(d-3) \to \mathcal{O}_X(d-3) \to 0$ in the analytic category because global analytic Serre vanishing on projective space requires Cartan's Theorems A/B or Dolbeault cohomology—none of which exist in Mathlib.
- **Missing vanishing theorem:** The deduction that $H^0(X, \mathcal{O}_X(d-3)) \simeq H^0(\mathbb{P}^2, \mathcal{O}(d-3))$ requires $H^1(\mathbb{P}^2, \mathcal{O}(-3)) = 0$. The plan waves this away as "Bott / Serre vanishing", but this is a massive gap that the author provides no recipe for formalizing. 

### 6. Recommendation
**Reject.** Scrap the abstract sheaf-cohomology/adjunction approach entirely. 

**Alternative Proof Recipe:** Replace with a direct analytic/computational proof. For a smooth plane curve $F(x,y,z) = 0$, define the explicit differential forms on the affine patch $z \neq 0$: 
$$ \omega_P = \frac{P(x,y) \, dx}{\partial F / \partial y} $$
where $P$ is a polynomial. 
1. Prove analytically that $\omega_P$ extends to a globally holomorphic 1-form on the compact Riemann surface if and only if $\deg(P) \le d-3$. 
2. Show that these forms are linearly independent and span `HolomorphicOneForm X`.
3. Conclude the genus is the dimension of the space of polynomials of degree $\le d-3$, which is precisely $(d-1)(d-2)/2$. 
This avoids all sheaf cohomology, exact sequences, vanishing theorems, and GAGA gaps, utilizing only basic manifold calculus and polynomial dimension counting.

VERDICT: reject — The plan relies on nonexistent, heavy sheaf cohomology and Serre vanishing (ignoring a fatal GAGA gap) and should be replaced with a direct computation of the explicit basis of holomorphic 1-forms.
