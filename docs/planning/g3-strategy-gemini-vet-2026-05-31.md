# Gemini Deep Think Query History

Auto-generated log of queries sent to Gemini Deep Think and responses.

---


## 2026-06-04 22:28: Deep Think Query

**Duration:** 2m 42s

### Query

I am formalizing, in Lean 4 / Mathlib, the injectivity of the Abel–Jacobi map on a compact connected Riemann surface X of genus g > 0 ("Abel's theorem, curve side"). I want to derive the crux lemma G3 PROPERLY from Riemann–Roch and standard analytic infrastructure, introducing as FEW new axioms as possible. Please vet my strategy as an expert in Riemann surface theory and its formalization.

SETUP / what is already available as solid (proven or axiomatized) building blocks:
- Divisor X = free abelian group on points; deg : Divisor → ℤ.
- genus X = dim_ℂ H⁰(X, Ω¹) (holomorphic 1-forms), a biholomorphism invariant.
- AX_RiemannRoch (axiom): dim H⁰(O(D)) − dim H¹(O(D)) = deg D + 1 − g, with O(D), H⁰, H¹ currently OPAQUE (no function-space content yet).
- AX_AbelTheorem (axiom): ker(abelJacobiDiv : Divisor → Jacobian) = PrincipalDivisors.
- A "conservation of number" lemma (proven, Wallace): for a nonconstant holomorphic map f : X → ℙ¹ between compact Riemann surfaces, the weighted fiber count (sum of local multiplicities over f⁻¹(w)) is independent of w — i.e. the degree is well-defined.
- Chart-independent vanishing/pole order orderAt : X → (X→ℂ) → WithTop ℤ (proven, Wallace).

TARGET G3: for g > 0, if (Q₁) − (Q₂) ∈ PrincipalDivisors (i.e. = div f for some nonzero meromorphic f) then Q₁ = Q₂.

MY PROPOSED STRATEGY:
1. De-opaque the layer: define MeromorphicFunctionField X (nonzero global meromorphic functions, CommGroup under ×), divHom : f ↦ Σ_p orderAt(p,f)·(p) (needs: a nonzero global meromorphic function on compact X has finite zero/pole set), and redefine PrincipalDivisors := range(divHom). 
2. The genus obstruction C1: if Q₁≠Q₂ and div f = (Q₁)−(Q₂), then f as a map X→ℙ¹ has a single simple pole, so total pole order = degree = 1; by conservation of number every fiber is a single point with multiplicity 1, so f is bijective; a bijective holomorphic map between compact Riemann surfaces is a biholomorphism; genus is a biholomorphism invariant and genus(ℙ¹)=0; so genus X = 0, contradicting g>0. Hence Q₁=Q₂.

SPECIFIC QUESTIONS:
(a) Is the g≥2 case of G3 genuinely UNAVOIDABLE via the geometric degree-1⇒biholomorphism argument? In particular: do Riemann–Roch + Serre duality NUMERICS alone (without the geometric "no degree-1 map" input) suffice to prove h⁰(P)=1 for all g≥1, or only for g=1? I believe RR+Serre give h⁰(P)=1 cleanly only for g=1 (since deg(K−P)=2g−3 <0 forces h⁰(K−P)=0), and for g≥2 one truly needs the geometric argument. Confirm or correct.
(b) Is my factoring (de-opaque div/PrincipalDivisors first, then the geometric C1) the right minimal-axiom decomposition, or is there a leaner route that stays within the opaque H⁰/RR interface and avoids building meromorphic-function theory? 
(c) Which sub-steps of C1 are the genuine formalization risks / likely to need their own axiom: (i) finiteness of zeros/poles, (ii) "weight-1 fiber everywhere ⇒ injective", (iii) "bijective holomorphic between compact RS ⇒ biholomorphism", (iv) "genus is a biholomorphism invariant"? Rank them by difficulty and tell me which are standard/short vs which are substantial.
(d) Any subtlety I am missing — e.g. need for connectedness, the map being well-defined into ℙ¹ at the pole, multiplicity-vs-ramification conventions, or a cleaner classical route (e.g. via the fact that a degree-1 proper holomorphic map is automatically an iso, or via h⁰((Q₂)) and Riemann–Roch packaged differently)?

Be concrete and rigorous; I will act on this to choose the axiom boundary for a multi-week formalization.

### Response

This is an excellent, highly specific formalization architecture question. Your strategy is geometrically completely sound, and you have correctly identified the structural bottleneck in going from algebraic divisor data to analytic/geometric mappings. 

Here is a detailed vetting of your strategy, answering your questions directly, ranked by formalization priority.

### (a) Is the $g \ge 2$ case genuinely unavoidable via the geometric argument?
**Yes, you are completely correct.** Riemann–Roch + Serre duality pure numerics **fail** to prove $h^0(P) = 1$ for $g \ge 2$. 
*   **The Math:** By RR + Serre, $h^0(P) = 2 - g + h^0(K - P)$. To conclude $h^0(P) = 1$, you need $h^0(K - P) = g - 1$. However, $\deg(K-P) = 2g - 3$. For $g=1$, $\deg = -1 < 0$, forcing $h^0 = 0$, so the numerics work perfectly. For $g \ge 2$, $\deg(K-P) > 0$. The fact that $h^0(K-P) = g-1$ means $P$ is *not a base point of the canonical linear system*. Proving the canonical linear system is base-point-free on a non-rational curve requires exactly the geometric "no degree-1 map to $\mathbb{P}^1$" argument you are trying to avoid!
*   **Takeaway for Formalization:** You **must** use the geometric argument (C1) for $g \ge 2$. In fact, notice a beautiful consequence for your axiom boundary: **Lemma G3 does not require the Riemann–Roch axiom at all.** It relies entirely on your meromorphic/analytic infrastructure.

### (b) Is the factoring (de-opaque div, then geometric C1) the right minimal-axiom route?
**Yes, this is the optimal minimal-axiom decomposition.** 
You cannot stay within the opaque $H^0/O(D)$ interface because an opaque cohomology group cannot be evaluated at points to construct a map $f: X \to \mathbb{P}^1$. 
To use the Wallace "conservation of number" theorem, you mathematically *must* bridge the gap between "algebraic equivalence of divisors" and "explicit holomorphic maps to $\mathbb{P}^1$". De-opaquing `PrincipalDivisors` as the image of `divHom` on the Meromorphic Function Field is the standard, unavoidable bridge.

### (c) Ranking the Formalization Risks in C1 (Hardest to Easiest)
Here is the true ranking of your sub-steps by formalization difficulty in Lean 4/Mathlib:

**1. (HARD) Constructing the map to $\mathbb{P}^1$ (Subtlety missing from your list)**
Before you even use C1, you must turn $f \in \mathcal{M}(X)$ into a holomorphic map $\hat{f}: X \to \mathbb{P}^1$. In Mathlib, this means gluing $f: X \setminus \{\text{poles}\} \to \mathbb{C}$ and $1/f: X \setminus \{\text{zeros}\} \to \mathbb{C}$. Showing that $1/f$ is holomorphic at the poles of $f$ and that the resulting map is a globally well-defined manifold morphism is notoriously tedious in a formalized setting. *Recommendation: Axiomatize this construction step if you are pressed for time.*

**2. (MEDIUM-HARD) Finiteness of zeros/poles**
This requires combining the Identity Theorem (zeros of a non-zero holomorphic function are isolated) with topological compactness. Mathlib has the Identity Theorem for $\mathbb{C}$, but lifting it through manifold charts to deduce that the zero locus has no accumulation points requires some careful topological boilerplate.

**3. (MEDIUM) Genus is a biholomorphism invariant / $g(\mathbb{P}^1) = 0$**
If you define $g = \dim H^0(X, \Omega^1)$, invariance requires showing that pullback of 1-forms along a biholomorphism is a linear isomorphism. Depending on the state of Mathlib's differential geometry library regarding pullbacks of sections of the cotangent bundle, this is either a 5-line proof or a massive headache. Furthermore, you will need to prove (or axiomatize) that $H^0(\mathbb{P}^1, \Omega^1) = 0$ (e.g., by showing $dz$ has a pole of order 2 at $\infty$).

**4. (EASY) "Bijective holomorphic between compact RS $\implies$ biholomorphism"**
*Crucial optimization here:* Do **not** try to prove the general theorem that a bijective holomorphic map is a biholomorphism (which requires Osgood's theorem or Open Mapping). Instead, use the numerics of your degree!
Because $\deg = 1$, the sum of local multiplicities $\sum_{x \in f^{-1}(w)} m_x = 1$. Since $m_x \ge 1$, there is exactly one preimage **AND** its local multiplicity is exactly $m_x = 1$. A local multiplicity of 1 *means* the derivative is non-zero, making it a *local diffeomorphism* by the Inverse Function Theorem. A bijective local diffeomorphism is trivially a global diffeomorphism (and biholomorphism).

**5. (TRIVIAL) "Weight-1 fiber everywhere $\implies$ injective"**
This is pure arithmetic. If $\sum_{x \in S} m_x = 1$ for integers $m_x \ge 1$, then $|S| = 1$.

### (d) Subtleties to watch out for

*   **Connectedness is crucial:** The "conservation of number" theorem requires $X$ to be connected. If $X$ were disconnected (e.g., $X_1 \sqcup X_2$), a function could have degree 1 on $X_1$ and degree 0 on $X_2$, breaking the "bijective everywhere" argument. You must ensure your definition of Riemann Surface includes connectedness, or carry `ConnectedSpace X` as an assumption.
*   **Multiplicity vs. `orderAt`:** You defined `divHom` using `orderAt`. You must ensure that the definition of multiplicity used in Wallace's theorem exactly matches your `orderAt` at zeros, and `-orderAt` at poles. In complex analysis, the local mapping degree of $f$ at $p$ mapping to $\infty$ is the pole order of $f$ at $p$. 
*   **The definition of $f \neq 0$:** When de-opaquing `MeromorphicFunctionField`, ensure it is defined as functions that are *not identically zero on any connected component*. Since $X$ is connected, $f \neq 0$ globally is sufficient.

### Summary / Actionable Advice for your Axiom Boundary

To keep the multi-week project achievable, here is the recommended axiom set for your C1/G3 bridge:

1.  **Axiom (Map to $\mathbb{P}^1$):** Given $f \in \mathcal{M}(X)$, there exists a holomorphic map $\hat{f} : X \to \mathbb{P}^1$ such that the local winding number of $\hat{f}$ at $w \in \mathbb{P}^1$ exactly matches the zero-order of $(f - w)$ (and pole-order for $w = \infty$).
2.  **Axiom (Genus of $\mathbb{P}^1$):** $\dim H^0(\mathbb{P}^1, \Omega^1) = 0$.
3.  **Axiom (Biholomorphism Invariance):** If there exists a biholomorphism $X \cong Y$, then $\dim H^0(X, \Omega^1) = \dim H^0(Y, \Omega^1)$.

With these three specific analytic axioms, plus Wallace's theorem, you can rigorously derive G3 in Lean entirely via your proposed geometric degree-1 argument, completely bypassing the opaque Riemann-Roch block for this specific lemma.

---
