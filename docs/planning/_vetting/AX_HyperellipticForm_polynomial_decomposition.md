# Gemini 3.1 Pro critique — `AX_HyperellipticForm_polynomial_decomposition`

**Model:** gemini-3.1-pro-preview
**Duration:** 170.6s
**Source axiom:** `Jacobians/Axioms/HyperellipticLiouville.lean`
**Note:** L2 keystone
**Verdict:** **reject**

---

Here is a detailed referee critique of the proposed discharge plan.

### 1. Route classification
The classification **genuine-textbook** is conceptually correct for the mathematical result, but the proposed plan turns this into a **needs-infra** quagmire by demanding the construction of rational function fields (`RatFunc`, `AdjoinRoot`) on the curve. This algebraic machinery is completely unnecessary and over-engineers the problem; the proof can and should be done using pure, elementary complex analysis on $\mathbb{C}$.

### 2. Effort
The estimate of **8 (~3–6 weeks)** is inflated due to the bad algebraic design. Using a purely complex-analytic path (pointwise symmetry over the two sheets), you bypass the algebraic geometry entirely. The true effort for the correct proof should be closer to a **5**. However, as written, the recipe's effort is $\infty$ because it tasks the formalizer with proving mathematically false statements.

### 3. Proof recipe
The recipe is **fatally flawed** on both logical and mathematical levels. 
* **Fatal Error 1 (Wrong Poles):** The recipe proposes decomposing `form.coeff` as $a(z) + y b(z)$ and claims in sub-step 2 that holomorphy forces $b \in \mathbb{C}[x]$. This is mathematically impossible. `form.coeff` represents the function $\omega / dx$. Because $dx = 2y\,dy/f'$ has simple zeros at the branch points, the ratio $\omega/dx$ must have simple poles there. Therefore, $b(z)$ will be a rational function with poles at the roots of $f(z)$, **not** a polynomial. Asking the formalizer to prove $b \in \mathbb{C}[x]$ is asking them to prove a false lemma.
* **Fatal Error 2 (Backwards Asymptotics):** In sub-step 3, the recipe claims the infinity pullback bounds $\deg b \le N/2 - 2$. This is backwards. If $\omega = y b(x) dx$, holomorphy at $\infty$ (where $x = 1/u$, $y \sim u^{-N/2}$, $dx \sim u^{-2}du$) requires $b(x)$ to *decay* as $O(|x|^{-N/2 - 2})$. It is the product $g(x) := f(x)b(x)$ that grows like $O(|x|^{N/2 - 2})$ and becomes the target polynomial.
* **Unnecessary Abstraction:** Sub-step 1 invokes abstract field theory. Because you are working locally on charts over $\mathbb{C}$, you can directly define the symmetric and antisymmetric components pointwise without invoking abstract algebra.

### 4. Textbook citations
Forster §13–14 is the correct reference, but the recipe misapplies it. Forster decomposes $\omega = (A(x) + y B(x)) \frac{dx}{y}$, which naturally makes $A$ and $B$ polynomials. The recipe author blindly adapted this linear combination to $\omega / dx$ without adjusting for the $\frac{1}{y}$ factor, leading to the cascading pole and degree errors.

### 5. What's missing or wrong
The entire recipe needs to be rewritten to eliminate `RatFunc` and focus on the correct holomorphic functions.
* **Fix Sub-step 1:** Drop `FieldTheory.RatFunc`. For $z \in \mathbb{C} \setminus \{f=0\}$, let $(z, w)$ and $(z, -w)$ be the two points on the affine curve over $z$. Define $a(z) = \frac{1}{2}(h_+ + h_-)$ and $g(z) = \frac{w}{2}(h_+ - h_-)$ directly as $\mathbb{C} \to \mathbb{C}$ functions, where $h_{\pm} = \text{form.coeff}((z, \pm w), z)$. 
* **Fix Sub-step 2:** Prove that $a(z)$ and $g(z)$ are holomorphic on $\mathbb{C} \setminus \{f=0\}$. Then, use the branch-point charts (where $w$ is the local coordinate) to show that $\text{form.coeff} \sim O(1/w)$. This implies $a(z)$ and $g(z)$ are bounded as $z \to \text{roots}(f)$. By Riemann's removable singularity theorem, $a$ and $g$ extend to entire functions on $\mathbb{C}$. 
* **Fix Sub-step 3:** Use the infinity chart to bound their growth. Show that $\omega$ being bounded at $u=0$ implies $\text{form.coeff} = O(|z|^{-2})$. Thus, $a(z) = O(|z|^{-2})$ and $g(z) = O(|z|^{N/2 - 2})$.
* **Fix Sub-step 4:** Apply Liouville's theorem to conclude $a(z) \equiv 0$, and use the already-proven `differentiable_eq_polynomial_of_growth` to conclude $g(z)$ is a polynomial of degree $< N/2 - 1$. Substitute $a=0$ back to get `form.coeff = g(z)/w`.

### 6. Recommendation
Reject outright. The current recipe commands the formalizer to prove false algebraic properties because it decomposes the wrong function, and needlessly complicates the formalization with function-field infrastructure.

VERDICT: reject — The recipe mathematically fails by decomposing the wrong function (resulting in false claims about polynomials) and unnecessarily bloats the effort with function fields instead of elementary pointwise symmetries.
