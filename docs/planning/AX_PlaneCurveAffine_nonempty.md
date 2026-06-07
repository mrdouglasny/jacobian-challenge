> **✅ DISCHARGED — 2026-06-07 (PR #92).** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# `AX_PlaneCurveAffine_nonempty` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:103`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 5 &nbsp;&nbsp; **Est:** ~4–6 focused days, ~150 LOC (including downstream signature updates, correct FTA variable selection, and ruling out constant dehomogenizations)
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** For a smooth plane curve of degree `≥ 1`
the affine patch is nonempty. Classical: `F` has at least one zero on
`ℂ² × {1} ⊂ ℂ³ \ {0}` by projective algebraic geometry. -/
axiom AX_PlaneCurveAffine_nonempty (H : PlaneCurveData) :
    Nonempty (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_nonempty
```

**Why it's an axiom right now:** The original author axiomatized this under the classical intuition that projective curves intersect the affine patch, but **the axiom as stated is mathematically false**. For $d = 1$, the polynomial $F(x,y,z) = z$ defines a valid smooth plane curve, but its affine patch $\{ (x,y) \mid 1 = 0 \}$ is completely empty. The statement must be weakened to require $d \ge 2$ (or $F \notin (z)$). Once the signature is corrected, it classifies as `mathlib-now`, relying on dehomogenization and `Complex.exists_root` (already used at `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean:95`), provided one carefully handles polynomial degree bounds and variable selection. Load-bearing facts: (i) `H.h_deg : 1 ≤ d` (`PlaneCurve.lean:47`) needs to become $2 \le d$; (ii) `H.F.homogeneous : F.val.IsHomogeneous d` (`PlaneCurve.lean:41`); (iii) `H.h_smooth` at `PlaneCurve.lean:52` rules out curves like $F = cz^d$ for $d \ge 2$.

**Proof recipe**

1. **Step 0 — Correct the axiom signature.** Change the statement of `AX_PlaneCurveAffine_nonempty` in `Jacobians/ProjectiveCurve/PlaneCurve.lean:103` to require `(hd : 2 ≤ H.d)`. Propagate this new hypothesis to downstream consumers, specifically `PlaneCurve.instNonempty` at `PlaneCurve.lean:178`.

2. **Step 1 — Dehomogenize and rule out constant polynomials.** Define the dehomogenized polynomial $G(x, y) := F(x, y, 1)$ in `MvPolynomial (Fin 2) ℂ`. We must prove $G$ is not a constant polynomial. Suppose for contradiction $G(x, y) = c$. Since $F$ is homogeneous of degree $d$, this implies $F = c z^d$. 
   - If $c = 0$, $F = 0$, which contradicts $d \ge 2$.
   - If $c \neq 0$, then the gradient is $\nabla F = (0, 0, dc z^{d-1})$. At the projective point $(1, 0, 0)$, $F(1, 0, 0) = 0$ (since $d \ge 2$), and the gradient evaluates to $(0, 0, 0)$. This contradicts the smoothness assumption `H.h_smooth` (`PlaneCurve.lean:52`). Thus, $G$ is not a constant.

3. **Step 2 — Variable selection and leading coefficients.** Since $G$ is not constant, it has positive degree in at least one variable. Without loss of generality, assume it has positive degree in $y$. Write $G(x,y) = \sum_{i=0}^k P_i(x) y^i$ as a polynomial in $y$ with coefficients in $\mathbb{C}[x]$, where $k \ge 1$ and $P_k \neq 0$. Because $P_k(x)$ is a non-zero univariate polynomial, it has only finitely many roots. Choose an $x_0 \in \mathbb{C}$ such that $P_k(x_0) \neq 0$.

4. **Step 3 — Apply the Fundamental Theorem of Algebra.** Substitute $x_0$ into $G$ to obtain a univariate polynomial $g(y) := G(x_0, y)$. Because $P_k(x_0) \neq 0$, $g(y)$ has degree exactly $k \ge 1$. Apply `Complex.exists_root` to $g(y)$. This yields a root $y_0 \in \mathbb{C}$ such that $g(y_0) = 0$, which means $F(x_0, y_0, 1) = 0$.

5. **Step 4 — Assemble the instance.** In `Jacobians/ProjectiveCurve/PlaneCurve.lean`, replace the axiom block with:
   ```lean
   /-- For $d \ge 2$, $F = cz^d$ is singular at $(1,0,0)$. Thus the dehomogenization 
   $G(x,y) = F(x,y,1)$ is non-constant, and FTA guarantees a root in $\mathbb{C}^2$. -/
   noncomputable theorem PlaneCurveAffine.nonempty (H : PlaneCurveData) (hd : 2 ≤ H.d) :
       Nonempty (PlaneCurveAffine H) := by
     sorry -- ~60 LOC implementing Steps 1-3
   ```
   *(Note: By switching to a `theorem` that takes `hd`, you will drop the `instance` attribute on this specific lemma and instead thread `hd` into the downstream `PlaneCurve.instNonempty` instance or convert that to a theorem as well.)*

**Next discrete deliverable.** The mathematical formulation of "If $F = c z^d$ and $d \ge 2$, then $F$ is singular at $(1,0,0)$" in Lean is entirely self-contained and isolates the core algebraic geometry contradiction.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — Replace the false `axiom` at lines 100–106 with a proven `noncomputable theorem` requiring `2 ≤ H.d`.
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — Update `PlaneCurve.instNonempty` at `:178` to accept the new signature.
- `Jacobians/ProjectiveCurve/PlaneCurve/Nonempty.lean` (new) — House the `F = cz^d` singularity proof, the variable selection logic, and the FTA assembly.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurve.instNonempty` (at `PlaneCurve.lean:178`) no longer lists `AX_PlaneCurveAffine_nonempty`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Propagating the `2 ≤ d` assumption will break the signature of `PlaneCurve.instNonempty`. If downstream files heavily rely on this being a blanket instance for *all* PlaneCurveData (including degree 1 lines), the project architects must be escalated to. The correct fix might be modifying `PlaneCurveData` itself to globally mandate $d \ge 2$.
- If Mathlib's `MvPolynomial` API lacks the necessary view of an MV-polynomial as a univariate polynomial with polynomial coefficients (`G(x,y) = \sum P_i(x)y^i`), manual evaluation gymnastics will be required, increasing LOC.

### `Gemini critique addressed:`
- **Acknowledged false axiom:** The critique correctly identified that the axiom is mathematically false for $d=1$ (the line $F=z$ has an empty affine patch on $z=1$). Added Step 0 to rewrite the signature to require $d \ge 2$.
- **Fixed degree-zero gap:** The critique noted the failure to handle constant dehomogenizations $G=c$. Added Step 1 to explicitly prove $F=cz^d$ is singular at $(1,0,0)$ for $d \ge 2$, which contradicts `H.h_smooth`.
- **Fixed variable selection:** The critique pointed out that arbitrarily selecting $y_0$ might leave a constant polynomial in $x$. Added Step 2 to explicitly isolate the leading coefficient $P_k(x)$ for the variable $y$, and select an $x_0$ that is not a root of $P_k$.
- **Adjusted effort:** Bumped effort from 4 to 5 to account for downstream signature propagation across instances.

---
**Vetting trail.** Critique: `_vetting/AX_PlaneCurveAffine_nonempty.md`. Verdict: reject. Revised: 2026-06-03.