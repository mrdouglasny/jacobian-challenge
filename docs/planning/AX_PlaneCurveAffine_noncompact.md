# `AX_PlaneCurveAffine_noncompact` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:121`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~2-3 focused weeks, ~250 LOC (requires heavy `MvPolynomial` manipulation)
**Blocked by:** `AX_PlaneCurveAffine_nonempty`

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** The affine patch is noncompact —
projective curves are compact but their affine patches are not (the
affine patch misses at least one point at infinity). -/
axiom AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
    NoncompactSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_noncompact
```

**Why it's an axiom right now:** The docstring states the classical fact "projective curves are compact, but their affine patches are not". While this is purely topological (`isClosed_carrier` is already a real theorem at `PlaneCurve.lean:82`), the affine patch is a closed subset of `ℂ²`, which is compact iff it is bounded. Showing an arbitrary algebraic curve is unbounded requires rigorous degree-counting and polynomial evaluation. This requires heavy infrastructure to bridge `MvPolynomial (Fin 3) ℂ` to univariate polynomials over `ℂ[X]` or `ℂ[Y]`, which Mathlib's API makes famously clunky. Furthermore, for the specific edge case $F = Z$, the affine patch is strictly empty (and thus compact); so the axiom structurally relies on `AX_PlaneCurveAffine_nonempty` to rule out this line at infinity.

**Proof recipe**

Standard reference: **Hartshorne, *Algebraic Geometry*, I.2 Exercise 2.4** (affine variety in `𝔸ⁿ_ℂ` is noncompact unless 0-dimensional) and **Beauville, *Complex Algebraic Surfaces*, Ch. I §I.2** (the projective compactification is the unique compactification of a smooth affine variety). Note that these references provide the high-level algebraic geometry facts but do not cover the elementary complex polynomial API-bashing required here. The Lean discharge will loosely mirror `Hyperelliptic/Basic.lean:108–129` once the `MvPolynomial` infrastructure is in place.

1. **Sub-step 1 — `MvPolynomial` Bridge Infrastructure.** Define the API bridging `MvPolynomial (Fin 3) ℂ` to `Polynomial (Polynomial ℂ)`. Specifically, create operations to evaluate at $Z=1$, then isolate the polynomial as a univariate polynomial in $Y$ whose coefficients are polynomials in $X$, and symmetrically as a univariate polynomial in $X$ with coefficients in $Y$. Create lemmas to extract the leading coefficients in both cases.

2. **Sub-step 2 — set up the projections.** Define $\pi_x, \pi_y : PlaneCurveAffine H \to ℂ$ by $\pi_x(p) := p.val.1$ and $\pi_y(p) := p.val.2$ (analogous to the inline `π` in `Hyperelliptic/Basic.lean:111`). Both are continuous by `continuous_subtype_val.fst` and `.snd` (`Hyperelliptic/Basic.lean:112`).

3. **Sub-step 3 — prove at least one projection is unbounded.** Because $F(X,Y,1)$ is not a constant (if it were, the affine patch would be empty, contradicting `AX_PlaneCurveAffine_nonempty` at `PlaneCurve.lean:103`), it must have positive degree in *at least one* of $X$ or $Y$. (This crucially handles cases like $F=X$, where the $X$-projection is a single point $\{0\}$, which is bounded.)
   - **Case 1:** $F(X,Y,1)$ has positive degree in $Y$. The leading coefficient in $\mathbb{C}[X]$ is a non-zero polynomial and thus has finitely many roots. For any $x \in \mathbb{C}$ that is not a root of this leading coefficient, the univariate polynomial $F_x(Y)$ has a root by `Complex.exists_root` (the same lemma used at `Hyperelliptic/Basic.lean:95`). Thus the image of $\pi_x$ is cofinite, and therefore unbounded.
   - **Case 2:** $F(X,Y,1)$ has positive degree in $X$. By a symmetric argument, the leading coefficient in $\mathbb{C}[Y]$ has finitely many roots, and the image of $\pi_y$ is cofinite, and therefore unbounded.
   - Conclude that at least one projection has an unbounded image.

4. **Sub-step 4 — assemble the `NoncompactSpace` proof.** Mirror `Hyperelliptic/Basic.lean:108–129` but branch on which projection is unbounded:
   ```lean
   instance AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
       NoncompactSpace (PlaneCurveAffine H) := by
     refine ⟨?_⟩
     intro hcompact
     -- from Sub-step 3, extract the unbounded projection π ∈ {π_x, π_y}
     -- have hπ : Continuous π := ...
     -- have himage_unbounded : ¬ IsCompact (π '' Set.univ) := ...
     exact himage_unbounded (hcompact.image hπ)
   ```
   Uses the fact that a compact subset of `ℂ` is bounded, hence a cofinite subset of `ℂ` cannot be compact.

5. **Discharge.** In `Jacobians/ProjectiveCurve/PlaneCurve.lean` lines 118–124, replace
   ```lean
   axiom AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
       NoncompactSpace (PlaneCurveAffine H)
   attribute [instance] AX_PlaneCurveAffine_noncompact
   ```
   with the explicit `instance` from Sub-step 4.

**Next discrete deliverable.** Land Sub-step 1: build the bounded `MvPolynomial` infrastructure required to treat an arbitrary 3-variable homogeneous polynomial (evaluated at $Z=1$) as an element of `Polynomial (Polynomial ℂ)`, complete with leading-coefficient extraction.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace `axiom AX_PlaneCurveAffine_noncompact` (lines 118–124) with an `instance`. Add the projection and bounding lemmas.
- `Jacobians/ProjectiveCurve/MvPolynomialHelpers.lean` (or similar new/existing utility file) — land the `MvPolynomial (Fin 3) ℂ` -> `Polynomial (Polynomial ℂ)` bridge infrastructure.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurve.instCompactSpace` (`PlaneCurve.lean:170`) — note this is unrelated downstream but its existence at all relies on the axiom being either present or replaced; verify that the project's `axiom_report` / `gate.py` no longer lists `AX_PlaneCurveAffine_noncompact`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Mathlib's `MvPolynomial` API is notoriously difficult for extracting degrees and coefficients across different ring viewpoints. If creating the `Polynomial (Polynomial ℂ)` bridge requires extending fundamental Mathlib algebra hierarchies, escalate.
- If the required non-empty topological conditions fundamentally conflict with the definition of `H.h_smooth` at `PlaneCurve.lean:52` in a way not handled by `AX_PlaneCurveAffine_nonempty`, escalate.

## Gemini critique addressed:
- **Route and Effort upgraded:** Reclassified from `provable-from-other-axioms` to `needs-infra`, and increased effort to 8 due to the significant `MvPolynomial` boilerplate needed to extract leading coefficients.
- **Symmetrized projection argument:** Fixed the fatal logical flaw in the original proof by acknowledging that the $X$-projection is not always cofinite (e.g., vertical curves like $F=X$), and modified the proof to branch on whether the $X$- or $Y$-projection provides the cofinite bound.
- **Shortcut Alternative removed:** Deleted the "shortcut alternative" involving coordinate scaling, as it mathematically fails to bypass the degree-counting requirement.
- **Addressed the $F=Z$ edgecase:** Explicitly noted that `AX_PlaneCurveAffine_nonempty` is structurally load-bearing for this proof, as the $F=Z$ plane curve has an empty affine patch which *is* topologically compact.

---
**Vetting trail.** Critique: `_vetting/AX_PlaneCurveAffine_noncompact.md`. Verdict: reject. Revised: 2026-06-03.