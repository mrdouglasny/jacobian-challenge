# `AX_PluckerFormula` — discharge recipe

**Location:** `Jacobians/Axioms/PluckerFormula.lean:55`
**Route:** genuine-textbook &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~4-6 focused weeks, ~800 LOC (analytic construction of explicit 1-forms, avoiding algebraic sheaf cohomology)
**Blocked by:** PlaneCurve

**Statement (verbatim):**
```lean
axiom AX_PluckerFormula (H : PlaneCurveData) :
    genus (PlaneCurve H) = (H.d - 1) * (H.d - 2) / 2
```

**Why it's an axiom right now:** The axiom depends on the `PlaneCurve` type itself, which is currently an axiom (`Jacobians/ProjectiveCurve/PlaneCurve.lean:161`) pending the three-chart atlas plan in `docs/plane-curve-atlas-plan.md`. Genus is defined analytically as `Module.finrank ℂ (HolomorphicOneForm X)` (`Jacobians/RiemannSurface/Genus.lean:39`). Proving the formula requires explicitly bridging this analytic genus definition with the degree of the defining polynomial, bypassing the heavy sheaf cohomology machinery that was originally thought necessary.

**Proof recipe**

Reference: **Miranda, *Algebraic Curves and Riemann Surfaces*, Ch VII.1**, or **Griffiths–Harris, *Principles of Algebraic Geometry*, Ch 1.1** (direct computation via explicit basis of holomorphic 1-forms / Poincaré residue).

1. **Explicit forms on the affine patch.** For a smooth plane curve $X$ defined by $F(x,y,z) = 0$, work on the affine patch $z = 1$ where the curve is $F(x,y,1) = 0$. For a polynomial $P(x,y)$, define the explicit differential 1-form:
   $\omega_P = \frac{P(x,y) \, dx}{\partial F / \partial y}$.
2. **Holomorphicity bound.** Prove analytically (using the existing `ContDiff` / `Manifold` infrastructure) that $\omega_P$ has no poles on the affine patch, and that it extends to a globally holomorphic 1-form on the compact Riemann surface $X \subset \mathbb{P}^2$ if and only if $\deg(P) \le d-3$.
3. **Basis of global sections.** Show that the map $P \mapsto \omega_P$ is an injective $\mathbb{C}$-linear map into `HolomorphicOneForm X`. Prove surjectivity: any globally holomorphic 1-form on $X$ must be of this form (by analyzing the order of poles at infinity if a higher-degree polynomial or non-polynomial meromorphic function were used).
4. **Dimension count.** Since $\omega_P$ span `HolomorphicOneForm X`, the genus is exactly the dimension of the complex vector space of polynomials in two variables of degree $\le d-3$. 
5. **Assemble.** Compute the dimension of the space of polynomials:
   $\dim_{\mathbb{C}} \{ P \in \mathbb{C}[x,y] \mid \deg(P) \le d-3 \} = \frac{(d-1)(d-2)}{2}$.
   Apply this to `Module.finrank ℂ (HolomorphicOneForm X)` (`Jacobians/RiemannSurface/Genus.lean:39`) to conclude the proof.
6. **Replace axiom with theorem in `Jacobians/Axioms/PluckerFormula.lean`** (drop the `axiom` keyword; statement signature is unchanged).

**Next discrete deliverable:** Steps 1 and 2 — define the explicit local form $\omega_P$ on the charts of the `PlaneCurve` atlas, and prove the necessary and sufficient condition $\deg(P) \le d-3$ for it to be a valid, globally well-defined element of `HolomorphicOneForm X`. 

**Files touched**
- `Jacobians/Axioms/PluckerFormula.lean` — replace `axiom AX_PluckerFormula` with `theorem AX_PluckerFormula`, body per step 5.
- `Jacobians/ProjectiveCurve/PlaneCurveForms.lean` (new) — explicit construction of $\omega_P$, holomorphicity bounds, and the linear equivalence between `HolomorphicOneForm X` and polynomials of degree $\le d-3$.

**Acceptance**
- `lake build Jacobians.Axioms.PluckerFormula` succeeds.
- `#print axioms AX_PluckerFormula` no longer lists `AX_PluckerFormula` (i.e. it lists only its still-axiomatic dependencies, which should be limited to `PlaneCurve`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Signature change required: if the `PlaneCurve` discharge forces `genus` to be defined relative to a `ChartedSpace`/`IsManifold` instance that turns out incompatible with the `OnePoint` compactification used in `Jacobians/ProjectiveCurve/PlaneCurve.lean:17`, the statement of `AX_PluckerFormula` itself may need to be re-stated against a different type.
- Surjectivity of $P \mapsto \omega_P$ (Step 3) turns out to be extremely difficult to prove purely via elementary local chart calculations and requires missing algebraic geometry infrastructure (e.g. Riemann-Roch) — escalate if this blocks progress.

### Gemini critique addressed:
- **Route Reclassified**: Changed from `needs-infra` to `genuine-textbook`.
- **Methodology Replaced**: Scrapped the algebraic sheaf cohomology / adjunction approach, which suffered from a fatal GAGA gap by improperly equating analytic and algebraic sheaf cohomology. 
- **Proof Recipe Rewritten**: Followed the recommendation to compute the genus explicitly using the Poincaré residue forms $\omega_P$, counting the dimension of polynomials of degree $\le d-3$.
- **Effort/Citations Updated**: Adjusted the time/LOC estimates and changed the textbook references from pure algebraic schemes (Mumford) to complex algebraic curves (Miranda Ch VII.1).

---
**Vetting trail.** Critique: `_vetting/AX_PluckerFormula.md`. Verdict: reject. Revised: 2026-06-03.