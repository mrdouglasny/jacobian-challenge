# Research — cheapest Lean path to `exists_periodLattice_realBasis` (#7)

**Question.** The period lattice of a genus-`g` compact Riemann surface is a *full-rank* lattice
in `ℂ^g` — the `2g` period vectors over an `H₁(X;ℤ)` basis and a basis of holomorphic 1-forms are
ℝ-linearly independent. Classically this is the **Riemann bilinear relations** (in particular the
positivity `(i/2)∮∮_X ω∧ω̄ > 0`). Mathlib has neither de Rham cohomology of manifolds nor Hodge
theory. What is the cheapest Lean path *today*?

## Bottom line

**Do it via Riemann's classical "cut-surface + Green's theorem" proof — NOT Hodge/de Rham.**
Manifold de Rham cohomology is **not needed at all** for this statement; the Hodge route
(Forster/Miranda) is strictly more expensive. Estimated **~2,000–4,000 Lean LoC**, dominated by
"Green's theorem on the `4g`-gon". **Not blocked** on anything Mathlib refuses to have.

## The proof to formalize (Riemann ≈1857; Siegel; Springer pp.139–141; Griffiths–Harris pp.231–232)

1. Cut `X` along a canonical symplectic homology basis `a₁..a_g,b₁..b_g` (`aᵢ·bⱼ=δᵢⱼ`) into a
   `4g`-gon 2-cell `S₀` with boundary word `a₁b₁a₁⁻¹b₁⁻¹⋯a_g b_g a_g⁻¹b_g⁻¹`.
2. On the simply-connected `S₀`, a holomorphic `ω` has a single-valued primitive `f`, `df=ω`.
3. **Green's theorem on the planar 2-cell**: `∮_{∂S₀} f·η = ∬_{S₀} d(f·η) = ∬_{S₀} ω∧η = 0`.
   The four-edge boundary bookkeeping collapses this to the **first** bilinear relation
   `∑ₖ(A_k B_k' − B_k A_k') = 0` (`A_k=∮_{aₖ}ω`, etc.).
4. With `η = ω̄`: `−i∮_{∂S₀} f̄·ω = −i∬_{S₀} ω̄∧ω = ∬_{S₀} 2|f'|² dx dy > 0` — the **positivity** /
   second relation. Strict because `ω≠0` on an open dense set. This Hermitian positive-definiteness
   is *exactly* full-rank: a nonzero real relation among the `2g` period vectors yields a nonzero
   `ω` plugged into the positivity giving `0>0`.

**Key point:** every integral is over the *planar* `S₀` or `∂S₀`. The analytic engine is Green's
theorem on a planar region — **no abstract manifold de Rham, no Hodge `*`-operator, no harmonic
forms.**

## Mathlib status (May 2026)

**Present & usable:**
- **2-D Green's theorem (divergence form)**: `MeasureTheory.Integral.DivergenceTheorem`
  (`integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`,
  `integral2_divergence_prod_of_hasFDerivAt_off_countable`) — literally `∮_{∂rect}=∬_rect` on a
  rectangle, with a countable exceptional set allowed.
- **Exterior-derivative calculus on normed spaces**: `Analysis.Calculus.DifferentialForm.Basic`
  (`extDeriv`, `extDeriv_extDeriv` (d²=0), `extDeriv_pullback`). (Not on manifolds — but the proof
  is chart-local, so that's fine.)
- **Complex analysis**: rectangle Cauchy–Goursat (`Complex.integral_boundary_rect_eq_zero…`),
  disc Cauchy formula, `DifferentiableOn.analyticOn`, `circleIntegral`. `integral_pos` for the
  positivity.

**⚡ CORRECTION (2026-05-31, found while building):** Mathlib has MORE than this report first
concluded. `Mathlib.MeasureTheory.Integral.CurveIntegral` provides `curveIntegral` (`∫ᶜ x in γ, ω x`)
with concat/symm/additivity, AND **homotopy-invariance of closed-form curve integrals**
(`curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`, Poincaré, via unit-square pullback). The
**single-valued primitive on a convex set** is `Convex.exists_forall_hasDerivWithinAt`
(`…CurveIntegral.Poincare`); `Mathlib.Analysis.Complex.HasPrimitives` adds Morera/`IsConservativeOn`.
So the "homotopy invariance / primitive" gap below is **CLOSED** for the normed-space (= cut-box)
setting. Still genuinely absent:
- **Green's theorem on the `4g`-gon** — but the box-image cut-surface model (see the build plan)
  avoids this: pull back to `[0,1]²` and use the box divergence theorem / `curveIntegral`.
- **Surface integration over `X`** as a manifold + the **cut-surface chart / boundary word** (the
  topological dissection) — these stay isolated (Pillar T).
- **Manifold de Rham cohomology / Hodge theory**: ABSENT, **no open PR**, "known gap" on the Lean
  blog for years — but **not needed for this statement**.

**External reference (do not vendor):** arXiv:2605.01028 (Hulak–Ramos–de Queiroz, *Stokes' Theorem
for Smooth Singular Cubes in Lean 4*, May 2026; repo `d0d1/lean-stokes-theorem`, **GPL-3.0**) has
box Stokes + four-edge Green corollaries bridged to Mathlib's `extDeriv`/divergence theorem —
useful as a *reference* for the boundary bookkeeping, but GPL blocks copying into this Apache repo.

## Recommended decomposition (keystone lemmas)

1. `greenOnPolygon` — Green on the `4g`-gon from Mathlib's rectangle Green (subdivide + cancel).
   **~800–1500 LoC** (the principal cost).
2. `exists_primitive_on_simplyConnected` — single-valued primitive on the contractible cut surface.
   **~400–800 LoC**.
3. `canonicalDissection` — the topology (`4g`-gon, boundary word, period jumps). **Take as
   hypotheses** (symplectic basis + 2-cell + boundary word), matching how this repo already takes
   `IsClosedSmoothLoop`/`PreimageCycle`/`MonodromyLiftFamily` data — this dodges Mathlib's thin
   surface-topology API and keeps the hard core on Green's theorem. **~0–1200 LoC** depending on
   how much is assumed vs. proven.
4. Final assembly (two relations + "positive-definite Hermitian ⟹ `2g` vectors ℝ-independent"):
   linear algebra + `MeasureTheory.setIntegral_pos`. **~300–600 LoC**.

**The one decision to make consciously:** how much of the canonical dissection to *assume* vs.
*prove*. Assuming it (low-risk, repo-consistent) keeps the proof's hard core squarely on Green's
theorem on a polygon.

## Sources
- Chai, *The period matrices and theta functions of Riemann*, §1.4 (cut-surface + Green sketch,
  boundary word, both relations) — https://www2.math.upenn.edu/~chai/papers_pdf/riemann_combined_v2.pdf
- Griffiths–Harris Ch. 2 pp. 231–232; Springer pp. 139–141; Siegel Vol. I Ch. 3 §3 (Strategy A).
- Forster §§19–21 / Miranda (Strategy B, Hodge `*` / harmonic — *more* expensive, avoid).
- Mathlib `DivergenceTheorem.lean`, `DifferentialForm/Basic`, `CauchyIntegral` (see status above).
- arXiv:2605.01028 (Lean Stokes for singular cubes, GPL — reference only).
