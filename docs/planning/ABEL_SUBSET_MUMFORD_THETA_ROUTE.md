# Abel's theorem, ⊆ direction (Jacobi inversion) — Route B: Mumford theta

*2026-06-07. Alternative discharge plan for the **hard** half of `AX_AbelTheorem`:*
```
ker(abelJacobiDiv X) ⊓ (Divisor.deg X).ker  ⊆  PrincipalDivisors X
```
*Companion to Route A ([`ABEL_SUBSET_FORSTER_ROUTE.md`](ABEL_SUBSET_FORSTER_ROUTE.md)).
The ⊇ direction is [`ABEL_SUPSET_LIOUVILLE_ROUTE.md`](ABEL_SUPSET_LIOUVILLE_ROUTE.md).*

Reference: Mumford, *Curves and their Jacobians* / *Tata Lectures on Theta* I–II;
Griffiths–Harris Ch. 2.7 (the theta function and Riemann's theorem).

## Strategy in one paragraph

Equip `Jacobian X = ℂ^g/Λ_τ` with the **Riemann theta function**
`θ_τ : ℂ^g → ℂ`, convergent because `τ ∈ SiegelUpperHalfSpace` (`Im τ ≻ 0`).
Its zero locus, the **theta divisor** `Θ`, is (Riemann's theorem) a translate of
`W_{g−1} = u(Sym^{g−1} X)`. From this one reads off both halves of the
Pic⁰-Jacobian isomorphism: **Jacobi inversion** (surjectivity — every class is
`u` of an effective degree-`g` divisor) and **Abel injectivity** (our ⊆: `u(D)=0`,
`deg D=0` ⟹ `D` principal). The whole argument is multivariable complex analysis
of `θ_τ`; it **never touches Riemann–Roch or Serre duality**.

## Prerequisites

**Shared with Route A:**
- `AX_AnalyticCycleBasis` (symplectic basis) — axiom, deep.
- `AX_RiemannBilinear` — axiom; **here the load-bearing facet is
  `τ ∈ SiegelUpperHalfSpace` (`Im τ ≻ 0`)**, which is exactly Riemann's *second*
  bilinear relation and is precisely the convergence condition for `θ_τ`. (Note:
  our axiom already delivers `τ ∈ SiegelUpperHalfSpace` by type — so the
  positivity Route B needs is *given*.)
- `AX_PeriodLattice` (`Λ` full ℤ-lattice).

**Route-B-specific (the big one):** a **multivariable Riemann theta** layer,
which Mathlib does **not** have (it ships only `jacobiTheta` in 1 and 2
variables — `Mathlib/NumberTheory/ModularForms/JacobiTheta/{OneVariable,TwoVariable}.lean`).
We must build, for general `g`:
1. `θ_τ(z) := ∑_{n ∈ ℤ^g} exp(πi nᵀτn + 2πi nᵀz)` — definition + **convergence**
   from `Im τ ≻ 0` (the hard analytic estimate; the 1-var proof in Mathlib is a
   template but the `g`-var lattice sum needs `Im τ` positive-definite bounds).
2. **Quasi-periodicity:** `θ_τ(z + m + τn) = exp(−πi nᵀτn − 2πi nᵀz)·θ_τ(z)` for
   `m,n ∈ ℤ^g` — so the zero locus descends to a well-defined divisor `Θ` on
   `ℂ^g/Λ_τ`.
3. **`θ_τ ≢ 0`** and `Θ` is an honest codimension-1 analytic divisor.
4. **Riemann's theorem:** `Θ = u(Sym^{g−1} X) + κ` for the Riemann constant `κ`;
   equivalently `θ(u(D − P₀·(g−1)) + κ) = 0 ⟺ D` effective/special.

## Recipe (Mumford §II.3.3–II.3.5)

1. **Build `θ_τ`** with the four properties above (the infrastructure layer).
2. **Jacobi inversion (surjectivity).** For generic `e ∈ ℂ^g`, the function
   `P ↦ θ_τ(u(P) − e + κ)` on `X` is not identically zero and has exactly `g`
   zeros `P₁,…,P_g` (counted via the argument principle against `θ`'s
   quasi-periodicity — reuses our `weightedFiberConservation`/period machinery).
   Then `u(P₁+…+P_g) = e`. Hence `u : Sym^g X → Jac` is surjective.
3. **Abel injectivity (our ⊆).** Suppose `u(D) = 0`, `D = D⁺ − D⁻` degree 0,
   `deg D⁺ = deg D⁻ = m`. By surjectivity (Step 2) pick an effective `E` of
   degree `g − m` generic; then `D⁺ + E` and `D⁻ + E` are effective of degree
   `g` with `u(D⁺+E) = u(D⁻+E)` (since `u(D)=0`). Riemann's theorem (Step-1
   property 4) identifies the fibers of `u : Sym^g X → Jac` over a generic point
   as a single linear system `|D⁺+E|`; `D⁺+E` and `D⁻+E` lie in it, so they are
   linearly equivalent: `D⁺+E ∼ D⁻+E`, hence `D⁺ ∼ D⁻`, i.e.
   `D = D⁺ − D⁻ ∈ PrincipalDivisors X`. Mumford §II.3.5; Griffiths–Harris p. 235–245.

## Lean decomposition

| File | Proves | Mathlib base |
|------|--------|--------------|
| `RiemannTheta.lean` (~800–1200) | `θ_τ` def + convergence (`Im τ ≻ 0`) + quasi-periodicity + `θ ≢ 0` | `jacobiTheta` (1-var) as template; **g-var from scratch** |
| `ThetaDivisor.lean` (~600–900) | `Θ` is a divisor; Riemann's theorem `Θ = W_{g−1}+κ` | the above + `weightedFiberConservation` |
| `JacobiInversion.lean` (~400) | `u : Sym^g X → Jac` surjective | argument principle vs `θ` |
| `AbelSubsetMumford.lean` (~250) | `ker ⊓ deg-0 ⊆ PrincipalDivisors` | the above |

Existing scaffolding: `Jacobians/AbelianVariety/Siegel.lean` (Siegel upper
half-space) is a start; `Jacobians/AbelianVariety.lean` exists. Mathlib's
`jacobiTheta` (1-var) directly serves the **genus-1 base case** (a concrete
witness, parallel to how the elliptic witness anchored `ofCurve_inj`).

## Forster (A) vs Mumford (B) — the trade

| | Route A (Forster) | Route B (Mumford theta) |
|---|---|---|
| Extra prerequisite | `AX_RiemannRoch` + `AX_SerreDuality` (sheaf cohomology) | multivariable Riemann `θ` (analysis) |
| Mathlib support | none for the cohomology LES; **but** RR/Serre *statement APIs* already scaffolded (`RiemannRochAPI`/`SerreDualityAPI`, 10 sorries) | only 1- & 2-var `jacobiTheta`; **no** g-var |
| Shares `AX_RiemannBilinear`? | yes (A-normalization + reciprocity) | yes (`Im τ ≻ 0` for convergence) |
| Self-contained? | needs the whole sheaf-cohomology stack | yes, once `θ` is built — no RR/Serre |
| Genus-1 witness | elliptic (already have `ofCurve_inj` elliptic) | Mathlib 1-var `jacobiTheta` |
| Rough size | ~1200 assembly + multi-year RR/Serre/cohomology | ~2000–2700, mostly the `θ` layer |
| Conceptual risk | the cohomology infra touches the typeclass surface | `θ` convergence + Riemann's theorem are delicate but localized |

**Recommendation: prefer Route B (theta).** The two are not symmetric in
difficulty. Route A's extra prerequisite (RR + Serre) is *infrastructure Mathlib
structurally lacks* — sheaf-cohomology long exact sequences, Čech cohomology of
analytic sheaves, Serre finiteness via Fréchet/Montel function spaces — a
genuinely multi-year, interface-touching build. Route B's extra prerequisite is
**concrete and algebraic**: an explicit absolutely-convergent lattice series with
explicit transformation laws. Specifically —

- **Convergence** is a Gaussian bound from `Im τ ≻ 0`. Mathlib's 1-variable
  `jacobiTheta` *already proves exactly this* for the scalar case; the `g`-variable
  version replaces the scalar `Im τ > 0` with a positive-definite quadratic-form
  bound — more bookkeeping, not new mathematics.
- **Quasi-periodicity** is a one-line index-shift identity on the summation `ℤ^g`.
- `θ ≢ 0` and **Riemann's vanishing theorem** are delicate but are *classical
  complex analysis of an explicit function*, not new foundational infrastructure —
  and crucially they do **not** route through sheaf cohomology.

So the theta layer is "hard analysis on a concrete object," whereas RR/Serre is
"build a missing branch of Mathlib." For a route to Abel ⊆ that the *challenge*
actually needs, Route B is the better bet: it is **independent of RR/Serre**,
algebraic in character, and has a genuine **genus-1 base case** via Mathlib's
1-variable `jacobiTheta` to validate the approach before any general-`g` work.

Both routes still consume `AX_RiemannBilinear` + `AX_AnalyticCycleBasis` — the
unavoidable shared foundation. But Route B stops there; Route A adds the
sheaf-cohomology mountain.

## Honest assessment
Earlier framing called this "not obviously cheaper than Forster" — that
understated it. The theta function is an **explicit algebraic/analytic object**,
not a missing Mathlib subsystem, so Route B is plausibly the *more tractable*
path to Abel ⊆ despite the larger raw LOC, precisely because it sidesteps RR +
Serre. Recommended sequencing: **genus-1 elliptic validation first** (using
Mathlib `jacobiTheta`) to de-risk, then the general-`g` `θ` layer.
