# Mumford — Tata Lectures on Theta I

**Citation.** David Mumford, with the assistance of C. Musili, M. Nori, E. Previato, M. Stillman, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser Boston, 1983 (original); reprinted Springer 2007 as Modern Birkhäuser Classics. ISBN 978-1-4899-2845-0 (print) / 978-1-4899-2843-6 (eBook). DOI 10.1007/978-1-4899-2843-6.

**Provenance.** Obtained via Harvard institutional Springer access; stored in this repo under `refs/mumford-tata-theta-1/TataTheta1.pdf` for research use.

**Origin.** Notes from Mumford's lecture series at the Tata Institute (Oct 1978–Mar 1979); Chapter I further developed at Harvard (Fall 1979); Chapter II from lectures at a Montreal summer school (Aug 1980). Contains the first two of four planned chapters — Chapters III and IV appear in Volumes II and III.

**Approach.** Chapters I–II study theta functions strictly from the viewpoint of classical analysis; no algebraic geometry needed for this volume. Chapters III–IV (Vols II–III) add algebraic geometry and Heisenberg/Weil representation theory. This is the "analytic" volume and is precisely what aligns with Buzzard's challenge setup (`ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) ω X`).

## Structure (from TOC)

**Chapter I — Theta functions in one variable** (pp. 1–117). 18 sections + 2 appendices.

Covers: definition of `ϑ(z, τ)` and periodicity; `ϑ(x, it)` as fundamental periodic solution of the heat equation; Heisenberg group and theta characteristics; projective embedding of `ℂ/(ℤ + ℤτ)` via theta functions; Riemann's theta relations; doubly periodic meromorphic functions via `ϑ`; functional equation of `ϑ(z, τ)`; heat equation again; modular forms; geometry of modular forms; `ϑ` as a 2-variable automorphic form; interpretation of `H/Γ` as a moduli space; Jacobi's derivative formula; product expansion and applications; representation of an integer as sum of squares; theta and zeta; Hurwitz maps; Hecke operators.

**Chapter II — Theta functions in several variables** (pp. 118–243). 7 sections + 2 appendices.

Covers: definition of `ϑ(z, Ω)` with `Ω ∈ 𝔥_g` (Siegel upper half space); **the Jacobian variety of a compact Riemann surface (§2)**; **`ϑ` and function theory on a compact Riemann surface (§3)**; Siegel's symplectic geometry; `ϑ` as a modular form; generators of `Sp(2g, ℤ)`; Riemann's theta formula and theta functions associated to a quadratic form; theta functions with harmonic coefficients.

## Relevance to the Jacobian challenge

**This is the primary reference.** Chapter II §§2–3 build the Jacobian variety of a compact Riemann surface via theta functions, proving exactly the theorems we need to formalize Buzzard's challenge:

- Period matrix `Ω ∈ 𝔥_g` → lattice `Λ_Ω = ℤ^g + Ω·ℤ^g` → complex torus `X_Ω = ℂ^g / Λ_Ω` with explicit theta-function projective embedding. **Gives the entire instance soup** (`AddCommGroup`, `TopologicalSpace`, `T2`, `Compact`, `ChartedSpace`, `IsManifold`, `LieAddGroup`) on `Jacobian X` once `Ω(X)` is constructed.
- §II.2 constructs `Ω(X)` for a compact Riemann surface `X` via period integrals of a normalized basis of holomorphic 1-forms — this is our Phase B liability made concrete.
- §II.3 is the Abel-Jacobi + function-theory side: Abel's theorem (injectivity of `ofCurve`), Riemann's theorem on the theta divisor, explicit form of `pushforward`/`pullback` in terms of pull-back of differentials.
- Chapter I §4 (`ℂ/(ℤ + ℤτ)` via theta) is the genus-1 warm-up: formalizing it on its own is a self-contained sub-project that exercises all the theta-series machinery before attacking general `g`.

## Recommended path through the book for formalization

1. **I.§1–2** — basic theta series and its convergence (Mathlib-friendly: locally uniformly convergent exponential series).
2. **I.§4** — projective embedding of the elliptic curve (genus-1 warm-up, closes 1D case of `ChartedSpace (Fin 1 → ℂ)` etc.).
3. **II.§1** — the several-variables theta function on `ℂ^g × 𝔥_g`.
4. **II.§2** — Jacobian of a compact Riemann surface. **This is where the Phase B gaps (integration of holomorphic 1-forms on a Riemann surface) become blocking.**
5. **II.§3** — function theory on the Jacobian; Abel, Jacobi inversion, Riemann's theorem.
6. **II.App (§5)** — Siegel's `Sp(2g, ℤ)`-action on 𝔥_g (modular side, useful for the dual-Jacobian instance).

## Caveats

- Analytic style: Mumford uses classical-analysis language (power series, uniform convergence on compacta, elementary estimates). This matches Mathlib well — no scheme theory here.
- The "Jacobian via theta" path still needs `H⁰(X, Ω¹)` and `H_1(X, ℤ)` as input. These don't appear in Mathlib; Vol I §II.2 is a recipe, not a short-circuit.
- Chapter III (Jacobian theta functions, KdV) and IV (Heisenberg-Weil representation, abelian varieties over arbitrary fields) are in Vols II and III.
