# Gemini 2.5 Pro review — Genus theorem framework (S6/S7 progress)

Date: 2026-04-26.
Reviewer: `gemini-2.5-pro` via `query_deep_think.py` (CLI script).
Scope: review of the recent S6 (linearity) + S7 (injectivity, linear independence) work
on `hyperellipticForm`, including the unsoundness fix to the cross-summand axioms.

---

## Executive Summary (Gemini)

> The project is in a very strong state. The core logic for constructing and
> distinguishing differential forms is now sound and sorry-free.
>
> 1. **Soundness:** The witness construction (A) is sound. The concerns about
>    `Relation.EqvGen` are unfounded; the argument is tight.
> 2. **Type-Theoretic Nuance:** The unconditional injectivity result (B) is
>    mathematically correct but reveals a subtle "philosophical soundness" issue.
>    The type `HolomorphicOneForm` is more of a "candidate form" until the gluing
>    condition is proven.
> 3. **Previous Concerns:** The fix for the cross-summand axioms (C) is robust
>    and has successfully eliminated the soundness gap.
> 4. **Proof Architecture:** The linear independence proof (D) is solid. There
>    is a slightly more idiomatic Mathlib alternative (`Polynomial.degreeLT.basis`).
> 5. **Next Steps:** Tackling the Riemann-Roch upper bound (E) is a monumental
>    task. The far more pragmatic and valuable next step is to discharge the
>    `hGluing` cocycle condition for low-degree polynomials.

## (A) Witness construction — sound

For `a₀ = (0, ±√H.f(0))`, the gluing relation `HyperellipticEvenGlue` is
defined only when `a.val.1 ≠ 0`, so `Sum.inl a₀` is an isolated vertex
in the relation graph. `Relation.EqvGen` cannot create non-trivial chains
without edges. So the equivalence class is `{Sum.inl a₀}`, and
`Quotient.out (Quotient.mk _ (Sum.inl a₀)) = Sum.inl a₀`. Tight.

## (B) Unconditional injectivity — partial soundness gap

Gemini characterized the situation as a "philosophical" gap: the type
`HolomorphicOneForm` behaves more like a "candidate form" until the
gluing condition is proven. They argued the cross-summand axiom becomes
`False → Q` for high-degree `g_aff`, hence vacuously true.

**Claude's note (review of the review):** Gemini's "vacuously true" reasoning
is incomplete. The hypothesis `hGluing : g_inf = infReverse H g_aff` is just
a polynomial equation, and is **always true** in the constructor where we
set `g_inf := infReverse H g_aff`. So the axiom is invoked with `hGluing`
TRUE, not vacuously satisfied.

The cocycle CONCLUSION of the axiom, however, is mathematically false for
high-degree `g_aff`. So the axiom is genuinely unsound: it asserts a false
statement under satisfiable hypotheses.

The exploitability is mitigated by `Quotient.out` being non-computable
(constructing specific (q, q', a, b) witnesses with the right Quotient.out
values is non-trivial), but the soundness gap is a real liability.

**Recommended fix:** Add a degree bound `(hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)`
to both cross-summand axioms. Refactor `hyperellipticForm` to take this
bound (or restrict to a subtype of low-degree polynomials).

This converges with Gemini's recommendation in (E): discharging the cocycle
for low-degree polynomials would replace the axioms with real proofs (only
valid for low-degree g), and the soundness issue goes away.

## (C) Previous fix (gluing-hypothesis) — confirmed good

The change from unconditional axioms to ones taking `hGluing` as a hypothesis
correctly addressed the previously-flagged unsoundness — at least up to the
issue identified in (B) above.

## (D) Linear independence proof — solid, alternative available

Current path: `Polynomial.basisMonomials` → `Fin.val_injective` restriction →
`LinearMap.linearIndependent_iff` with `LinearMap.ker_eq_bot`. Standard and
correct.

**Mathlib alternative:** `Polynomial.degreeLT ℂ n` is the subspace of
polynomials of degree < n with a `Basis (Fin n)` available as
`Polynomial.basisDegreeLT`. Starting from this basis is slightly more
idiomatic: it works directly in the finite-dimensional space we actually
care about. Refactor recommended but not high-priority.

## (E) Next steps — discharge the cocycle, defer Riemann-Roch

**Riemann-Roch path:** 6-12 months. Requires divisors, line bundles,
sheaf cohomology, and proofs of Riemann-Roch + Serre duality. Substantial.

**Cocycle discharge path:** 1-3 weeks. Self-contained calculation showing
that for low-degree `g`, the local form `g(x) dx/y` transforms correctly
under `x = 1/z`. Polynomial degree analysis + manipulation of Laurent series
+ careful bookkeeping. The mathematical core of the genus problem.

> **Strongly pursue the cocycle discharge.** This is the natural and necessary
> next step to solidify the foundation you have built. It bridges the gap
> between your `CandidateOneForm` construction and the actual space of
> holomorphic forms, directly enabling the completion of the genus theorem.
> Leave the full Riemann-Roch theorem for a future, more ambitious project.

## Action items

1. **Add the degree bound to the cross-summand axioms** (per (B), Claude's note).
   Quick fix: ~1 day. Restores soundness rigorously.
2. **Discharge the cocycle for low-degree polynomials** (per (E)).
   Major next milestone: 1-3 weeks. Replaces axioms with real proofs.
3. *(Optional)* Consider renaming `HolomorphicOneForm` to `CandidateOneForm`
   per Gemini (B) recommendation. Architectural improvement; lower priority.
4. *(Optional)* Refactor linear independence to use `Polynomial.basisDegreeLT`
   per (D). Lower priority.
