# Anchor APIs for the deepest axioms (sheaf cohomology / RR / Serre / Plücker)

*2026-06-05. Methodology (MRD): for the research-grade axioms, the real risk is
**formulation**, not proof — the kernel checks proofs, never that a statement
MEANS the right thing, so a degenerate def compiles. So: pin a **faithful,
heavily-vetted API** — real definitions + theorem statements with `sorry`-ed
proofs — FIRST. Vet the statements very well; do the hard proofs LAST, against a
known-correct surface. Each cluster gets its own file.*

This extends the existing `RiemannSurface/SheafCohomologySpec.lean` (the Buzzard-
style **faithfulness acceptance suite**: non-vacuity A1–A3, structural pins S1–S3,
RR/Serre backbone B1–B2, ℙ¹ teeth C1–C2) from a Prop-level *spec* to **de-opaqued
anchors** — now possible because `MeromorphicFunctionField` + `divHom` exist.

## Current state (all opaque/axiomatized)
- `LineBundle`, `LineBundle.ofDivisor`, `H0`, `H1`, `canonicalDivisor` — **opaque
  axiom TYPES** (no content) in `RiemannSurface/LineBundle.lean`.
- `AX_RiemannRoch` : `finrank(H0 𝒪(D)) − finrank(H1 𝒪(D)) = deg D + 1 − g` (real ℤ
  statement, but about opaque H0/H1).
- `AX_SerreDuality` : `H1(𝒪(D)) ≃ₗ[ℂ] (H0(𝒪(K−D)))*`.
- `AX_PluckerFormula` : `genus (PlaneCurve H) = (d−1)(d−2)/2`.

## The anchor that de-opaques most of it: `L(D)` via the meromorphic function field

We can now DEFINE the Riemann–Roch space as a real `ℂ`-submodule:
```lean
/-- L(D) = global sections of 𝒪(D): meromorphic f with div f + D ≥ 0, plus 0. -/
def riemannRochSpace (D : Divisor X) : Submodule ℂ (… meromorphic functions …) :=
  { f | f = 0 ∨ (f ≠ 0 ∧ divHom f + D ≥ 0) }   -- as a ℂ-subspace
```
where `divHom f : Divisor X` (= `Σ orderAt p f · (p)`), `Divisor X = FreeAbelianGroup X`,
and `D' ≥ 0` means "effective" (all coefficients ≥ 0; need a `≤` / effective-divisor
predicate on `FreeAbelianGroup X` — anchor it: `Effective D := ∀ p, D.coeff p ≥ 0`
via `FreeAbelianGroup.lift`/`toFinsupp`). The ℂ-subspace structure: closed under
`+` (`div(f+g) ≥ min` — careful: `div(f+g) ≥ min(div f, div g)` so `f,g ∈ L(D) ⇒
f+g ∈ L(D)`) and scalar mult (`div(cf) = div f`). **FORMULATION TO VET:** the `+`
closure uses the ultrametric `orderAt(f+g) ≥ min(orderAt f, orderAt g)` — confirm
that's the right subspace condition and that `0` handling is clean.

Then **de-opaque `H0`**: `H0 (LineBundle.ofDivisor D) := riemannRochSpace D` (or a
`≃ₗ`), retiring the 3 opaque `H0` axioms and making `AX_RiemannRoch`'s `finrank H0`
become `finrank (riemannRochSpace D)` — a real dimension.

## Per-cluster anchor APIs (real defs + sorry-ed theorems, to VET)

### 1. `RiemannRochAPI.lean`
- `def riemannRochSpace D` (real, above); `H0 := riemannRochSpace`.
- `def canonicalDivisorClass` / anchor `K` with `theorem canonical_degree : deg K = 2*g − 2` (sorry).
- `theorem riemannRoch (D) : finrank ℂ (riemannRochSpace D) − finrank ℂ (riemannRochSpace (K − D)) = deg D + 1 − g` (sorry) — the **weak/strong RR in L(D)-only terms** (uses Serre to eliminate H1; avoids needing a separate H1 object). Cross-check vs the existing `AX_RiemannRoch` (h⁰−h¹ form).
- Corollaries (sorry): `h⁰(D) ≥ deg D + 1 − g`; `deg D > 2g−2 ⇒ h⁰(D) = deg D + 1 − g`; `h⁰(D)=1` for `g≥1` single point (the G3-relevant fact!).
- Faithfulness: reuse `SheafCohomologySpec` A1–A3/S1–S3/C1–C2 as the acceptance gate.

### 2. `SerreDualityAPI.lean`
- Either keep `H1` opaque with `theorem serre : H1(𝒪(D)) ≃ₗ[ℂ] (riemannRochSpace (K−D))*` (sorry), OR **DEFINE** `H1 (𝒪(D)) := (riemannRochSpace (K−D)) →ₗ[ℂ] ℂ` (Serre-dual form) — making H1 real and Serre definitional, leaving RR (above) as the one sorry. **DECISION TO VET:** define-H1-by-Serre (clean, fewer axioms, but bakes Serre in) vs keep-H1-opaque-with-Serre-iso (keeps Serre as a checkable target). Recommend the latter for honesty unless we want H1 real.

### 3. `PluckerAPI.lean` — ✅ COMPLETE (2026-06-06)
`plucker_genus` re-exports `AX_PluckerFormula` and the low-degree corollaries
(`_zero_of_deg_le_two`, `_cubic`, `_quartic`) are proved by ℕ-arithmetic — the
file is **sorry-free**. Plücker's anchor was thin: a single axiom with no
intermediate proof obligations, so the API holds no deferred targets. Remaining
Plücker work lives *below* the API: the formula axiom `AX_PluckerFormula`
(Bézout/adjunction) and the `PlaneCurve` three-chart atlas — both still on the
axiom list. (Original note retained: smoothness/irreducibility hypotheses on
`PlaneCurveData` rule out singular curves; the `ℕ`-division `/2` is exact since
`(d−1)(d−2)` is always even.)

### 4. Sheaf-cohomology faithfulness (mostly DONE)
`SheafCohomologySpec.lean` already encodes the acceptance suite. Anchor work: turn
its §4 "deepest pin" (documented target) into the real `riemannRochSpace`-based
statements, and wire A1/A2/S2 to the real `H0 := riemannRochSpace`.

## Vetting protocol (per the axiom-management rules)
For EACH anchored statement: (a) cite the textbook form (Forster *Lectures on RS*
§16/§17/§21; Griffiths–Harris Ch.2; Mumford; Miranda Ch.VI–VIII); (b) cross-model
vet (Gemini deep-think + Codex) — type-correct, non-vacuous, faithful, sufficient,
correct hypotheses; (c) record verdict in the file docstring + `AXIOM_AUDIT.md`;
(d) confirm the `SheafCohomologySpec` gate still passes. The whole point: a wrong
RR/Serre/Plücker STATEMENT is the failure mode; lock the statements before proofs.

## Sequencing
1. `riemannRochSpace L(D)` real def + the effective-divisor predicate + ℂ-subspace
   proof (REAL, no sorry — this de-opaques H0). **Highest value, now unblocked.**
2. De-opaque `H0 := riemannRochSpace`; restate `AX_RiemannRoch` against it; vet.
3. `RiemannRochAPI` theorem statements (sorry) + the `h⁰(P)=1`/`deg>2g−2` corollaries
   (these feed G3 and the genus bounds) — vet.
4. `SerreDualityAPI`, `PluckerAPI` statements (sorry) — vet.
5. (LAST) the hard proofs — Čech/Dolbeault for RR/Serre; Bézout/adjunction for Plücker.

Parallel-safe with the Abel-injectivity / categoricity lanes (disjoint files).
