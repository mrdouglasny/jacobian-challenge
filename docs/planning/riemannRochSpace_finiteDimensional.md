# `riemannRochSpace_finiteDimensional` — discharge recipe

**Statement.** On a compact (connected) Riemann surface `X`, the Riemann–Roch
space `L(D) = riemannRochSpace D = { meromorphic f : div f + D ≥ 0 }` is
finite-dimensional over ℂ, for **every** divisor `D`:
```
@[instance] axiom riemannRochSpace_finiteDimensional {X} [compact RS X]
    (D : Divisor X) : FiniteDimensional ℂ (riemannRochSpace D)
```
**Location:** introduced for the Forster-route Tier-1 program
(`docs/planning/FORSTER_ROUTE_PLAN.md` §5b). `riemannRochSpace` is the de-opaqued,
vetted-faithful germ-quotient model of `L(D)`.

**Route:** mathlib-soon / needs-infra (the analytic engine is vendored; the
extension is new). &nbsp; **Effort:** 5 &nbsp; **Est:** ~2–4 focused weeks.
**Blocked by:** nothing on the critical path — it reuses already-vendored Kirov
Montel machinery; the new work is re-targeting that engine from `Ω¹` to `O_D`.

## Why it's a pin (an axiom) right now

This is **Forster §14 finiteness** specialized to `H⁰(O_D) = L(D)`. It is a true,
classical, citable theorem (Forster, *Lectures on Riemann Surfaces*, §14; Miranda
Ch. VI; Mumford). It is asserted now (not proved) so the Tier-1 kill program can
run on the audited RR/Serre base: `AX_RiemannRoch` takes `[FiniteDimensional H0]`,
`[FiniteDimensional H1]` as instance hypotheses, and without an `L(D)`-finiteness
fact those brackets cannot be filled. This pin fills the `H0` side directly
(`H0 (O_D) = riemannRochSpace D`); the `H1` side is **derived**, not axiomatized
(see below). It also discharges the existing `sorry` at
`RiemannRochAPI.lean:544`.

## Vetting (Gemini deep-think, 2026-06-07)

- **(a) Typed:** correct — `FiniteDimensional ℂ (riemannRochSpace D)` is the right
  Mathlib statement. *Lean note:* must be tagged `@[instance]` so `AX_RiemannRoch`
  resolves it; the `AddCommGroup`/`Module ℂ` instances on `riemannRochSpace D`
  must already be registered (they are — the prior `sorry`-theorem typechecked).
- **(b) Strength:** correct — quantifying over **all** `D` is exactly right; it
  covers `K`, `K−D`, negative-degree (`L(D)=0`), effective, etc.
- **(c) Non-vacuous / true:** correct — classical; on a *compact* surface `L(D)`
  is always finite-dimensional, no edge cases.
- **(d) Satisfiable / no inconsistency:** correct, with one caution it raised —
  *do not* try to obtain H¹-finiteness from a Serre axiom that itself demands
  H¹-finiteness (Catch-22). **Averted here:** `AX_SerreDuality` is stated as a bare
  `Nonempty (H¹(O_D) ≃ₗ[ℂ] Dual (H⁰(O(K−D))))` with **no** finiteness hypothesis,
  so H¹-finiteness is *derived* (finite `L(K−D)` → finite dual → transport across
  the equiv) and fed only to `AX_RiemannRoch`. No companion axiom required.
- **(e) Module instances:** ensure present before stating (they are).

Rating: **Standard** (textbook §14 finiteness over a vetted-faithful `L(D)`).
Sources: DT (deep-think), LP (Forster §14). Non-vacuous, correctly typed,
sufficient.

## Discharge strategy (how to retire the pin)

The single deep analytic input is **Forster §14**: `dim H¹(X, O) < ∞` (whence
`dim H⁰(O_D) < ∞`) via local `∂̄`-solvability (Dolbeault) + Schwarz' lemma +
Montel/normal-families compactness. The project already holds the **`L(K)` case**:
`FiniteDimensional ℂ (HolomorphicOneForm X)` is a theorem
(`Bridge/KirovHolomorphic.lean`, transferred from Kirov's Montel-derived
`FiniteDimensional ℂ (Vendor.Kirov.HolomorphicOneForms X)`). So the engine exists;
the task is to re-target it from `Ω¹` to `L(D)`.

1. **Identify the Kirov finiteness lemma's generality.** Inspect
   `Jacobians/Vendor/Kirov/Montel/*` + `Bridge/KirovHolomorphic.lean`: does the
   Montel/normal-families argument yield finite-dimensionality of *bounded
   holomorphic sections of a line bundle* generally, or only the cotangent case?
   If general, `L(D)` finiteness is a near-direct instantiation.
2. **Bound `L(D)` by a compactness/normal-families argument.** `L(D)` embeds into a
   space of meromorphic functions with prescribed pole bound; the unit ball is
   relatively compact (Montel) and the subspace is closed, forcing finite
   dimension (a bounded-below + closed + locally-compact ⇒ finite-dim argument,
   the Riesz lemma form Kirov already uses for `Ω¹`).
3. **Bridge to `riemannRochSpace D`.** As with the `Ω¹` bridge, transport finiteness
   along an injective ℂ-linear map `riemannRochSpace D →ₗ[ℂ] (Kirov section space)`,
   or prove it intrinsically on the germ-quotient model.
4. Replace the axiom with the resulting `instance` theorem; update `AXIOM_AUDIT.md`.

This is the **Tier-3 entry cost** named in `FORSTER_ROUTE_PLAN.md` §0: the genuine
structure-sheaf finiteness. It is reused by every RR/Serre consequence, so it is
the right thing to pin first and discharge once.

## References

- Otto Forster, *Lectures on Riemann Surfaces* (GTM 81), §14 (Finiteness Theorem),
  §16 (Riemann–Roch). `refs/forster-riemann-surfaces/`.
- Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VI.
- David Mumford, *Abelian Varieties*, II.2.
- Project: `Jacobians/Bridge/KirovHolomorphic.lean` (the `Ω¹` precedent);
  `Jacobians/Vendor/Kirov/Montel/*` (the engine).
