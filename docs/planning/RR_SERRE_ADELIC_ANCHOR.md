# RR / Serre / sheaf-cohomology anchor — the adelic (Weil) route on curves

*2026-06-07. Design for a **new self-contained challenge** that Buzzard's
challenge's Tier-3 (RR / Serre / sheaf cohomology) reduces to. Goal: **proper
faithful definitions** of `LineBundle` / `H¹` / `canonicalDivisor` so the pinning
theorems (`SheafCohomologyFaithful`) are genuinely **provable**, not definitional.
Companion to the faithfulness spec in `RiemannSurface/SheafCohomologySpec.lean`.*

## Basic object: the compact Riemann surface `X` (1-d complex manifold), unchanged

Keep Buzzard's analytic `X` (`[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`,
compact/connected) so the anchor plugs into the existing tower. Do **not** abstract
to algebraic curves — that needs the Riemann-existence bridge (every compact RS is
projective algebraic), itself deep. We restrict to **curves (1-d)** for this
project; no schemes/higher-dim.

## Why algebraic (adelic), not analytic

A faithful `H¹` defined analytically (Dolbeault `∂̄`, Čech over Leray covers,
manifold integration) is the multi-year mountain Mathlib lacks. On a **curve**
there is a concrete *algebraic* model — Weil's **repartitions** (a simplified
adele) — built from data we already have (`MeromorphicFunctionField`, `orderAt`,
`Divisor`), with **no `∂̄`, no covers, no integration**, and it keeps Serre
duality a **theorem**.

## The definitions

Write `K_X := MeromorphicFunctionField X` (the function field; **prerequisite:
complete it to a `Field` — currently only a `CommGroup`**). Places = points `p : X`,
valuation `v_p := orderAt p`.

- **Repartition** `r : X → K_X` with `∀ᶠ p, orderAt p (r p) ≥ 0` (cofinitely many
  places have a non-negative-order entry). The ℂ-algebra of repartitions `𝔸_X`.
  *(Weil's form — valued in `K_X` itself, no local completions needed.)*
- **`𝔸_X(D)`** `:= { r | ∀ p, orderAt p (r p) ≥ −D(p) }` (a ℂ-subspace).
- **Diagonal** `K_X ↪ 𝔸_X`, `f ↦ (p ↦ f)` (principal repartitions).
- **`H⁰(𝒪(D)) := riemannRochSpace D`** (already real, over the corrected `MeroField`).
- **`H¹(𝒪(D)) := 𝔸_X / (𝔸_X(D) + image K_X)`** — a real ℂ-vector space ⇒
  `H1`/`AddCommGroup`/`Module` retire from axioms to defs.
- **`canonicalDivisor X := div(ω)`** for a meromorphic 1-form `ω` (from
  `HolomorphicOneForm` + meromorphic order). Well-defined up to linear equivalence.

## The pinning theorems (the new challenge — stated as `sorry`)

| Theorem | Statement | Needs |
|---|---|---|
| **Residue sum** | `∑_p res_p ω = 0` for meromorphic `ω` | local residues; the crux |
| **Serre duality** | residue pairing `H¹(𝒪(D)) × H⁰(Ω(−D)) → ℂ` is perfect | residue sum |
| **Riemann–Roch** | `h⁰(D) − h¹(D) = deg D + 1 − g` | adele-quotient dim count |
| **`deg K = 2g−2`** | `Divisor.deg X (canonicalDivisor X) = 2·genus X − 2` | RR at `D=K` + `H⁰(Ω)=g` |
| **ℙ¹ teeth** | `H⁰(𝒪(n·p)) ≅ ℂⁿ⁺¹`, `H¹(𝒪(D))=0` for `deg ≥ −1` | compute on `ProjectiveLine` |
| **§4 embedding** | `H⁰(𝒪(D)) ↪` meromorphic `f` with `div f + D ≥ 0` | now stateable (H0 is `MeroField`) |

Discharging these = the new challenge; on completion the `LineBundle`/`H1`/
`canonicalDivisor` axioms retire and `SheafCohomologyFaithful` is proved.

## File layout (`Jacobians/RiemannSurface/Cohomology/`)

| File | Real defs | Sorried pins |
|---|---|---|
| `FunctionFieldComplete.lean` | **complete `K_X` to a `Field`** (Add/Neg/AddCommGroup/Field) | field axioms (prereq) |
| `Repartitions.lean` | `𝔸_X`, `𝔸_X(D)`, diagonal `K_X ↪ 𝔸_X` | — |
| `Residue.lean` | local `res_p`, residue map | **`∑_p res_p ω = 0`** |
| `H1.lean` | `H¹(D) := 𝔸_X/(𝔸_X(D)+K_X)`, instances | finite-dim |
| `CanonicalDivisor.lean` | `K := div(ω)` | `deg K = 2g−2` |
| `RiemannRochAnchor.lean` | — | RR, Serre, ℙ¹ teeth, §4 embedding |

Then `LineBundle.lean`'s 6 axioms re-point to these defs.

## High-leverage observation

The **residue theorem `∑res ω = 0`** is the crux of adelic **Serre duality**
(perfectness of the residue pairing) — the *same* lemma that is the crux of
**Abel ⊇** (bypassed via Liouville, Discussion #100) and the **Forster route to
Abel ⊆**. So `Residue.lean` is the single highest-leverage build: it unlocks Serre
*and* Forster-⊆. Substrate: the `picard-lefschetz` contour-integration repo
(homotopy-invariant contour integrals of holomorphic forms on `ℂⁿ` + closedness).

## Prerequisites / risks

1. **`K_X` → `Field`.** Currently `CommGroup` (multiplicative `K_X^×`). Addition of
   meromorphic reps is pointwise (still meromorphic; orders only rise on cancellation);
   instantiate `Add`/`Neg`/`AddCommGroup`/`Field` mod the germ-zero quotient. First task.
2. **Non-constant meromorphic function exists** (places separate points). Explicit on
   ℙ¹/elliptic; for general `X`, classical — may need a (true) existence axiom, or
   bootstrap from RR. Design carefully to avoid circularity.
3. **Residues on a manifold.** Local Laurent residue via charts; the global `∑=0` is
   the deep pin (picard-lefschetz substrate).

## Acceptance
Anchor compiles with `sorry`s; `SheafCohomologyFaithful` becomes *stateable against
the new defs*; the 6 `LineBundle.lean` axioms re-point to defs (axiom count drops by
3 immediately — the `H1` cluster — once `H1.lean` lands). Tracking: Discussion (this
file's companion).
