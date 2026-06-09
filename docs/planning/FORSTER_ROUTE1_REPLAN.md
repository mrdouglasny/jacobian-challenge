# Forster Route-1 re-plan — collapse the period cluster onto a real-cohomology build

*Draft 2026-06-08. Strategic route-selection doc (not an implementation plan).
Prompted by: "the RR/Serre anchor layer is now sorry-free — can't we use it to
discharge the period cluster?" Answer below, with the precise dependency and the
re-plan it implies. To be vetted by Gemini deep-think + Codex before any build.*

## Thesis

The current period-cluster discharge plans (`docs/planning/AX_PeriodLattice.md`,
`AX_RiemannBilinear.md`, `AX_AnalyticCycleBasis.md`) follow **Route 2**
(Griffiths–Harris): three independent hard builds — 4g-gon fundamental-polygon
topology, an independent Hodge-norm, and polygon-Stokes — two of which Mathlib
lacks (~year+, per `refs/JACOBIAN_ROUTE_COMPARISON.md`). **Route 1 (Forster
§§12–21)** instead derives the *entire* period cluster from one analytic input
(the §14 finiteness theorem) plus homological algebra and an **elementary** local
Hodge computation, with `H₁ ≅ ℤ^{2g}` *derived* (§21.5), no 4g-gon. This doc
proposes re-planning the period axioms onto Route 1 and asks the vetting models
to falsify the cost claim.

## Why "anchor layer sorry-free" did NOT already do this

What we closed (PR #120/#122) are the RR/Serre *consequences* (`h0_of_deg_gt`,
`h1_eq_zero_of_deg_gt`, `riemannRoch_consistent_with_AX`,
`h0_point_eq_one_of_genus_pos`), proved **from** `AX_RiemannRoch` +
`AX_SerreDuality` over an **opaque `AX_H1` type**. The period cluster (§19–21)
consumes the *real* cohomology — period integrals `∫_γ ω` over actual cycles,
harmonic forms, the ⋆-operator. An opaque `H1` carries none of that. **The anchor
axiomatized away exactly the object the period collapse needs.** So the leverage
is not "close the API sorrys" (done) — it is **build a real cohomology with the
analytic structure §19–21 require.**

## The two candidate keystones (this is the crux to vet)

| | **A — Adelic / Weil repartitions** (`Cohomology/Repartitions.lean`, `adeleH1`) | **B — Dolbeault / harmonic forms** (Forster §13, §19) |
|---|---|---|
| What it is | purely **algebraic** H¹ = `𝔸_X(D) / (𝔸_X(D)+K_X)` | **analytic** H¹ via ∂̄, ⋆-operator, harmonic decomposition |
| Gives RR/Serre? | **yes** (§16–17 algebraically) | **yes** (§16–17) |
| Gives period lattice / cycle basis / bilinear? | **NO** — no period integrals, no harmonic structure | **yes** (§19 harmonic ⇒ §21 period lattice; `H₁≅ℤ^{2g}` byproduct §21.5) |
| Axioms retired | `AX_RiemannRoch`, `AX_SerreDuality`, `AX_H1` stub (~2–4) | those **+ the 7 period axioms** (~9) |
| Single hard prereq | residue pairing / `∑res=0` (`serre_anchor`) | Dolbeault lemma §13 + `∑res=0` + harmonic decomp §19 |
| Status | `adeleH1` scaffolded; `adeleH1_finiteDim` + `serre_anchor` are sorrys | not started |

**Key point for vetting:** the period collapse the README advertises requires
**Keystone B**, not A. The adelic route (A) retires RR/Serre only. They share the
residue theorem; B additionally needs the Dolbeault lemma and the harmonic
decomposition.

## The Route-1 dependency chain (Forster), mapped to our axioms

```
§14  dim H¹(X,O) < ∞          ← the ONE hard analytic step
        ├─ L(D) side  ✓ DONE (#116, riemannRochSpace_finiteDimensional, elementary)
        └─ H¹ side    = adeleH1_finiteDim (sorry; #116-style method, reachable)
§16  Riemann–Roch            ⇒ discharges AX_RiemannRoch
§17  Serre duality           ⇒ discharges AX_SerreDuality   [needs ∑res=0]
        ⇒ §17.10  dim H⁰(Ω¹) = g   ✓ already have h0_canonical (#113)
§19  Harmonic forms (Dolbeault):
        • ⋆ + positivity ⟨ω,ω⟩=∫ω∧⋆ω≥0  — Forster claims ELEMENTARY local comp (§19.5)
        • Hodge decomp, dim Harm¹ = 2g   (from §17.10 + Dolbeault)
        • deRham–Hodge H¹(X,ℂ)≅Harm¹, b₁=2g
§20  Abel's theorem          [needs ∑res=0]   (⊇ half: our Liouville route, in progress)
§21  Period lattice:
        (a) rank-g period matrix  ⇐ §17.10 (have)
        (b) Γ∩W=0                 ⇐ Abel + ∑res=0
        (c) Γ spans               ⇐ §19.8 harmonic-period nondegeneracy
        ⇒ discharges AX_PeriodLattice, AX_RiemannBilinear, AX_AnalyticCycleBasis,
          AX_IntersectionForm(+alternating/perfect), AX_H1FreeRank2g
```

## The single recurring blocker: the residue theorem `∑_p res_p ω = 0`

On the path at §17 (Serre pairing), §20 (Abel), §21b. **Forster's is the easy
surface-Stokes** (§10.20–21): the divergence theorem for a 1-form compactly
supported away from finitely many points, giving `∫∫ d(fσ) = ±2πi·Res` — **NOT**
the 4g-gon polygon-Stokes the Route-2 plans assume. Open question for vetting:
is this tractable in Mathlib v4.30 (manifold divergence theorem with point
punctures), or is it itself a multi-month build?

## What to decide / vet

1. **Cost falsification.** Is Forster's claim that §19 (harmonic decomposition +
   Hodge positivity) is *elementary local algebra* — not the Route-2 independent
   Hodge-norm build — actually right at the formalization level? Or does it hide
   a real PDE/functional-analysis cost (Dolbeault lemma §13 = global ∂̄-solvability
   on a compact surface, via Montel/Fréchet)?
2. **Dolbeault availability.** Is the §13 Dolbeault lemma (local inhomogeneous
   Cauchy–Riemann `∂̄u = f`) in Mathlib, or buildable in days, or a real gap?
3. **Residue theorem tractability.** Forster §10 surface-Stokes vs Mathlib's
   current manifold-integration API — bounded build or blocker? (cross-ref the
   `picard-lefschetz` repo's flat-ℂⁿ contour machinery as a partial substitute).
4. **Keystone choice.** Given (1)–(3): is the right move (i) Keystone B (full
   Route-1, ~9 axioms, but needs Dolbeault+harmonic) or (ii) Keystone A first
   (adelic, RR/Serre only, ~2–4 axioms, smaller), then revisit the period cluster?
5. **Net axiom math.** Honest count of axioms retired vs. *added* (does Route 1
   need new low-level axioms, e.g. a Dolbeault-solvability or surface-Stokes
   axiom, that just relocate the debt?).

## Vetting — Gemini deep-think (2026-06-08)

Rigorous skeptical pass; verdicts:

1. **Adelic (A) cannot yield periods — confirmed.** The Riemann bilinear relations
   need Hodge positivity `(i/2)∫_X ω∧ω̄ > 0`; conjugation `ω̄` and integration over
   the topological `X` *do not exist* in the algebraic adelic model. Extracting
   periods from A would require algebraic de Rham + Grothendieck's theorem + GAGA
   — *vastly* harder than just doing Dolbeault.
2. **§19 analysis is cheap; the homological algebra is the cost.** Hodge ⋆-positivity
   is literally `∫|f|²dx dy` (elementary). But the *existence* of the harmonic
   decomposition needs the ∂̄-Poincaré lemma, the Dolbeault iso `H¹_Dolb ≅ Ȟ¹(X,O)`,
   and the LES of `0→ℂ→O→Ω¹→0`. **In Lean the real work is sheaf-cohomology long
   exact sequences**, notoriously tedious if Mathlib's API isn't a fit.
3. **Route 1 avoids the 4g-gon — confirmed — but hides one topological cost.**
   `H¹(X,ℂ)≅ℂ^{2g}` (Hodge) + universal coefficients ⇒ `H₁≅ℤ^{2g}`. **Danger zone:**
   the *symplectic basis* (`AX_AnalyticCycleBasis`) needs the intersection form to be
   **unimodular over ℤ** = integral Poincaré duality, which Mathlib handles poorly.
   Once unimodular, "alternating unimodular ℤ-form ⇒ symplectic basis" is pure
   linear algebra.
4. **Residue Stokes — Forster's is vastly cheaper — confirmed.** Integrating over
   `X ∖ ⋃ Dₑ(pᵢ)` has boundary = a finite disjoint union of circles; need only
   Stokes on a disk/annulus + sum. No CW-quotient orientation tracking. Mathlib is
   much closer to this than to polygon quotients.
5. **Recommendation: ABANDON Keystone A; go straight to B (Dolbeault/harmonic).**
   Adelic-first costs months to retire 2 axioms (RR, SD) and buys *zero* toward the
   period cluster — you'd restart with Dolbeault anyway.

**Per-axiom discharge under Keystone B (Gemini):** RR + Serre (§16–17); `H₁` rank 2g
(Hodge + UCT); period lattice (integrate the `g` forms over `2g` cycles, indep. from
Hodge); intersection alternating (trivial `α∧β=−β∧α`), **perfect-over-ℤ = the one
manual gap (unimodularity)**; symplectic basis (linear algebra once unimodular);
Riemann bilinear (`∫ω∧ω=0` trivial by type; `i∫ω∧ω̄>0` = the elementary local comp).

**Immediate probe (Gemini):** check Mathlib's sheaf-cohomology + Dolbeault state —
specifically, can one state `0→ℂ→O→Ω¹→0` and extract its LES in cohomology. If yes,
Route 1 is open. (← this is the Codex feasibility audit now running.)

## Revised recommendation (post-Gemini, pending Codex Mathlib audit)

**Go straight to Keystone B (Dolbeault/harmonic) — do NOT detour through the adelic
model for the period goal.** The single roof is: real Dolbeault cohomology + §14
finiteness (L(D) side ✓ #116; H¹ side via the same method) → §16–17 (RR/Serre as
theorems) → §19 harmonic forms → §21 period lattice, retiring ~9 axioms. Two gates
to de-risk *before* committing weeks: (i) **Mathlib sheaf-cohomology LES usability**
(the Codex audit), and (ii) **integral unimodularity** of the intersection form (the
one piece Route 1 doesn't hand you for free). The residue theorem is the shared
analytic nut but is Forster's cheap surface-Stokes, not polygon-Stokes.

*Note: the adelic anchor (`RiemannRochAnchor`) remains useful as an independent
faithful RR/Serre cross-check and could still discharge RR/Serre on its own track —
it is just not on the period-cluster critical path.*

*Sources: Forster GTM 81 §§9–21; `refs/JACOBIAN_ROUTE_COMPARISON.md`;
`docs/planning/RR_SERRE_ADELIC_ANCHOR.md`; `docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`.*
