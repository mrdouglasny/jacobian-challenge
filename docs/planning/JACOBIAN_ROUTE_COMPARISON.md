# Two routes to the Jacobian — prerequisite comparison

**Question.** To make `Jac(X) = ℂ^g/Λ` well-defined and discharge the core
period axioms (`AX_AnalyticCycleBasis`, `AX_RiemannBilinear`, `AX_PeriodLattice`),
plus Abel + Jacobi inversion — which classical route is cheaper to formalize, and
does it need Riemann–Roch / Serre duality?

**Answer (this doc).** There are two standard routes. They reach the same
`Jac(X)` but put the depth in completely different places. The project's current
`AX_*` discharge plans assume **Route 2 (Hodge / period-matrix)**, which needs
three pieces of infrastructure that don't exist in Mathlib. **Route 1 (Forster,
cohomological)** concentrates all the hard analysis into a single finiteness
theorem — which the project has *already discharged* — and gets the rest by
homological algebra, **without the 4g-gon topology or polygon-Stokes**.

Sources: Forster, *Lectures on Riemann Surfaces* (GTM 81) §§9–21 (in
`refs/forster-riemann-surfaces/`); Griffiths–Harris Ch. 2; the project's
`docs/planning/AX_RiemannBilinear.md`, `AX_AnalyticCycleBasis.md`,
`AX_PeriodLattice.md`.

---

## Shared base (both routes need)

- Riemann surface = complex 1-manifold; holo/mero functions; sheaves.
- Differential forms `ℰ^(1)` with the `∂`/`∂̄` (`d'`/`d''`) split.
- **Easy surface-Stokes:** `∫∫_X dσ = 0` for compactly-supported `σ`, and the
  residue identities `∫∫ d(fσ) = ±2πi·Res`. (Forster §10.20–10.21.) This is the
  divergence theorem on a manifold with the integrand compactly supported away
  from finitely many points — **not** integration over a polygon with boundary.

---

## Route 1 — Forster (cohomological): ONE hard input, then algebra

```
§13 Dolbeault (local ∂̄-solvability = inhomogeneous Cauchy–Riemann)
 └─ §14 ★ FINITENESS:  dim H¹(X, O) < ∞      ← the ONLY hard analytic step
         (Dolbeault + Schwarz' lemma + Montel/normal-families compactness)
     └─ §16 Riemann–Roch
         └─ §17 Serre duality   ⇒   §17.10:  dim H⁰(X, Ω¹) = g
             └─ §19 Hodge decomposition — a COROLLARY of Serre + Dolbeault,
                     not an independent build (⋆-positivity is elementary)
                 └─ §20 Abel  →  §21 period lattice full-rank in ℂ^g;
                         H₁(X) ≅ ℤ^{2g} falls out as a BYPRODUCT (§21.5)
                     └─ §21.6  Jac(X) = ℂ^g / Per(ω₁,…,ω_g)
```

Hard prerequisites: **exactly one** — the §14 finiteness theorem. Everything
downstream (RR, Serre, the Hodge decomposition, Abel, the period lattice, *and*
`H₁ ≅ ℤ^{2g}`) is homological algebra + elementary form manipulation + the easy
surface-Stokes. The 4g-gon / triangulation is **never used** — `H₁ ≅ ℤ^{2g}` is
*derived* (§21.5), not assumed.

## Route 2 — Griffiths–Harris / current discharge plans (Hodge / period-matrix)

```
① 4g-gon topology (Radó triangulation + polygon classification)
     ⇒ symplectic homology basis  (= AX_AnalyticCycleBasis)     [plan: ~1+ year, ~5000 LOC]
② multi-chart homotopy-invariant path integration  (loopIntegralToH1)
③ Hodge inner product ⟨ω,η⟩=(i/2)∫_X ω∧η̄ + positivity  (built independently)
④ POLYGON-Stokes: integration-by-parts on the 4g-gon  (NOT in Mathlib)
   ③+④ ⇒ Riemann bilinear relations  (= AX_RiemannBilinear)    [plan: ~6+ months]
   ①+bilinear ⇒ period lattice full-rank  (= AX_PeriodLattice)
      ⇒ Jac(X) = ℂ^g/Λ
```

Hard prerequisites: **three** — the 4g-gon topology, the Hodge-norm positivity,
and polygon-Stokes. Two of the three are not in Mathlib.

---

## Verdict

| | Route 1 — Forster | Route 2 — GH / current plans |
|---|---|---|
| Hard analytic inputs | **1** (H¹ finiteness, §14) | **3** (4g-gon, Hodge-norm, polygon-Stokes) |
| Needs 4g-gon / triangulation? | **No** (`H₁≅ℤ^{2g}` derived) | **Yes** (~1 yr) |
| Needs polygon-Stokes? | No (only easy surface-Stokes) | **Yes** (not in Mathlib) |
| Independent Hodge build? | No (Hodge = corollary of Serre+Dolbeault) | **Yes** |
| RR/Serre | **foundational** (spine of the route) | sidestepped |
| `genus = dim Ω¹` | from Serre §17.10 | from Hodge decomposition |
| Shape | one deep theorem + homological algebra | three parallel infra projects |

Both reach the same `Jac(X)`; they differ in where the depth sits. **Route 1
replaces three infrastructure builds with a single finiteness theorem** — and
that theorem is the one piece the project has already discharged (see
[`FORSTER_ROUTE_PLAN.md`](FORSTER_ROUTE_PLAN.md)). Recommendation: re-base the
core period-axiom discharges on Route 1 before investing further in the
polygon-Stokes / 4g-gon infrastructure that Route 2 requires.
