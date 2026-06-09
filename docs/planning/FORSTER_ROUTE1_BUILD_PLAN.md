# Forster Route-1 build plan — the real-cohomology roof

*Draft 2026-06-08. Implementation roadmap for the pivot decided in
[`FORSTER_ROUTE1_REPLAN.md`](FORSTER_ROUTE1_REPLAN.md) (strategic rationale +
Gemini deep-think vetting there). Keystone B (Dolbeault/harmonic), per Gemini:
go straight to the analytic cohomology; the adelic model is off the period path.
Mathlib-feasibility specifics (Phase 0/1) to be firmed by the running Codex
audit. This is a multi-month program — sequence and gates matter more than dates.*

## Goal & payoff

Build one real (analytic) cohomology and run Forster §§16–21 over it, retiring
**~9 axioms** as theorems and replacing the Route-2 plans (4g-gon topology +
independent Hodge-norm + polygon-Stokes, two of which Mathlib lacks):

| Axiom | Retired by | Forster |
|-------|-----------|---------|
| `AX_RiemannRoch` | SES LES + §14 finiteness | §16 |
| `AX_SerreDuality` | residue pairing | §17 |
| `AX_H1FreeRank2g` | `H¹(X,ℂ)≅ℂ^{2g}` + UCT | §21.5 |
| `AX_AnalyticCycleBasis` | unimodular alternating ℤ-form ⇒ symplectic basis | §21 |
| `AX_PeriodLattice` | periods of `g` forms over `2g` cycles, indep. via Hodge | §21.3 |
| `AX_RiemannBilinear` | `∫ω∧ω=0` (type) + `i∫ω∧ω̄>0` (Hodge positivity) | §19 |
| `intersectionForm` (+ `_alternating`, `_perfect`) | `∫_X α∧β`; alternating trivial; **perfect-over-ℤ = the one manual gap** | §21 |
| (`AX_AbelTheorem`) | Phase 5, enabled by RR/Serre theorems | §20 |

## Current assets (on `main` after #120/#122)

- `riemannRochSpace` (real `L(D)`) + `riemannRochSpace_finiteDimensional` (#116) — **§14 L(D) side ✓**.
- `MeromorphicFunctionField`/`divisor`/`deg`/`deg_divisor_eq_zero` (#120); `toP1` + fiber/multiplicity machinery.
- `HolomorphicOneForm` (`Ω¹`), `jacobianBasis`, `Jacobian = ℂ^g/Λ` (Λ axiomatic for now).
- `adeleH1` (Weil repartitions) — algebraic H¹; **off the period path** (keep as independent RR/Serre cross-check only).
- Abel ⊇ chunk-1 (fiber divisor) — in progress on this branch.

## Dependency DAG (Forster Route 1)

```
§13 Dolbeault lemma (∂̄u=f local)
        │
§14 dim H¹(X,O)<∞   [L(D) side ✓ #116; H¹ side = same Montel/Fréchet method]
        │
   ┌────┴─────┐
§16 RR      §17 Serre  ──→ §17.10 dim H⁰(Ω¹)=g  [≈ h0_canonical ✓ #113]
   │            │(residue ∑res=0)
   └────┬───────┘
§19 Hodge ⋆ + harmonic decomposition  ──→  dim Harm¹=2g, H¹(X,ℂ)≅Harm¹, b₁=2g
        │
§20 Abel (⊇ Liouville in progress; ⊆ now enabled)   §21 period lattice + intersection form
                                                          │(unimodularity = danger zone)
                                                     Jac(X)=ℂ^g/Λ, AX_* discharged
```

Three recurring analytic nuts: **(N1) Dolbeault solvability** (§13), **(N2) the
residue sum `∑res=0`** (§17/§20/§21 — Forster's *cheap surface-Stokes*, boundary =
finite circles, **not** polygon-Stokes), **(N3) integral unimodularity** of the
intersection form (Gemini's danger zone; Mathlib weak here).

---

## Phase 0 — De-risk probes (GATE; ~1–2 wk). Do these BEFORE committing weeks.

The pivot is a net win only if Route 1 retires 9 axioms while introducing at most
a few *cleaner, lower-level* ones. Phase 0 determines build-vs-axiomatize for each
nut and sets the honest net-axiom math.

- **P0.1 — Sheaf-cohomology LES (the keystone probe).** Can we, on a complex
  1-manifold, state `0 → ℂ → O → Ω¹ → 0` and extract the cohomology LES
  `H⁰(Ω¹) → H¹(ℂ) → H¹(O) → H¹(Ω¹)`? Determine the path: Mathlib abelian-category
  derived functors / `Mathlib.Algebra.Homology` LES vs. a hand-rolled Čech H¹ over
  a good cover. *(← the running Codex audit answers this; it is the single most
  decisive feasibility question.)*
- **P0.2 — Dolbeault lemma (N1).** Is local `∂̄u=f` solvability in Mathlib
  (`Mathlib.Analysis.Complex`), buildable in days (Cauchy-transform / `1/(πz)`
  convolution), or a real gap?
- **P0.3 — Residue surface-Stokes (N2).** Forster §10.20 divergence on
  `X ∖ ⋃Dₑ(pᵢ)`: reuse Mathlib's `DivergenceTheorem`/`circleIntegral` + the
  sibling `picard-lefschetz` contour machinery? Or one clean low-level axiom
  `∑_p res_p ω = 0` to start.
- **P0.4 — Integral unimodularity (N3).** Cheapest route to the intersection form
  being unimodular over ℤ: a Mathlib Poincaré-duality fact, or accept it as one
  clean low-level axiom (`geometric intersection pairing on H₁ is unimodular` — a
  standard fact), with the symplectic-basis algebra (`alternating unimodular ℤ ⇒
  symplectic`) proved on top (pure linear algebra — likely already feasible).

**Gate decision.** Tabulate: 9 retired vs. `k` introduced (each of N1–N3 either
*proved* or relocated to *one* clean low-level axiom). If `k ≤ 3` clean
standard-analysis axioms and P0.1 has a viable path → **proceed**. Else hold the
period cluster axiomatized and reassess (or do only the parts that net out).
Each retained nut-axiom gets the full vetting protocol (citation, satisfiability,
Gemini review) and its own discharge tracker.

### Phase-0 findings — hands-on Mathlib recon (2026-06-08, our pin)

Cross-checks the running Codex audit; all from `.lake/packages/mathlib`.

- **P0.1 sheaf-cohomology LES — GREEN (compile-confirmed).** `lake env lean`
  type-checks: `CategoryTheory.Sheaf.H : Sheaf J AddCommGrpCat → ℕ → Type`
  (sheaf cohomology, needs `[HasSheafify] [HasExt]`), `Sheaf.H.equiv₀ : F.H 0 ≃+
  Γ(F)` (H⁰ = global sections), and `ShortComplex.ShortExact.δ : X₃.homology i ⟶
  X₁.homology j` + `homology_exact₁/₂/₃` (the homological LES). So the keystone's
  homological algebra is **assemble existing API**, not build-from-scratch — the
  single biggest flagged risk is substantially de-risked. *Open architecture
  choice (audit to detail): model `X` via an open-cover Grothendieck site with
  `O` an `AddCommGrp`-valued abelian sheaf so `Sheaf.H` applies; derive the
  sheaf-cohomology LES from a sheaf SES through `HasExt`/derived functors.*
- **P0.2 Dolbeault (N1) — GAP.** No `∂̄`/Dolbeault/inhomogeneous-CR in
  `Analysis.Complex`. Build (Cauchy-transform) or one clean low-level axiom.
- **P0.3 residue surface-Stokes (N2) — PARTIAL/positive.** `MeasureTheory.Integral.
  DivergenceTheorem` + `BoxIntegral.DivergenceTheorem` + `MeasureTheory.Integral.
  CircleIntegral` present — the pieces for the punctured-surface residue argument
  exist; assembly needed.
- **P0.4 symplectic basis (N3-algebra) — GAP.** `LinearAlgebra.SymplecticGroup`
  has the standard matrix `J` + symplectic group, but **no** "alternating
  nondegenerate form ⇒ symplectic/Darboux basis" lemma (the `Darboux.lean` in
  Mathlib is the calculus MVT, unrelated). Pure-linear-algebra build; the
  unimodular-over-ℤ refinement is the danger-zone half.

**Provisional gate read (pre-audit): GO.** — *revised below; the audit overturns
this.*

### Phase-0 GATE DECISION — post Codex Mathlib audit (2026-06-08): **PARK for the near term**

The Codex audit sharpens P0.1 and overturns the "cheaper near-term win" framing.
The LES *substrate* is real (`Ext.covariantSequence`, Mayer–Vietoris `sequence_exact`,
`cechComplexFunctor`) — but the **inputs Forster §§13–21 consume are mostly ABSENT
from Mathlib**, each months-scale to build to upstream grade:

| Item | Audit verdict | Gap |
|---|---|---|
| Holomorphic sheaves `O`, `Ω¹` | **TODO in Mathlib** (`Geometry/Manifold/Complex.lean`) — only *smooth* sheaves exist (`smoothSheafCommRing`) | build `O`/`Ω¹` as sheaves: **weeks** |
| Dolbeault `∂̄`-Poincaré | **ABSENT** | local solvability + Dolbeault thm: **months** |
| Manifold differential forms + integration | **TODO** (`DifferentialForm.Basic`, `PartitionOfUnity`) — flat-space `extDeriv` only | manifold forms/∫: **months** |
| Hodge ⋆ / harmonic forms / `∫ω∧⋆ω̄` | **ABSENT** | depends on forms+Dolbeault: **months** |
| Integral Poincaré duality / unimodularity | **PARTIAL** — singular homology exists, but no cup product / fundamental class / `unimodular ℤ-form ⇒ symplectic basis` | **months** (topology); ℤ-symplectic algebra weeks *after* unimodularity |
| Residue surface-Stokes | **PARTIAL** — flat box-divergence + circle/Cauchy strong; global compact-surface Stokes blocked on manifold forms | weeks–months |

**Bottom line (audit, verbatim sense):** *"Route 1 is not buildable on current
Mathlib in a weeks-scale discharge."* And — critically — **axiomatizing the gaps
mostly RELOCATES the debt**: a `DolbeaultPoincare` / `surfaceStokes_residue` /
`IntegralPoincareDuality_unimodular` / `HodgeDecomposition` axiom set "is not
materially safer than keeping the period cluster axiomatized" unless we commit to
retiring them through *upstream-grade infrastructure*.

**Reconciling the two vettings.** Gemini (math level) is right that Route 1 is the
*cleaner* route and §19's positivity is elementary; Codex (Mathlib level) is right
that the **infrastructure those steps stand on — manifold forms, holomorphic
sheaves, Dolbeault, Hodge ⋆, integral PD — does not yet exist in Mathlib**. Both
routes are gated on building that infrastructure; Route 1 needs *less* of it than
Route 2 (no 4g-gon, no polygon-Stokes), but it is a **months-to-years upstream
build, not a near-term axiom collapse.**

**Decision: do NOT pour weeks into Route 1 as a near-term discharge.** Options:
1. **Keep the period cluster axiomatized** (status quo); pursue independent feasible
   wins instead — Abel ⊇ (in progress, needs none of this infra), the pure-ℤ
   symplectic-basis algebra (weeks, once we accept unimodularity as one clean axiom),
   the adelic RR/Serre track (concrete, residue-pairing-gated).
2. **Commit to Route 1 as a long-horizon infrastructure program** — build (and ideally
   upstream) manifold differential forms → holomorphic sheaves → Dolbeault → Hodge.
   Months-to-years; the payoff is real (retires ~9 + becomes Mathlib infra) but it is
   not a quick collapse.

**Cheapest decisive next de-risk (if pursuing):** try to *state* (no proofs)
`0 → ℂ → O → Ω¹ → 0` + the connecting `H⁰(Ω¹) → H¹(ℂ)` on a complex manifold. The
LES extraction works (`Ext.covariantSequence`); the probe will likely fail at
*stating `O`/`Ω¹`* — confirming the real gap is the holomorphic-sheaf layer.

---

## Phase 1 — Real cohomology foundation (~3–5 wk). The keystone.

1. **Define H¹(X,O) concretely** (replacing opaque `AX_H1`): Dolbeault
   `H^{0,1} = ℰ^{0,1}/∂̄ℰ^{0,0}`, or Čech over a good cover — chosen per P0.1.
2. **§13 Dolbeault lemma** (per P0.2: prove or one clean axiom).
3. **§14 finiteness `dim H¹(X,O)<∞`** — the hard analytic step; attempt to transfer
   the #116 `L(D)`-finiteness Montel/normal-families argument to the H¹ side.
4. **Bridge**: make the existing `H1`/`riemannRochSpace` API rest on this real
   object (so #113/#120/#122's proved consequences carry over unchanged).

*Output:* a real, finite-dimensional `H¹(X, O(D))`; `AX_H1` stub retired or bridged.

## Phase 2 — Riemann–Roch + Serre as theorems (§16–17) (~3–4 wk).

1. **§16 RR**: the skyscraper SES `0→O(D)→O(D+P)→ℂ_P→0` LES + finiteness ⇒
   `χ(D+P)=χ(D)+1`, induct ⇒ `h⁰(D)−h¹(D)=deg D+1−g`. **Discharges `AX_RiemannRoch`.**
2. **§17 Serre duality** via the residue pairing `H¹(O(D)) × H⁰(Ω¹(−D)) → ℂ`
   (uses N2). ⇒ `dim H⁰(Ω¹)=g` (≈ `h0_canonical` ✓). **Discharges `AX_SerreDuality`.**
3. Re-point `riemannRoch`, `h1_eq_h0_canonical_sub`, Serre vanishing from
   axiom-resting to theorem-resting; `#print axioms` should lose `AX_RiemannRoch`/
   `AX_SerreDuality` on those.

## Phase 3 — Harmonic forms + de Rham–Hodge (§19) (~3–4 wk).

1. **Hodge ⋆** on 1-forms; **positivity** `⟨ω,ω⟩=∫ω∧⋆ω̄ = ∫|f|²dx dy ≥ 0` (Gemini:
   elementary local algebra — the cheap part).
2. **Harmonic decomposition** `ℰ¹ = dℰ⁰ ⊕ ⋆dℰ⁰ ⊕ Harm¹`; `dim Harm¹ = 2g` (from
   §17.10 + Dolbeault). *(Existence of harmonic reps = the sheaf-LES homological
   algebra — the real Lean cost flagged by Gemini.)*
3. **de Rham–Hodge** `H¹_dR(X,ℂ) ≅ Harm¹`, `b₁ = 2g`.

## Phase 4 — Period lattice + intersection form (§21) (~4–6 wk).

1. **`H₁(X;ℤ) ≅ ℤ^{2g}`** via UCT from `H¹(X,ℂ)≅ℂ^{2g}` + torsion-free.
   **Discharges `AX_H1FreeRank2g`.**
2. **Period map / period integrals** `∫_γ ω`; rank-`g` period matrix (from §17.10).
3. **Riemann bilinear relations**: `∫ω∧ω=0` (type (2,0)=0 on a curve — trivial);
   `i∫ω∧ω̄>0` (Hodge positivity, Phase 3). **Discharges `AX_RiemannBilinear`.**
4. **Intersection form** `∫_X α∧β`: alternating trivial; **perfect-over-ℤ via N3
   (unimodularity, the danger zone)**. **Discharges `intersectionForm` + laws.**
5. **Symplectic basis** from a unimodular alternating ℤ-form (pure linear algebra).
   **Discharges `AX_AnalyticCycleBasis`.**
6. **Period lattice full rank** (`Γ∩W=0` via Abel + N2; `Γ` spans via §19.8 nondeg).
   **Discharges `AX_PeriodLattice`.**

## Phase 5 — Abel (§20) (~3–6 wk).

1. **Abel ⊇** (Liouville / Jacobi-constant-on-ℙ¹) — *already in progress* on
   `abel-supset`; reuses `toP1`/fiber/Liouville. Independent of Phases 1–4.
2. **Abel ⊆** (Jacobi inversion) — now **enabled** by the RR/Serre *theorems*
   (third-kind differentials). **Discharges `AX_AbelTheorem`** (full).

---

## Honest debt accounting

Route 1 retires ~9 axioms; it may introduce up to **3 cleaner low-level axioms**
if N1–N3 aren't fully proved in their phase: a Dolbeault-solvability fact, the
residue sum `∑res=0` (cheap surface-Stokes), and integral unimodularity. All three
are *standard, satisfiable, narrowly-scoped analysis/topology facts* — strictly
lower in the dependency order than the 9 they retire, and each independently
discharge-planned. Net consolidation is large even in the worst case; this is a
genuine reduction, not relocation, provided the Phase-0 gate holds.

## Decision gates / off-ramps

- **After Phase 0:** the go/no-go. If P0.1 (sheaf LES) has no viable Mathlib path,
  Route 1 stalls at the cohomology foundation — stay axiomatized.
- **After Phase 2:** RR/Serre discharged is a complete, shippable win (2–3 axioms)
  even if Phases 3–4 are deferred — a natural stopping point.
- **Phase 5 ⊇** ships independently (no dependency on 1–4); already underway.

## Sequencing recommendation

Phase 0 now (cheap, decisive) → Phase 1 (keystone) → Phase 2 (RR/Serre, shippable)
→ Phases 3–4 (the period collapse) → Phase 5 ⊆. Keep Abel ⊇ (Phase 5.1) running in
parallel — it's independent and de-risks the developing-value/period plumbing the
later phases reuse.

*Vetting trail: Gemini deep-think 2026-06-08 (strategic, in REPLAN doc); Codex
Mathlib-feasibility audit 2026-06-08 (Phase 0/1 specifics — fold in on completion).
Re-vet each retained nut-axiom before relying on it.*
