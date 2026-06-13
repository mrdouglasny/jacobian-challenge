# Topology-finish route — the four named residuals under K-LITE leverage

Date: 2026-06-12. Lane: TFIN (`feat/topology-finish`). Companion to
`H1_COMPOSITE_ROUTE.md` (#230, the composite consumer), `TRANK_SCOPING.md`
(Free + T-RANK analysis), `GOODCOVER_BLOCKER.md` (GC-1, T-FG's gate), and the
K-LITE lane (TR-DISC: `DiscreteTopology (loopPeriodLattice x₀ b)`).

This doc scopes the LAST four topology residuals before the general
`AX_PeriodCycleBasis` flip on the H₁ side, with the new leverage that K-LITE
makes `finrank ℤ Λ = 2g` available from discreteness alone:

* **T-GEN** — `AnalyticLoopsGenerateH1 x₀`: `span ℤ (range loopToHomology) = ⊤`.
* **T-FG** — `Module.Finite ℤ (H1 X x₀)` (from `Group.FG π₁`).
* **Free** — `Module.Free ℤ (H1 X x₀)` (H₁ torsion-free).
* **T-RANK≤** — `Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X`.

## 0. Headline finding — the residuals collapse to {T-GEN, KER-0}

The composite (`H1Composite.lean`, #230) already proves, **conditional on**
`[DiscreteTopology (loopPeriodLattice x₀ b)]` (K-LITE's output) and T-GEN:

> `H1 ≃ₗ[ℤ] (ker φ × Λ)`  (`nonempty_ker_prod_lattice_equiv_h1`),

with `Λ = loopPeriodLattice` **free, finitely generated, `finrank ℤ Λ = 2g`
exactly** (K-LITE / ZLattice). The splitting itself uses **no** module
hypothesis on `H1` (Λ is projective; the surjection `φ̄ : H1 ↠ Λ` from T-GEN
splits). So with the K-LITE leverage, all H₁-module structure is governed by
the single short exact sequence

```
0 → ker φ → H1 → Λ → 0      (split; Λ free f.g. rank 2g)
```

**Consequence (the collapse).** The three H₁-module residuals
{T-FG, Free, T-RANK≤} feed `h1PeriodInjective_of_finrank_le` for one purpose
only: to prove **KER-0** := `∀ v, φ v = 0 → v = 0` (`ker φ = 0`). And KER-0 is
**equivalent** (given the split SES) to "`H1 ≃ Λ`", which *outputs* Free +
Finite + `finrank = 2g` for free. So the honest minimal residual set on the
H₁ side is

> **{T-GEN, KER-0}**,

exactly the hypotheses of `exists_h1LoopBasis_of_periodInjective`. The
`_of_topology` triple {T-FG, Free, T-RANK≤} is **one sufficient packaging** of
KER-0, not three independent obligations.

### 0.1 Is T-FG droppable from the packaging? NO — a `finrank` subtlety

It is tempting (per the brief) to drop T-FG because "Λ carries the rank". The
`finrank` bookkeeping says otherwise, and this is the load-bearing subtlety:

`Module.finrank ℤ M = Cardinal.toNat (Module.rank ℤ M)`. `toNat` sends
**infinite** cardinals to `0`. With the split SES,
`rank H1 = rank (ker φ) + 2g`. If `rank (ker φ)` is **infinite**, then
`rank H1` is infinite, so `finrank ℤ H1 = 0 ≤ 2g` — the T-RANK≤ bound is
**satisfied while `ker φ ≠ 0`**. The bound only forces `ker φ = 0` once
`rank H1` (hence `rank (ker φ)`) is known **finite** — which is exactly what
**T-FG** (`Module.Finite ℤ H1`) supplies. So in the `_of_topology` route:

* **T-FG is genuinely used** (makes `finrank` faithful to rank; the proof's
  `Module.finrank_eq_card_basis` over a chosen `chooseBasis` needs Free+Finite).
* **T-RANK≤ is genuinely used** (the `≤ 2g` that `omega`-forces `n = 0`).
* **Free is genuinely used** (PID basis + `basisOfPid` of the submodule
  `ker φ`; also it *is* the honest torsion-freeness carried into KER-0).

None of the three is vacuous or redundant *within that packaging*; the
collapse is that the packaging as a whole is **equivalent to the single
KER-0**, not that any one of the three drops. (Contrast the *image*-lattice
route, `PeriodDiscreteness.lean §ImageRoute` / #206, where all three H₁-module
hypotheses genuinely drop — but that route never produces the H₁ *basis*, only
the lattice basis. The H₁ fields of `AX_PeriodCycleBasis` need the H₁ basis,
so they cannot use the image route; see `H1_COMPOSITE_ROUTE.md` §2.3.)

### 0.2 What KER-0 actually is (no Hodge-avoidance on the H₁ side)

KER-0 = period-injectivity on `H1` = "a class with all developing-value
periods zero is zero". Decomposed:

* `ker φ` torsion ⟸ torsion classes always have zero periods (φ lands in the
  torsion-free `ℂ^g`); so KER-0 ⊆ "`H1` torsion-free" (= Free, modulo f.g.).
* the **rank** part — "no nonzero torsion-free class has all periods zero" —
  is the de-Rham/Hodge content (`TRANK_SCOPING.md` §2 route (a)), which the
  splitting reduces to the pure rank inequality `finrank H1 ≤ 2g` **given
  T-FG**. There is no torsion-free-avoidance here (the H₁ basis needs Free
  anyway); that dividend belongs to the lattice consumers only (#206).

So **KER-0 ⟺ T-FG + Free + T-RANK≤** under K-LITE + T-GEN — the collapse is an
*equivalence*, sharpening `H1_COMPOSITE_ROUTE.md` §2.2.

## 1. Per-residual status

| # | Residual | Status | Closest source |
|---|----------|--------|----------------|
| T-GEN | analytic loops generate H₁ | **NAMED — g=1 PROVEN (`analyticLoopsGenerateH1_elliptic`); general compact-surface gap** | §2 below |
| T-FG | `Module.Finite ℤ H1` | **RESEARCH-GRADE (GC-1)** — good-cover existence on compact X, blocked at Mathlib pin | `GOODCOVER_BLOCKER.md` |
| Free | `Module.Free ℤ H1` (torsion-free) | **RESEARCH-GRADE** — surface-classification / Hodge; folded into KER-0 | §3 below |
| T-RANK≤ | `finrank ℤ H1 ≤ 2g` | **RESEARCH-GRADE (TR-DISC route (a))** — de Rham comparison layer | `TRANK_SCOPING.md` §2 |

All four are honest topology/Hodge content; none is a definition-chase. The
K-LITE leverage **re-bundles** them (four → {T-GEN, KER-0}) but does **not**
discharge any: KER-0 still contains the de-Rham rank input.

### What this lane CAN land (independent merges)

1. **Collapse certificate** (`h1Free_finite_rank_of_periodInjective`,
   §0/§3): KER-0 (+ T-GEN + K-LITE) ⟹ Free + Finite + `finrank = 2g` for H₁,
   as *outputs*. Makes the four→two collapse a kernel-checked theorem, not just
   a doc claim. **PROVEN this lane** (see §3).
2. The route doc itself (this file).

### What this lane CANNOT land (named research-grade)

* **T-GEN on compact X**: the lasso machinery (`IsolatingLasso.lean`,
  `normalClosure_isolatingLassos_eq_top`) lives on the **punctured plane**
  `ℂ ∖ T`, not on `X`. The bridge to `π₁(X)` is the branched-cover /
  slit-sheet reduction (`CellLassoPower.lean`, `PuncturedPlanePi1.lean` are the
  start), which is incomplete — there is no theorem giving analytic generators
  of `π₁(X)` for a general compact `X`. See §2.
* **T-FG**: GC-1 (good-cover existence), blocked on Mathlib Riemannian
  geometry (no exponential map / totally-normal neighborhoods at the pin).
* **Free + T-RANK≤ = the rank half of KER-0**: TR-DISC route (a), a multi-week
  de Rham comparison sub-campaign (`TRANK_SCOPING.md` §2). No keystone bypass
  (`GOODCOVER_BLOCKER.md` GC-2: ℂ-valued pairings are blind to ℤ-rank/torsion).

## 2. T-GEN — punctured-plane done, compact-surface gap (NAMED)

The #227 lasso ladder proves, for the **punctured plane**:
`normalClosure_isolatingLassos_eq_top` — one explicit isolating circle lasso
per puncture normally generates `π₁(ℂ ∖ T, x₀)`; the lassos are concrete
piecewise-analytic loops (`t ↦ s + (z−s)·exp(2πi t)`). By abelianization,
their classes ℤ-generate `H1(ℂ ∖ T)`.

**The gap.** `X` is a *compact* Riemann surface, and T-GEN is
`span ℤ (range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)) = ⊤` —
generation of `π₁(X)` (abelianized) by analytic loops *on X*. The bridge from
`π₁(ℂ ∖ T)` to `π₁(X)` is the **branched-cover / slit-sheet** presentation:
`X` minus the branch fibre is a cover of `ℂ ∖ (branch locus)`, and lifts of
the isolating lassos stay piecewise-analytic. This bridge is **not present**:
grep over `Jacobians/Topology/` finds the lasso results stated only on
`{z : ℂ // z ∉ (T : Set ℂ)}`; `CellLassoPower.cellLasso` produces a
`FundamentalGroup X x₀` element from a *cell* `A : Set X` carrying a chart to
`ℂ`, but there is no assembled theorem that the cellLassos over a finite atlas
**generate** `π₁(X)`, nor that those generators are `loopToHomology` of
`AnalyticLoop X`s. Building that = the slit-sheet π₁-generation campaign
(`CYCLEBASIS_ALTERNATIVES.md` direction 2b) — concrete but multi-session, not
a short composition of existing results.

**Verdict: NAMED residual.** Punctured-plane normal-generation is done; the
compact-surface lift is a genuine open sub-campaign (slit-sheet π₁), not a
one-application corollary. It is NOT surface-classification-grade (the lasso
generators are explicit and analytic), but it is more than glue.

**Satisfiability (PROVEN this lane).** T-GEN is non-vacuous on a genuine
positive-genus curve: `analyticLoopsGenerateH1_elliptic`
(`Elliptic/H1Basis.lean`) proves `AnalyticLoopsGenerateH1 (0 : Elliptic ω₁ ω₂ h)`
unconditionally and axiom-free, via the covering-space `H₁ ≃ Λ` basis realized
by concrete oriented elliptic loops (`ellipticH1Basis_eq_loops` +
`analyticLoopsGenerateH1_of_h1LoopBasis`). This is the g = 1 instance of the
general residual; the general (g ≥ 1, arbitrary compact X) case is the
slit-sheet gap above. `#print axioms` = standard-3.

## 3. The collapse certificate — PROVEN this lane

`H1Composite.lean` gains `h1Free_finite_rank_of_periodInjective`: under T-GEN +
`[DiscreteTopology (loopPeriodLattice x₀ b)]` + KER-0, `H1 X x₀` is
`Module.Free ℤ`, `Module.Finite ℤ`, and `finrank ℤ = 2g`. Proof: KER-0 makes
`φ̄ : H1 ↠ Λ` injective, hence `H1 ≃ₗ[ℤ] Λ` (`LinearEquiv.ofBijective`); Λ is
free f.g. rank 2g (K-LITE), and all three transfer across the equiv.

This certifies §0: the four residuals collapse to {T-GEN, KER-0} as an
*equivalence* — `_of_periodInjective` (KER-0) and `_of_topology` (the triple)
are inter-derivable given T-GEN + K-LITE. The remaining mathematical content
is exactly KER-0 = period-injectivity, whose rank half is the de Rham layer
(`TRANK_SCOPING.md` route (a)) and whose torsion half is "H₁ torsion-free".

## 4. Kernel closures

`h1Free_finite_rank_of_periodInjective`: `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (standard-3); named hypotheses
(T-GEN as `AnalyticLoopsGenerateH1`, KER-0 as a `∀`-hypothesis, K-LITE as the
`[DiscreteTopology …]` instance variable) appear as hypotheses/instances,
never as axioms. `AX_PeriodCycleBasis` is in **no** closure.

## 5. Bottom line for the flip

```
K-LITE (TR-DISC):  [DiscreteTopology (loopPeriodLattice x₀ b)]   — parallel lane (PR #233)
                     └─ Λ free f.g., finrank ℤ Λ = 2g
H₁ side residual  =  T-GEN  +  KER-0          (= T-FG + Free + T-RANK≤, equiv.)
                     │          └─ rank half: de Rham comparison (TRANK route (a), multi-week)
                     │          └─ torsion half: H₁ torsion-free
                     └─ punctured-plane done (#227); compact-surface slit-sheet lift OPEN
flip = exists_h1LoopBasis_of_periodInjective  (+ R1/R2 per H1_COMPOSITE_ROUTE §4)
```

No residual is dischargeable by short composition at this HEAD. The lane's
deliverable is the **collapse certificate** (§3, proven) + this precise naming
of the two genuine open inputs (T-GEN-on-X slit-sheet lift; KER-0 de Rham
rank), so the flip's bill of materials is exact and minimal.
