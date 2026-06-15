# Finishing the odd-hyperelliptic cycle basis + explicit period map — plan

**Goal.** Complete the canonical homology (cycle) basis on the odd hyperelliptic surfaces
`y² = f(x)` (`deg f = 2g+1`) and the explicit map **moduli (= the branch points / coefficients of
`f`) → period matrices**, thereby (a) **discharging `AX_PeriodCycleBasis` on the odd hyperelliptic
family** and (b) realizing the period map into the **Siegel upper half space** (the launchpad for
hyperelliptic Torelli).

Companion to the gap ledger [`HYP_CB_BLOCKER.md`](HYP_CB_BLOCKER.md) (gaps **G-A…G-E**, with discharge
routes) and [`CYCLEBASIS_ALTERNATIVES.md`](CYCLEBASIS_ALTERNATIVES.md). This doc is the **forward
route + the post-#223 update**; it does not duplicate the ledger's gap analysis.

## Where it already stands (mostly built, 0–3 sorries)

- **The explicit period map already exists** (`Hyperelliptic/BoundaryWord.lean`, 0 sorries):
  `aPeriodIntegral` / `bPeriodIntegral` give each period-matrix entry `Ω_ij` as an **explicit
  x-plane branch-cut integral** `∫₀¹ (form-coeff)·x′ dr` (= `∮ xᵏ dx/y` over the cuts), a function of
  `f`'s branch points; `arcA/BPeriodMatrix_branchCut` tie these to the A/B period blocks. *(Not
  closed-form — hyperelliptic integrals are special functions — but it is the genuine explicit map.)*
- **The conditional witness is proven** (`Hyperelliptic/CycleBasisWitness.lean`):
  `nonempty_periodCycleBasis_of_branchCutSystem` inhabits `PeriodCycleBasis (HyperellipticOdd H h)`
  from a `BranchCutSystem` plus **four inputs** — `isBasis`, `tie` (the 2g loops are a ℤ-basis of H₁),
  `hR1` (`Q(period,period)=0`), `hR2` (positivity). So discharging the axiom on the family **=
  supplying those four**.
- Foundations landed (see ledger "DONE"): `SqrtArcData` + branch lift, `loop_period_eq`,
  `arcPeriodVec` reduction, loop conjugation, and the `R1Word`/`R2GramWord` definitions with their
  `r1Word_iff_integrals` / `r2GramWord_iff_integrals` reductions to explicit interval-integral families.

## NEW unblock — PR #223 (2026-06-15), which the ledger predates

PR #223 discharged `AX_Hyperelliptic_genus` and proved the **odd one-form representation**
`AX_HyperellipticOddOneForm_eq_form_proof` ({holomorphic 1-forms} = `{xᵏ dx/y : k<g}`, dimension `g`).
Consequences for the ledger:
- **G-C.3 (analytic-genus gate) is now resolved** — `genus (HyperellipticOdd H h) = (deg f−1)/2` is a
  theorem and the explicit `g`-form basis `xᵏ dx/y` is exhibited.
- **G-D's direct-computation route is now enabled** — the ledger gated R1/R2-by-direct-computation on
  "`AX_Hyperelliptic_genus` pins the form space"; that pin now exists.

## The four witness inputs → ledger gaps → the g=1 → general-g route

| witness input | ledger gap | g=1 template | route for general `g` |
|---|---|---|---|
| cycle **closure** | G-A | — | sqrt monodromy: a circle closes iff it encloses an **even** number of branch points (`L(1) = 2πi·#enclosed ∈ 4πiℤ`); residue/winding via Mathlib `circleIntegral` + `Polynomial.roots`. Self-contained; ~days–week. Clears the `CycleLoops.lean` sorry. |
| cycle **layout** | G-B | — | enumerate roots of `f`, pair by proximity, thin Jordan loops around each pair (`segmentX`+`circleX` via `AnalyticArc.trans`). Plane geometry + finite combinatorics; no manifold content. |
| `isBasis` + `tie` | **G-C** | `ProjectiveCurve/Elliptic/H1Basis.lean` | SVK (the port's proven `VanKampen.lean` two-open method) ⇒ π₁(ℂ∖{2g+1 pts}) free on the loops; lift through the index-2 double cover (`HyperellipticAffine.sqMap_covering` + `Topology.Homotopy.Lifting`) + the ∞-compactification; abelianize, rank `2g`. **G-C.3 done (#223).** The research-grade half; clears the `Index2KernelGeneration.lean` sorry. |
| `hR1` | **G-D** | `RiemannSurface/BoundaryWordElliptic.lean` | R1 = `AᵀB = BᵀA` (period matrix symmetric), reduced by `r1Word_iff_integrals` to x-plane interval-integral identities; **direct per-branch-pair computation** over `xᵏ dx/y` (enabled by #223), generalizing the elliptic boundary word. |
| `hR2` | **G-D** | `RiemannSurface/BoundaryWordEllipticPoly.lean` | R2 positivity (`Im Ω ≻ 0`) reduced by `r2GramWord_iff_integrals` + **Cholesky tuning** of the polynomial family `P`, generalizing `elliptic_word_R2_lhs` + `boundaryForm_const_linear`. |

## Sequencing & effort

1. **G-A + G-B** (build the actual cycles) — complex analysis (winding/residue) + plane geometry;
   ~1–2 weeks. Clears 2 of the 3 residual sorries.
2. **G-D** (R1/R2) — now the **direct** branch-cut computation over `xᵏ dx/y` (the `r*_iff_integrals`
   reductions make it computational, not abstract Stokes); generalize the g=1 boundary-word proofs.
   ~1–3 weeks; R2/positivity (the Cholesky tuning) is the trickier half.
3. **G-C** (H₁ ℤ-basis) — the SVK/covering package; the research-grade half, de-risked by
   `VanKampen.lean` + #223's genus; weeks.

**G-C and G-D are independent** (the witness consumes them through separate hypothesis slots), so they
can proceed in parallel. **G-E** (even model `HyperellipticEvenProj`) is a follow-on: the `SqrtArcData`
layer is model-independent up to the chart-readout lemma, which must be re-proven against `EvenAtlas`.

**Assembly.** Feed `(isBasis, tie, hR1, hR2)` into `nonempty_periodCycleBasis_of_branchCutSystem` ⇒
`PeriodCycleBasis (HyperellipticOdd H h)` becomes **unconditional** ⇒ `AX_PeriodCycleBasis` discharged
on the odd hyperelliptic family; and `BoundaryWord`'s `Ω` becomes an unconditional period map landing
in Siegel space.

## Outcome
- `AX_PeriodCycleBasis` discharged on the **entire odd hyperelliptic family** — a concrete dent in the
  last big topology axiom (the "hyperelliptic route").
- A fully **explicit (integral-form) period map** `f ↦ Ω(f)` into the Siegel upper half space — the
  natural launchpad for a hyperelliptic **Torelli** statement (injectivity of the period map on moduli).

*References:* gap ledger [`HYP_CB_BLOCKER.md`](HYP_CB_BLOCKER.md); alternatives
[`CYCLEBASIS_ALTERNATIVES.md`](CYCLEBASIS_ALTERNATIVES.md); g=1 templates
`Jacobians/ProjectiveCurve/Elliptic/H1Basis.lean`,
`Jacobians/RiemannSurface/BoundaryWordElliptic.lean`,
`Jacobians/RiemannSurface/BoundaryWordEllipticPoly.lean`; the period-map engine
`Jacobians/ProjectiveCurve/Hyperelliptic/BoundaryWord.lean`.
