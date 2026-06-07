# Discharge `AX_Period_Triangle` via HI-1 → HI-2 → HI-3 (plan-loop)

*2026-06-06. MRD-approved hard-axiom target. Strategy vetted by Gemini deep-think
(Route A, decisive). Branch `hi-1-period-triangle`. This file is the plan-loop
source of truth — re-read every cycle; statuses live here.*

## Goal
Discharge `AX_Period_Triangle` (`Axioms/AbelJacobiMap.lean:165`) — the period
1-cocycle: the closed triangle `p_xz − p_xy − p_yz` (loop x→y→z→x) has period ∈ Λ.

## Strategy (Gemini-deep-think-vetted, Route A)
**Route A** (telescope `developingValue` over a homotopy grid) — decisively chosen.
Route B (espace-étalé `X̃ω` + `IsCoveringMap` from scratch) is multi-month; Mathlib
lacks the sheaf→covering API. Route A reuses everything HI-0 built.

**The 1D-strip trick** kills the 2D-bookkeeping slog: per horizontal strip the
single-cell identity `V(Bᵢ) − V(Tᵢ) = V(Lᵢ) − V(Lᵢ₊₁)` telescopes via
`Finset.sum_range_sub` to `V(L₀) − V(Lₘ) = 0` (outer edges are constant paths, rel
endpoints); then 1-D induction over rows. No manual 2D edge-cancellation.

**Already built (reuse):** HI-0 `developingValue = canonicalArcIntegral` (standard-3);
`developingValueOfSubdivision_eq_of_subdivisions` (well-defined); single-ball base
case `developingValue_eq_zero_of_loop_in_pathChartBall`; `exists_chart_subordinate_grid`
(2D grid); arc algebra `canonicalArcIntegral_reverse`/`_trans`. Mathlib:
`FundamentalGroup`, `Abelianization.lift`, `Finset.sum_range_sub`.

**Post-HI-1 reduction (Gemini):** HI-2 via `FundamentalGroup X x₀ →+ ℂ` +
`Abelianization.lift` (commutators vanish definitionally; bypasses Hurewicz). The
"cycle basis spans abelianized π₁" need is **likely already `AX_AnalyticCycleBasis`**
(a basis spans) — verify NO new axiom. HI-3 + triangle then routine.

## Guardrails
No new axiom (the whole point — must reuse `AX_AnalyticCycleBasis`, not add a
spanning axiom). Build-gate each item (`lake env lean` / `lake build`). `#print
axioms` on the final theorem: no `sorryAx`, no new project axiom. Update
`AXIOM_AUDIT.md` + counts + the by-class breakdown (guard enforces sum) in the
same commit that retires the axiom.

## Plan (status machine — plan-loop re-reads this)

### Setup
- [x] S0. Branch `hi-1-period-triangle` + this plan doc   status: done   deps: []

### HI-1 — homotopy invariance of `canonicalArcIntegral` (developing-value path algebra)
- [x] A1. `devVal_symm` — `developingValue` of a reversed path = `−developingValue`   status: done   deps: []   note: committed 1b2c277
- [x] A2. `devVal_trans` — `developingValue` of a concatenation = sum   status: done   deps: []   note: DONE 7117e9b (sorry-free, standard-3). Workhorse; stalled 4 Codex attempts on Fin.append. Cracked via Gemini-3.1-pro Nat-conditional `S_trans` glued subdivision (`if i.1 ≤ S₁.n` + omega) + `Fin.sum_univ_add` split + per-cell `devInc_castAdd/natAdd` (Path.trans_apply branches; j=0 shared-midpoint same-chart).
- [x] A3. `devVal_refl` — `developingValue` of a constant path = `0`   status: done   deps: []   note: committed de784fa
- [x] A4. `devVal_subdivision` — `developingValue γ = Σ devVal(edge segment)`   status: done   deps: [A2]   note: DONE c29753a (sorry-free, standard-3)
- [x] A5. `devVal_cell_eq` — `devVal Bᵢ − devVal Tᵢ = devVal Lᵢ − devVal Lᵢ₊₁` (cell-boundary loop in one chart ⇒ 0 via base case; split via A1/A2/A3)   status: done   deps: [A1, A2, A3]   note: DONE c29753a (sorry-free, standard-3)
- [x] A6. `row_sum_eq` (devVal_strip_eq) — strip telescope via `Finset.sum_range_sub`   status: done   deps: [A5]   note: DONE a3bba88. Gemini-3.1-pro grid blueprint (extGrid ℕ-index, definitional edges, double sum_range_sub, IsCompact→subset_ball).
- [x] A7. `developingValue_homotopy_invariance` — col telescope + grid assembly   status: done   deps: [A4, A6]   note: DONE 60c8ddb (col_sum_eq 2d6c630 + plumbing)
- [x] A8. `canonicalArcIntegral_homotopy_invariant` — substitute HI-0 bridge   status: done   deps: [A7]   note: DONE edabd9a. **#print axioms = [propext, Classical.choice, Quot.sound] (STANDARD-3, no sorryAx, no project axiom). HI-1 COMPLETE.**

### HI-2 — factor through H₁
- [x] B1. `loopDevValHom : FundamentalGroup X x₀ →* …ℂ` (well-defined by A8, additive by devVal_trans)   status: done   deps: [A8]   note: DONE e0a8413
- [x] B2. `loopDevValH1Hom : H1 X x₀ →+ ℂ` via `Abelianization.lift` + basis-compat `loopDevValH1Hom_cycleBasis_loop`   status: done   deps: [B1]   note: DONE 8f736aa (standard-3; compat uses existing AX_AnalyticCycleBasis)

### HI-3 — loop integral ∈ Λ
- [x] C1. verify the existing cycle basis spans abelianized π₁ via `AX_AnalyticCycleBasis` — **NO new axiom**   status: done   deps: []   note: CONFIRMED 2026-06-06. `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` (Homology.lean:41) = exactly the HI-2 target. `AnalyticCycleBasis.isBasis : Module.Basis (Fin 2g) ℤ (H1 X x₀)` spans by def (`Basis.repr`/`sum_repr`); `loops_to_basis` ties basis vectors to `loopToHomology (loops i)`. HI-3 = `isBasis.repr` + basis periods define Λ. No new axiom — whole workstream reuses `AX_AnalyticCycleBasis`.
- [x] C2. `loop_integral_mem_periodLattice` — any loop's developing periods ∈ Λ   status: done   deps: [B2, C1]   note: DONE 0d05da2 + crux agreement dc98014 (loopDevValH1Hom = loopIntegralToH1 on spanning cycle basis)

### Discharge
- [x] D1. `AX_Period_Triangle` as a `theorem` — triangle loop at x; integral ∈ Λ by C2 + HI-0 + devVal_trans/symm   status: done   deps: [C2]   note: DONE a594e2e
- [x] D2. retire the axiom + reconcile counts (59→58)   status: done   deps: [D1]   note: DONE a594e2e + 7aac720. #print axioms ofCurve_inj: NO AX_Period_Triangle, NO sorryAx. Kernel 58. Guard green at 58. **AX_Period_Triangle DISCHARGED — whole HI workstream complete, no new axiom.**

## Sequencing
A1–A3 are independent (parallelizable). A4 needs A2. A5 needs A1–A3. A6 needs A5
(the crux). A7 needs A4+A6. A8 needs A7. B/C/D are mostly algebra once A8 lands.
Park any item that blocks on a genuine Mathlib gap (note it) and move on; escalate
to MRD only for: a new axiom, or a frozen-interface change.
