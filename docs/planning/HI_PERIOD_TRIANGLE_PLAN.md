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
- [~] A1. `devVal_symm` — `developingValue` of a reversed path = `−developingValue`   status: in_progress   deps: []   note: dispatched to Codex (A1–A5 foundation)
- [~] A2. `devVal_trans` — `developingValue` of a concatenation = sum   status: in_progress   deps: []   note: dispatched to Codex; workhorse (subdivision-of-concat)
- [~] A3. `devVal_refl` — `developingValue` of a constant path = `0`   status: in_progress   deps: []   note: dispatched to Codex
- [~] A4. `devVal_subdivision` — `developingValue γ = Σ devVal(edge segment)` from `developingValueOfSubdivision_eq_of_subdivisions`   status: in_progress   deps: [A2]   note: dispatched to Codex
- [~] A5. `devVal_cell_eq` — `devVal Bᵢ − devVal Tᵢ = devVal Lᵢ − devVal Lᵢ₊₁` (cell-boundary loop `B·R·T⁻¹·L⁻¹` in one chart ⇒ 0 by the single-ball base case; split via A1/A2/A3)   status: in_progress   deps: [A1, A2, A3]   note: dispatched to Codex
- [ ] A6. `devVal_strip_eq` — `Σᵢ devVal Bᵢ = Σᵢ devVal Tᵢ` (telescope A5 via `Finset.sum_range_sub`; `L₀,Lₘ` constant rel endpoints ⇒ 0). **Hardest lemma.**   status: todo   deps: [A5]
- [ ] A7. `devVal_homotopy_invariant` — grid from `exists_chart_subordinate_grid` + 1-D row induction with A6   status: todo   deps: [A4, A6]
- [ ] A8. `canonicalArcIntegral_homotopy_invariant` — substitute HI-0 bridge   status: todo   deps: [A7]

### HI-2 — factor through H₁
- [ ] B1. `loopIntegralFundamentalGroupHom : FundamentalGroup X x₀ →+ ℂ` (per ω; well-defined by A8, additive by A2)   status: todo   deps: [A8]
- [ ] B2. factor through `H₁ = Abelianization (FundamentalGroup X x₀)` via `Abelianization.lift`   status: todo   deps: [B1]

### HI-3 — loop integral ∈ Λ
- [x] C1. verify the existing cycle basis spans abelianized π₁ via `AX_AnalyticCycleBasis` — **NO new axiom**   status: done   deps: []   note: CONFIRMED 2026-06-06. `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` (Homology.lean:41) = exactly the HI-2 target. `AnalyticCycleBasis.isBasis : Module.Basis (Fin 2g) ℤ (H1 X x₀)` spans by def (`Basis.repr`/`sum_repr`); `loops_to_basis` ties basis vectors to `loopToHomology (loops i)`. HI-3 = `isBasis.repr` + basis periods define Λ. No new axiom — whole workstream reuses `AX_AnalyticCycleBasis`.
- [ ] C2. `loop_integral_mem_periodLattice` — any loop's class is a ℤ-combo of the basis whose periods ∈ Λ   status: todo   deps: [B2, C1]

### Discharge
- [ ] D1. `AX_Period_Triangle` as a `theorem` — triangle = closed loop `(p_xy.trans p_yz).trans p_xz.symm` at x; integral ∈ Λ by C2 + arc algebra   status: todo   deps: [C2]
- [ ] D2. retire the axiom; `#print axioms` verify (no sorryAx / no new axiom); update `AXIOM_AUDIT.md` (counts, by-class breakdown — guard enforces), README, golden report; PR   status: todo   deps: [D1]

## Sequencing
A1–A3 are independent (parallelizable). A4 needs A2. A5 needs A1–A3. A6 needs A5
(the crux). A7 needs A4+A6. A8 needs A7. B/C/D are mostly algebra once A8 lands.
Park any item that blocks on a genuine Mathlib gap (note it) and move on; escalate
to MRD only for: a new axiom, or a frozen-interface change.
