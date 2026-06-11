# DICT_BLOCKER — residual status of the Čech↔tail dictionary discharge

Branch `feat/cech-tail-dictionary`, 2026-06-11.  Companion to
`docs/planning/DICT_ROUTE.md` (the route decision and discoveries D1–D3).

## Verdict (keystone-completion question)

`CechTailComparison 𝔇 g G D` for the concrete fine-sheaf `G` is **NOT yet an
unconditional theorem for all `D`** — but its status changed in three ways on this
branch:

1. **Pinched exactly** (`TailDictionary.lean`): given the slot frame
   (`SlotExactK`, `K ≥ 0`), `CechTailComparison 𝔇 g G D ↔ G.UnwindRegularity D`
   (`cechTailComparison_iff_unwindRegularity`, standard-3).  The open core is exactly
   the isolation-free §17.7 regularity — no separate "dictionary" content remains.
2. **Conditional theorem** (`TailDictionary.lean`): for every `D` with
   `BadPointsIsolated 𝔇 K D`, `CechTailComparison` IS a theorem for the concrete `G`
   (`cechTailComparison_concrete_of_isolated`, standard-3).
3. **The analytic wall is BROKEN** (`FineResidue/GlobalCorrection.lean`): the
   multi-chart (non-isolated marked point) residue evaluation — both walls of
   `UNWIND_BLOCKER.md` — is now a THEOREM,
   `resFunctional_eq_neg_residue_of_global_correction` (standard-3): the residue
   functional evaluates a coboundary with a non-isolated marked simple pole to `−r`,
   via the global-cutoff-subtraction presentation (D3), the general R0 atom (D1), and
   the relocation collapse.  No new analytic atom was needed.

## What remains (cocycle-side bookkeeping, no new analysis)

To assemble `unwindRegularity_concrete` (no isolation) and hence the unconditional
`cechTailComparison_concrete`, per `DICT_ROUTE.md` W2–W5:

* **W2 — the deep-matching star cocycle.**  At a non-isolated forced bad point `b`
  (where `K b = 0`, `K_apply_eq_zero_of_not_isolated`), the test cocycle needs
  per-star-chart sections `c_i ∈ 𝒪_{Ě+b}(U i)` whose FULL window Laurent tails at `b`
  (orders `−(m+1) … −(E b+1)`, read invariantly at `b`) match a common target — then
  `δ⁰c ∈ Z¹(𝒪_E)` and the class dies at level `D`.  The single-coefficient cone
  (`SkyscraperConeRealization.coneB0`) only matches the TOP coefficient (level-`Ě`
  membership); the multi-coefficient realization is a triangular induction over the
  window on `ExactOrderWitness` sections (realize the lowest-order coefficient, read
  off the witness's higher window coefficients, subtract, recurse).  Estimated
  ~300–400 LoC, elementary.
* **W3 — the X-side cutoff.**  A smooth `θ : X → ℂ`, `θ ≡ 1` near `b`,
  `tsupport θ ⊆ U j₀`, avoiding the finitely many other `(K+b)`-points (pull a planar
  `ContDiffBump` through the chart, `pouCoeff`-style smoothness).  ~100 LoC.
* **W4 — the presentation bookkeeping.**  `H := θ·vanishFn(fE·c)_{j₀}` and
  `h̃ := vanishFn(fE·c) − Ĥ` (constant cochain), with the one-point analytic repair of
  `h̃` at `b` (the matching parts cancel, `ord ≥ n − E b ≥ 0`); verify the engine's
  hypothesis list: `IsCoboundaryOn` survives the repair by continuity (the level-`K`
  cocycle is honest at `b` since `K b = 0`), `SlotProductExtendsAt` at unmarked
  K-points inherits from `slotProductExtendsAt_vanishFn` (supp `θ` avoids them),
  `hpole` comes from the existing `exists_slotProductSimplePoleAt` (which never used
  isolation).  ~250 LoC.
* **W5 — assembly.**  `unwindRegularity_concrete`: case split on
  `∃ j₀, MLIsolated 𝔇 j₀ b` (existing isolated theorem / the new engine via W2–W4);
  then `cechTailComparison_concrete` via `cechTailComparison_of_unwindRegularity`,
  and the keystone re-wiring through `pairing_surjective_of_cechTailComparison`.
  ~150 LoC.

None of these requires a new integral/analytic ingredient; the remaining risk is
bookkeeping-sized (window-coefficient reads across charts in W2 are the only
mathematically delicate point — restriction-invariance of `laurentCoeff` at `b` is
already available via `coeffWFn_comp_openIncl`).

## Why per-instance uses are NOT blocked

Any consumer with a specific `(E, fE, lam)` whose order violation sits at a
cover-isolated point can already use `cechTailComparison_concrete_of_isolated` /
`unwindRegularity_concrete_of_isolated`.  The open case is only the worst-case `D`
whose every bad point is non-isolated.
