# R6D2 blockers — what the last analytic lane could NOT honestly close (2026-06-10)

Branch `feat/keystone-r6d2` (built on the R6 tie + R7 engine). Landed sorry-free:

* **D2a** — `MeroVanish.lean`: the bad-point coboundary engine
  (`resFunctional_eq_zero_of_mero_coboundary`) and the **order-`m` pole tie**
  (`resFunctional_poleCocycle_eq_zero_of_slot_vanishes`). Key simplification over the
  R7_BLOCKER sketch: NO higher-order Cauchy–Pompeiu ladder — the slot zero of order `≥ m`
  makes the smeared product extend analytically across the pole, so the surviving Stokes
  term dies by the R5a planar Stokes atom after a finite limit-repair (`pointRepair`).
* **D2b** — `DescentVanish.lean`: **`vanish_coboundary` at general `K`**
  (`resCocycle_vanish_coboundary`, replacing Descent's `K ≤ 0` restriction), the
  unconditional `liftQ` descent (`resH1_of_slotMatches`), the R6 bridge
  (`r6Outputs_holds` — `Descent.R6Outputs` is now a THEOREM), and the corrected §17.6
  witness interface (`CupMLWitnessR` + `nondegenerate_of_witnessR` +
  `cousinResidueData_of_witnessR`). The Laurent principal-part decomposition of the
  R7_BLOCKER §1 sketch was avoided by the **product-germ trick**: restrict the 0-cochain
  germ off the K-points, `holoFn`-extract, and at each K-point multiply the meromorphic
  germ by the slot pullback — the product is an `𝒪`-class (orders `−K a + K a ≥ 0`), and
  its `holoFn` IS the analytic extension the engine consumes.

The remaining gaps, with precise reductions:

## 1. `CupMLWitnessR` — the §17.6 transport CONSTRUCTION (D2d, the open half)

**Interface fixed, construction open.** `Descent.CupMLWitness` as stated demands the slot
value be EXACTLY `1` at the transported pole (`g j₀ (chartMap 𝔇 j₀ a) = 1`); for a fixed
slot family the level set `{g = 1}` can be empty (rescale `ω₀` small), so that interface is
in general **unsatisfiable** — flagged here, do not attempt to discharge it as stated.
`DescentVanish.CupMLWitnessR` corrects the normalization to `r · g j₀ (α) = 1` with the
transported residue `r` free (what the duality pairing actually needs, achievable by scaling
`ξ`), and drops the membership conjunct (now proven, `mlGlue_mem_oneOneCoeff`);
`nondegenerate_of_witnessR` re-proves the `nondegenerate` field from it via the landed
`resFunctional_mlGlue`.

What remains to inhabit `CupMLWitnessR 𝔇 hsep g`: given `0 ≠ v ∈ L(K−D)`,

* pick `a` off the poles/zeros of `v`, off `supp K ∪ supp D`, with `g j₀ (α) ≠ 0` AND
  `a` isolated in a single cover set — the existence of such an `a` for the FIXED `𝔇` is a
  **cover-geometry hypothesis** (a generic point lies in several cover sets); the honest
  route is the same refinement discipline as `SeparatesPoles`: build `𝔇` from the start
  with one reserved isolated point per ... OR formalize cover refinement at one extra point
  (`LerayCoverExists` + `ChartDiskRefinement` are the ingredients; refinement *invariance*
  of the functional is NOT needed — only existence of a refined cover for which the whole
  lane is instantiated).
* take `ξ := [η]` with `η` the one-point cocycle of the germ of
  `r·(z−α)⁻¹ · v⁻¹` (an `𝒪_D`-cocycle since `a` avoids `supp D` and the zeros/poles of
  `v`), `r := g j₀ (α)⁻¹`;
* compute `cup v ξ` at the cocycle level (`cupCochain1` multiplies by `globalGerm v`, so
  the product germ is `r·(z−α)⁻¹` exactly) and identify the extraction
  (`cocycleFn (v·η) = mlCocycle j₀ a r` on overlaps — `eq_at_of_toGerm_eq` + the germ
  computation; same pattern as `isCoboundaryOn_cocycleFn_vanishFn`).

Estimated: the cocycle-level cup computation and extraction identification are mechanical
(the tools are all in `Descent.lean`/`DescentVanish.lean`); the genuinely new ingredient is
the **isolated-point selection** (cover refinement or a reserved-point cover hypothesis).

## 2. `UnwindRegularity` for the concrete realization (D2c, S5 gap) — NOT closed

Two genuine walls beyond the one-point-cocycle machinery of §1:

* **The bad point is forced, not chosen.** The §17.7 argument evaluates the residue at a
  point `b` where the `L(K−D)` order bound FAILS — `b` is given by `v`, not selectable, so
  (a) `b` need not be isolated in the fixed cover (the ML tie and the whole
  `MLIsolated`-based engine do not apply without refinement-at-`b`), and (b) the test
  cocycle is `z^{−1−ord_b(v·ω₀-slot)}`, a HIGHER-ORDER pole — the evaluation needs the
  order-`m` tie with a NONZERO conclusion (residue extraction at order `m`), i.e. the
  Cauchy–Pompeiu derivative ladder `∫ ∂̄χ·(z−α)^{−m}·g̃ ∼ g̃^{(m−1)}(α)` that D2a
  deliberately avoided (D2a only needed the VANISHING direction, where the Stokes kill
  suffices). This is the first place the genuine higher-order Cauchy–Pompeiu atom is
  unavoidable.
* **Level bookkeeping at `E`.** The one-point test cocycle must lie in `Z¹(𝒪_E)` with
  `E = (D − nP) − div ψ` of arbitrary sign; on overlaps where `E < 0` membership demands
  zeros, not mere holomorphy — the K-point separation discipline does not cover E-negative
  loci. Needs either an `E`-aware cover discipline or the skyscraper route through
  `h1InclMono` kernels.

Recommended discharge order (next session): higher-order Cauchy–Pompeiu atom
(`∫ ∂̄(χ·(z−α)^{−m})·g̃` evaluation — extend `SignTest.integral_dbar_smearedSimplePole` by
differentiating Cauchy–Pompeiu `m−1` times, or integrate by parts in the area integral),
THEN the forced-point refinement, THEN `UnwindRegularity`.

## 3. `hga` (G0 bonus) — not attempted

`h1Dim 0 = 0` at genus 0 via Čech↔Dolbeault needs `H^{0,1} = 0` from "no holomorphic
1-forms", i.e. the conjugation/Hodge symmetry the port deliberately avoided
(`G0_BLOCKER.md` route 2). No new leverage from this lane: the D2a/D2b machinery is about
residue functionals, not about the vanishing of `H^{0,1}` itself. Stays with the G0 lane.
