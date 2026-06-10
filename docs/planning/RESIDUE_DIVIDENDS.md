# Residue-theorem dividends — what the Kirov port's `∑Res = 0` buys us (D2)

*2026-06-10. Port assets (all sorry-free, standard-3, importable via the S2 Lake
path dep): `residueTheorem_unconditional`
(`KirovDolbeault/Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean:1017`),
`MeromorphicFunction.deg_div` (`KirovDolbeault/RiemannRoch.lean:76`),
`GeneralMLDistribution.res_eq_zero_of_globalMeromorphic`
(`KirovDolbeault/Dolbeault/GeneralMittagLeffler.lean`, Forster §17.3).
Type-shape caveat for all three: the port writes a meromorphic 1-form as `g·ω₀`
(a `MeromorphicFunction` times a global holomorphic form), so the residue
results bite only when a nonzero `ω₀` exists (g ≥ 1); genus 0 uses their sphere
modules.*

## Hits

**1. `serreDuality_equiv` (Layer-3 axiom, `Jacobians/Layer3/Cohomology.lean`,
audit rows AXIOM_AUDIT.md:302/345) — THE dividend.** Forster's Serre duality is
exactly: the ML-residue pairing descends to `H¹` (well-defined = §17.3
coboundary vanishing = `res_eq_zero_of_globalMeromorphic`) and is perfect
(§17.5/§17.9 = the open keystone `exists_serreDualityData`). The descent half is
now fully proved in the port; everything below the keystone rests on
`residueTheorem_unconditional`. What it discharges: nothing *by itself* — it is
the substrate that makes Phase D item B (keystone) the single remaining
chokepoint for `serreDuality_equiv` + `h1coh_zero_finrank` (41 → 34 axioms if it
falls). Alignment cost: the L(D) bridge (`riemannRochSpace D ⊆ MeroField X`
germ-quotient vs their `linearSystem D ⧸ germZeroSubmodule`) — already scoped as
the one substantive mismatch in `PHASE_D_TYPE_ALIGNMENT.md`. **Priority:
after-L(D)-bridge (= Phase D order A4 → B as planned; the residue layer is why B
is now credible).**

**2. `serre_anchor` sorry (`RiemannSurface/Cohomology/RiemannRochAnchor.lean:56`,
also `:39`, `:45`).** Its docstring's "residue pairing on Weil repartitions"
needs exactly the §17.3 coboundary vanishing. But repartitions ≠ ML
distributions — that dictionary is new work — and Phase D replaces `H1coh` with
the port's Čech model anyway, demoting the adelic anchor to a secondary model.
**Priority: not-worth-it for the anchor specifically** (the content reaches us
cheaper through hit 1); revisit only if the adelic program (#103/#105) resumes.

**3. Abel ⊇ direction — trap rationale invalidated, route choice unchanged.**
`docs/planning/AX_AbelTheorem.md` (refresh item 3, 2026-06-07) bypassed the
residue route because it needed "3000+ LOC of nonexistent manifold-Stokes API."
That premise is now false — the port built exactly that API (real-slit
geometry + manifold trace `FormResidueTheorem`), sorry-free. However, the
classical Forster §20.7 ⊇ proof needs *more* than `∑Res = 0`: third-kind
differentials with prescribed residues (gated on the Serre keystone) plus the
period-reciprocity law, neither of which the port has sorry-free
(`CutSurfaceRelations.lean` still has sorries). The Liouville/ℙ¹ route
(`ABEL_SUPSET_LIOUVILLE_ROUTE.md`, ~800–1200 LOC, zero new bridges) remains
strictly cheaper. **Priority: not-worth-it now; moot unless reciprocity lands
upstream — note the "trap" justification should not be cited again.** The ⊆
direction's Route A (RR+Serre, `ABEL_SUBSET_FORSTER_ROUTE.md`) benefits
indirectly but only through hit 1's keystone.

**4. `deg_div` — redundant, zero dividend.** We already have
`deg_divisor_eq_zero` (`RiemannSurface/Cohomology/DegreeTheorem.lean:334`),
sorry- and axiom-free via Wallace's `weightedFiberConservation` ℙ¹-degree route
(#120); it already feeds `RiemannRochAPI.lean:200` and the `AX_AbelTheorem`
degree-0 restriction. Kirov's copy proves the same fact over *their*
`MeromorphicFunction`/`Divisor` types — bridging costs more than reproving
nothing. Useful at most as an independent cross-check. **Priority:
not-worth-it.**

**5. Argument principle (∑ res of df/f) — no open consumer.** All counting
needs (`DegreeViaP1.lean:46`, `Axioms/BranchLocus.lean:130`,
`DegreeOneGenusZero.lean:192`) are served residue-free by Wallace's
`weightedFiberConservation_of_contMDiff` (`HolomorphicMap.lean:1199`); cf.
`docs/deep-think-residue-theorem-route.md:126`. **Priority: not-worth-it.**

**6. `Layer3.AX_RBR1` (isotropy/Stokes, `Layer3/Periods.lean:67`).** Untouched
by `∑Res = 0` itself; its port route is the bilinear relations gated on
`exists_cutSurface` (Phase D item C, sorries remain). The sorry-free slit-Stokes
machinery raises confidence in C but discharges nothing today. **Priority:
after-L(D)-bridge via item C, not via the residue theorem.**

## Bottom line

Concentrated, not diffuse: hits 3–5 were already routed around (Liouville,
Wallace degree theory). The one real dividend is hit 1 — the residue layer
completes the floor under `exists_serreDualityData`, making
`serreDuality_equiv` + `h1coh_zero_finrank` a single-keystone problem.
