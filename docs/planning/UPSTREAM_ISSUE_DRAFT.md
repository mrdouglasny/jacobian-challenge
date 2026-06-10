# DRAFT — upstream coordination issue (DO NOT POST)

- **Target repo:** `rkirov/jacobian-claude`
- **Suggested title:** Serre-duality keystone (`exists_serreDualityData`): gap analysis, a question about the Cousin-split route at g > 0, and an offer to split the work
- **Suggested labels:** `question`, `collaboration` (or whatever the repo uses)
- [ ] **OWNER APPROVAL REQUIRED BEFORE POSTING** (@mrdouglasny)

---

## Issue body

Hi — we're [mrdouglasny/jacobian-challenge](https://github.com/mrdouglasny/jacobian-challenge), a sibling effort on the Buzzard Jacobian challenge. We've vendored your repo at `4437c2b` (forward-ported to Mathlib `c5ea003`, builds green) with Apache 2.0 attribution, and we're already consuming your sorry-free `exists_cechModel` and `exists_skyscraperLES` to discharge our own Čech-finiteness and LES axioms. Thanks for the work — the Dolbeault tower is excellent.

We did a detailed gap analysis of the remaining Serre sorry, `exists_serreDualityData` (`SerreDualityPairing.lean:125`), tracing your assembly chain `MeromorphicCousinSolutions → CousinResidueData → GlobalResidue → SerreResidueRealization → SerreDualityData`. Full writeup: [`docs/planning/KEYSTONE_GAP_ANALYSIS.md`](https://github.com/mrdouglasny/jacobian-challenge/blob/main/docs/planning/KEYSTONE_GAP_ANALYSIS.md). Summary of what we found (please correct anything we misread):

- `finH1` and `hKgenus` look unconditionally discharged already; `ι_inj` is reduced to the residue-1 witness interface; the §17.9 count is abstractly proven (`serre_surjectivity_dim_core`) with all RR inputs (`cohomological_riemannRoch`, `riemannRoch_inequality`, `h0Dim_eq_lDim`, `lDim_eq_zero_of_deg_neg`) available.
- The remaining content seems to be: the `vanish`/`nondeg` bookkeeping, Forster 17.7/17.8, the 17.9 assembly, and **one** genuinely hard object — the global residue functional behind `lift`.

**One thing we'd like your read on (we may be missing context).** The `lift` route goes through `CousinSplittable`, whose (A) engine `exists_holoSplit_of_isDiskAcyclic` assumes `IsDiskAcyclic 𝔘 0`, i.e. `H¹(𝔘, 𝒪) = 0` — which for a Leray cover of `X` seems false when `g > 0` (`h¹(0) = g`), and `IsDiskAcyclic` is currently proven only for single-chart `SharedChartCover` families. Killing the holomorphic remainder with extra poles appears to need `h¹(K + nP) → 0`, which is classically itself a Serre corollary — so we think there may be a circularity risk in the current shape. Does that match your understanding, or is there a planned route we haven't seen? If it is a real wall, would Forster's own §17.3 definition of `Res` (partition-of-unity + Dolbeault (1,1)-integral + Stokes, no harmonic theory) be acceptable within your PDE-free constraint?

**Offer — division of labor.** The pieces below the residue core are self-contained against your frozen interfaces (`GlobalResidue`, skyscraper LES, the RR API), so they're invariant under whatever you decide for `res`. We'd be glad to take, as upstream PRs:

1. the `hR : LocallyRealizable` signature change to `exists_serreDualityData` (+ threading through `DolbeaultLadder`), since every §17.9 input needs it and the sole consumer already has it in scope;
2. the §17.9 count skeleton: a `SurjectivityInputs` structure (17.7 + 17.8 as named fields) with `ι_surj_of_inputs` proved from `serre_surjectivity_dim_core` and your RR API;
3. then 17.8 (the `ψ`-action via iterated skyscraper `surj₄`) and 17.7 (restriction/unwinding), and the `nondeg` (`dz/z` witness) and `vanish` (Gate-A descent) bookkeeping.

You'd keep the analytic core — the `GlobalResidue` construction itself (Cousin solve or Dolbeault-integral `res`, per the architecture call above).

Concrete questions:

1. **Signature:** add `hR : 𝔘.LocallyRealizable` to `exists_serreDualityData` (and `arithmeticGenus_eq_genus` / `serre_h1_eq`), or restate the keystone at the canonical chart-disk cover?
2. **S3 architecture:** is `CousinSplittable` the intended plan for `g > 0` given the `IsDiskAcyclic` issue above, or is the Dolbeault/PoU-integral `Res` acceptable?
3. **Genus 0:** is the keystone at `g = 0` meant to be closed by the `SerreResidueDirectGenus0*` route, and is a genus case split inside the keystone proof acceptable?
4. **Division of labor:** does the split above work for you, and would you prefer it as upstream PRs or as work in our tree that you cherry-pick?

Happy to coordinate however is easiest — and to adjust to any in-flight work we'd otherwise duplicate.
