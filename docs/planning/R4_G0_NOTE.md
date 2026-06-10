# R4 genus-0 routing decision (the Gemini DT flag on PR #156)

*2026-06-10, lane R step R4 (`docs/planning/CAMPAIGN_KEYSTONE.md`; scoping
`docs/planning/S3_FINESHEAF_RES_SCOPING.md`). Status: **decision recorded**, no Lean change
required in lane R.*

## The flag

Gemini deep-think's verdict on PR #156 (R3, `IsOneZeroCoeff`/`glueCoeff` design delta) raised one
real flag: **the Forster fine-sheaf residue construction genuinely does not cover genus 0**. The
`dz`-slot family of the glue law must be the chart-coefficient family of a **nonzero global
holomorphic 1-form** `ω₀` (`OmegaWitness.lean`: `omegaCoeff 𝔇 ω₀`, `isOneZeroCoeff_omegaCoeff`).
At `kirovGenus X = 0` we have `HolomorphicOneForms X = 0` (finrank = genus), so the only
inhabitant of `IsOneZeroCoeff` is the `0` family, `glueCoeff` is identically `0`, and the R4
functional carries no information. This is a true mathematical boundary, not a formalization gap:
`deg K_X = 2g − 2 = −2 < 0` at `g = 0`, so no effective canonical divisor `K = div ω₀` exists and
the §17.4 twist `𝒪_K ≅ Ω` that lane R is built on has no holomorphic anchor.

## Decision

1. **Lane R (R4–R8) is conditioned on `0 < kirovGenus X`.** The non-triviality statement of the
   R4 witness is stated exactly so: `exists_omegaCoeff_ne_zero (hg : 0 < kirovGenus X)`
   (`OmegaWitness.lean`). No lane-R rung should be stated in a way that asserts a nonzero
   functional at `g = 0`.
2. **Do NOT fake a `g = 0` witness.** Inhabiting `IsOneZeroCoeff` at `g = 0` by anything other
   than the `0` family would require a *false* overlap law (a nonvanishing `(1,0)` family on `ℙ¹`
   would integrate to a nonzero holomorphic form). Any such "witness" would be the
   strengthened-axiom satisfiability trap of pinned issue #82.
3. **Do NOT generalize `ω₀` to a meromorphic form (for now).** Gemini's alternative — meromorphic
   `ω₀`, importing its poles into the `g`-slot — would break `IsOneZeroCoeff`'s `AnalyticAt`
   field at the `ω₀`-poles and re-import the K-point pole-management problem into the `dz`-slot,
   where (unlike the scalar `w`-side) no cover refinement can remove it (the poles are in the
   family itself, not in overlap data). The cost/benefit is wrong while a complete `g = 0`
   alternative already exists in the snapshot.
4. **Genus 0 routes through the snapshot's direct genus-0 feeders** — this is exactly S9 of the
   S3 scoping ("out of scope for S3"), already decided there and reaffirmed here:
   * `SerreResidueDirectGenus0*.lean` (e.g. `residueTheorem_ofAdapted_genus0`,
     `residueTheorem_ofCanonicalSimpleInfty_genus0` in `SerreResidueDirectGenus0Assemble.lean`)
     prove the genus-0 residue statements directly, with no fine-sheaf functional;
   * at `g = 0` the duality bookkeeping degenerates: `h¹(𝒪) = g = 0` and `H⁰(Ω) = 0`, so the
     `SerreDualityData` fields at `g = 0` are carried by the explicit `ℙ¹` computations (the
     `H¹(ℙ¹, 𝒪) = 0` circle of results), not by a residue pairing built from `ω₀`.
5. **Keystone consumption point.** When R7/R8 feed `GlobalResidue → toSerreDualityData` into the
   keystone `exists_serreDualityData` (`SerreDualityPairing.lean:131`), the discharge is by
   **case split on `kirovGenus X`**: the `0 < kirovGenus X` branch is lane R's
   `CousinResidueData` route with `K = div ω₀`; the `kirovGenus X = 0` branch is the S9
   direct-genus-0 leg. The case split lives at the keystone instantiation, not inside lane R.

## Tracking

* The constraint and pointer to this note are recorded in the `OmegaWitness.lean` module
  docstring (next to the K-point cover-refinement note, per the Gemini verdict's request to
  record them together).
* S9 remains a separate deliverable of the gap analysis; nothing in R4 advances or blocks it.
