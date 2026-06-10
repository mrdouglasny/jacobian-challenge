# Campaign: Fell the Keystone — `exists_serreDualityData` (36 → 34 axioms)

*Opened 2026-06-10, owner-approved in-session. Predecessor: the Phase-D night
(PRs #143–#152, 41→36). Operating pattern: implementation agents + fresh-context
review + Codex second pass; DT-vet every NEW structure statement before
reliance; #print axioms standard-3 gate per headline; one writer per tree.*

## Goal & effect

Discharge the port's keystone sorry `exists_serreDualityData`
(KirovDolbeault/Dolbeault/SerreDualityPairing.lean) → flip our last two
Layer-3 cohomology axioms (`serreDuality_equiv`, `h1coh_zero_finrank`) →
**RR + Serre rest on Lean core**; ledger 36 → 34; comparator run on
`riemannRochL3` at the end.

Decomposition status: S7 count skeleton LANDED (#146 —
`SurjectivityInputs.pairing_surjective`, reviewer-verified no vacuity hole).
Remaining = the two SurjectivityInputs fields (17.7, 17.8) + the
`GlobalResidue` construction + assembly. **Nothing research-grade**
(S3_FINESHEAF_RES_SCOPING.md verdict).

## Owner decisions recorded (2026-06-10)

- **E6 de-Rham headline: LEAVE.** The port's `DegreeOneSphere:703` bare-homeo
  sorry stays (off every critical path; our headline rests on the vetted
  Class-1 `AX_genus_eq_zero_iff_homeo`). Candidate campaign #2 with X1.
- **X1 HI developing-map gap: PARKED** (needs owner steer on approach; the
  `AX_ofCurve_contMDiff` truth-pin makes it non-parkable forever — revisit at
  campaign end).

## Lane R — fine-sheaf GlobalResidue (the critical path)

Source of truth: `docs/planning/S3_FINESHEAF_RES_SCOPING.md` (R1–R8, file
targets, Mathlib decl inventory verified at pin c5ea003). Branch prefix
`feat/keystone-r*`. Rules: **R0 FIRST — the end-to-end `(z−a)⁻¹` sign test**
(top scoping risk: sign/normalization conventions; pin them before anything
builds on R3/R4). **R0 DONE (PR #154): the pinned convention is
`resNormalization := −π⁻¹` against the Lebesgue AREA integral** — i.e.
Forster's `(2πi)⁻¹∬ τ` with `dz∧dz̄ = −2i·dA` absorbed
(`resNormalization = (2πi)⁻¹·(−2i)`); matches the port's `resAt`
(`(z−a)⁻¹ ↦ +1`). R3+ cite `FineResidue.resNormalization`; never re-derive. Then R1 (germ→chart-coefficient (1,1) representation) → R2
(PoU split via `SmoothPartitionOfUnity.exists_isSubordinate` + the port's
`cechPoU`/`rhoC`/`dbarRho`) → R3 (Wirtinger chain rule) → R4 (integral
functional + chart relocation via `integral_image_eq_integral_abs_det_fderiv_smul`)
→ R5 (coboundary Stokes via `integral2_divergence_prod_of_hasFDerivAt`) → R6
(**hardest**: simple-pole ML-tie `Res([δμ]) = Res_a(μ)`, scoped to simple
poles, via the proven `DbarDisk.cauchyPompeiu`) → R7 (descent into
`CousinResidueData` — ZERO interface changes needed) ∥ R8 (nondegeneracy
witness, parallel anytime). State lemmas up-to-germ (germ-choice noise risk).

## Lane L — the two SurjectivityInputs fields

Source: `docs/planning/KEYSTONE_GAP_ANALYSIS.md` S5/S6 + the landed skeleton
`KirovDolbeault/Dolbeault/SerreSurjectivitySkeleton.lean` (fields `psiAct`,
`psiAct_injective`, `unwind`). Branch prefix `feat/keystone-l*`.
- **S6 first (17.8):** construct the ψ-action (multiplication
  `H¹(𝒪_{D−nP}) → H¹(𝒪_D)` dualized) and its injectivity for λ ≠ 0 — key
  input: mult-by-ψ surjective on H¹ via the ITERATED skyscraper LES (all
  proven infra: `exists_skyscraperLES`, `chi_add_single`).
- **S5 (17.7):** the unwind — `ψλ = ι(ω)` with ψ ≠ 0 ⇒ `ω/ψ ∈ L(K−D)`
  (pole-bound regularity) and `ι_D(ω/ψ) = λ`. Consumes S6's action defn.
DT-vet the ψ-action DEFINITION (one query) before S6 lands.

## Lane A — assembly (trails R and L)

S1 datum alignment (M–HS), S2 vanish descent (HS), S4 dz/z witness transport
(HS), S9 genus-0 routing (HS) per KEYSTONE_GAP_ANALYSIS; then inhabit
`SerreDualityData` from {S7 + S5/S6 + R7}, replace the sorry, thread hR
consumers, flip `serreDuality_equiv` + `h1coh_zero_finrank` in
Layer3/Cohomology.lean (Phase-C in-place pattern), ledger 36→34, README,
**comparator run on `riemannRochL3`** (COMPARATOR.md protocol), close
tracker issues.

## Lane X — side quests (Codex-heavy, interleave)

- **#52 PR-4:** diagonal preferred-lifted compat assembly + `chartAt_compat`
  + the Atlas.lean module-placement resolution → discharge
  `PlaneCurve.instIsManifold` (−1 axiom, 2c cluster). Clean-clone Codex.
- **Abel pre-keystone plumbing** (`docs/planning/ABEL_WALL_GAP_ANALYSIS.md`
  A1 + B5): A1 = `div f = (P)−(Q) ⇒ HasSingleSimplePole P` port-side; B5 =
  `lineIntegral` meromorphic extension. Ready so Abel ⊆ assembles the moment
  the keystone falls.

## Milestones

- **M1:** R0 sign test + R1–R2 + S6 underway + #52 PR-4.
- **M2:** R3–R5; S6+S5 done (SurjectivityInputs inhabitable up to residue).
- **M3:** R6–R7 + A-lane S1/S2/S4/S9.
- **M4:** keystone theorem; axiom flips; 34; comparator; reconcile.

Estimate: 6–9 wk human-paced (scoping); 2–4 wk at agent pace. Likeliest
stall: R6.
