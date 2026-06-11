# R6 handoff — the keystone's last hard rung (written under agent degradation)

*2026-06-10 late. Six consecutive subagent stalls (600s stream watchdog,
systemic — even text-only agents died); R6 has NO artifacts yet. This note
captures the exact brief so any session/agent can start cold. Branch
`feat/keystone-r6-mltie` exists (empty, off main @ R5).*

## State

Main = 30 active / 7 challenge-critical. R-ladder R0–R5 merged (#154 #156
#162 #166). S-lane complete: `pairing_surjective_of_globalResidue`
(SerreUnwind.lean) reduces §17.9 to {`G : GlobalResidue 𝔘 K`,
`UnwindRegularity G D`}. R6 = BOTH remaining pieces.

## Deliverable 1 — simple-pole ML-tie (new FineResidue/MLTie.lean)

For the ML cocycle of a single simple pole at `a`, residue `r`, on a cover
with `a` in a single cover set (K-point refinement discipline, see
Glue/OmegaWitness docstrings): `resFunctional` of its glued (1,1) family
`= r`. Route: ContDiffBump cutoff + `DbarDisk.cauchyPompeiu_area` at the
pole; off-pole dies by R5's `resFunctional_eq_zero_of_coboundary`
mechanism (`IsCoboundaryOn` is exactly the off-pole shape). Identify `r`
via `resAt_const_mul_sub_inv`. MANDATORY: end-to-end sign-test lemma
(residue-1 ↦ exactly 1) citing `resNormalization = −π⁻¹` (R0; never
re-derive — `(2πi)⁻¹·(−2i)`, the i/2 trap is documented in SignTest).

## Deliverable 2 — UnwindRegularity discharge (Dolbeault-side per the #159 vet)

`UnwindRegularity G D` (SerreUnwind.lean:275): sections of L(K−E) whose
pairing factors through H¹(E)→H¹(D) lie in L(K−D). Content: residue
evaluation at each point of D−E (the ML-tie applied there) forces the
offending principal part to vanish. The #159 Gemini vet's guidance:
discharge on the DOLBEAULT side (bump-form class + Cauchy-Pompeiu,
cover-independent), NOT pure-Čech (heavy refinement comparison). If the
honest statement needs R7's descent first, write R6_ORDER_NOTE.md
proposing the R6b/R7 interleave — do not fake an interface.

## Then R7 (the prize lap)

liftQ descent via R5's feeder into `CousinResidueData`
(GlobalResidueConstruct.lean:141–182; `vanish_coboundary` field) →
`SerreResidueRealizationAssembly` → replace the keystone sorry
`exists_serreDualityData` → flip `serreDuality_equiv` +
`h1coh_zero_finrank` in Layer3/Cohomology.lean (Phase-C in-place pattern)
→ ledger 30→28 → comparator run on `riemannRochL3`.

## Process notes

Codex reviews every PR (invoke codex:codex-rescue, clean clone). Watchdog
discipline: no full lake builds in agents; per-file lake env lean.
Escalations queued for MRD: draft #165; retroactive #166 fresh review.
