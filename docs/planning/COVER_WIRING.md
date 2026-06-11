# Cover-wiring verdict (final-lane probe, 2026-06-11)

*Recovered from the lane-B agent's completed in-memory analysis (agent killed
by the disk-full incident before saving; verdict preserved from its report).*

## VERDICT

**The keystone's consumers all CHOOSE their own cover — `exists_serreDualityData`
can be honestly weakened to ∃-cover form. No refinement-invariance lemma is
needed for the port's ladder.** The only genuinely pinned consumers are our
repo's Layer-3 bridges (`H1coh` at the canonical `chartDiskCover`), best
resolved by re-pinning the bridge at the chosen cover (sanctioned by
`H1coh`'s "cover choice never leaks" docstring), NOT by Leray refinement
invariance — whose surjectivity half (`RefinementLift`) is genuinely open
(proven suppliers degenerate to H¹(fine)=0, false at g ≥ 1; injectivity IS
proven: `refineH1_injective_unconditional`, CechRefinementInjective.lean:386).

## Instantiation census

- SerreDualityPairing.lean:131 keystone sorry → consumed only by the two
  parametric pass-throughs (:140/:147).
- DolbeaultLadder.lean:56-87: parametric; all four non-keystone legs
  cover-generic and proven, at the SAME 𝔘.
- **RiemannRoch.lean:60-68 — the unique top-level consumer, and it CHOOSES
  the cover** (obtain ⟨𝔘,hL,hR⟩ := exists_realizableLerayCover); its own
  statement is cover-free. SerreOmega0.lean:135, RiemannRoch.lean:155 same.
- **The weakening**: keystone → `∃ 𝔘 (_ : IsLeray) (_ : LocallyRealizable),
  Nonempty (SerreDualityData 𝔘)` + one-line edit at RiemannRoch.lean:66;
  land in the SAME commit as the witness (sorry 1→0 atomically).
- Pinned our-side consumers: Layer3/CechH1Bridge.lean:64-66,
  CohomologyLESBridge.lean:145-149, LinearSystemBridge.lean:275-340, and the
  two remaining Layer-3 axioms — only cover-specific ingredient is
  `hR := locallyRealizable_chartDiskCover`; re-pin = bounded mechanical
  edit. Genus-0 branch keeps chartDiskCover (no ω₀ needed).
- Mitigation worth taking: build the separating cover AS a refinement of
  chartDiskCover (free in the construction) so proven refinement INJECTIVITY
  gives `finrank H1coh 0 ≤ kirovGenus` at the canonical cover.

## The reserved-disk trick (kills the fixed-cover ∀D worry)

SerreDualityData needs ι data for ALL D on ONE cover; one **reserved
privately-covered open disk** serves every (D, v) in CupMLWitnessR (the bad
set inside it is finite ∪ discrete; the slot is analytic, ≠ 0 at g ≥ 1).
Build the reserved disk into the SeparatesPoles cover construction — the
CupMLWitnessR construction and the cover construction are THE SAME work item.

## Bill of materials for exhibiting OUR cover

1. `exists_separatingChartDiskCover` — NEW, ~200-400 LOC (ingredients:
   ChartDiskRefinement.lean:52-183), WITH the reserved disk built in.
2. Generic `ChartDiskCover.isLeray` from simplyConnectedSpace_chartBallPreimage
   (LerayCoverExists.lean:88), ~40-80 LOC.
3. Generalize `locallyRealizable_chartDiskCover`
   (SkyscraperProductWitness.lean:185-243) to any ChartDiskCover —
   chart-generic proof, ~100 LOC.
4. SerreDualityData via the PROVEN chain CousinResidueData → toGlobalResidue
   → toSerreDualityData (GlobalResidueConstruct.lean:208). Remaining genuine
   walls unchanged: CupMLWitnessR (= the reserved disk of item 1) and
   UnwindRegularity (lane A).

## SlotMatchesK implementation plan (verified against sources, ~1-2h)

`slotMatchesK_omegaCoeff (𝔇) (α) (hK : ∀ x, (holToMero α).formOrderW x = K x)`:
chain formCoeff_holToSection (MeromorphicOneFormSystem.lean:356) +
formOrderW_chart_invariant (CanonicalFormDifferential.lean:416) +
coeffAt_analyticAt + the Mathlib analytic-order factorization, with
Int.toNat_of_nonneg; match exists_form_divisor's output shape
(CanonicalFormDifferential.lean:521).
