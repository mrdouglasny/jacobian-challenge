# P9 — the g=1 ArcBoundaryWordData witness: construction plan

Date: 2026-06-12. Handover UPDATE 4 P9; companion to `BW_ROUTE.md`.
Target file: `Jacobians/RiemannSurface/BoundaryWordElliptic.lean` (new;
`BilinearRelationsBoundaryWord.lean` is read-only).

## The datum at g = 1 collapses to two explicit integrals

Fix `X := Elliptic ω₁ ω₂ h`, basepoint `0`, loops `(aLoop, bLoop)` (possibly
`bLoop.reverse` — orientation, below), and `cω :=` the singleton basis on
`ellipticDz` (`eq_smul_ellipticDz` gives `finrank = 1`; build via
`basisOfLinearIndependent` or `Basis.mk` on `ellipticDz_ne_zero`).

Field choices (all explicit):
* `h₀ := fun _ => c` (constant), `F₀ := fun z => c * z`, `U := Set.univ`;
  `hbox`/`hh`/`hF` are trivial/elementary (`hasDerivAt_const`,
  `(hasDerivAt_id _).const_mul`).
* **word_R1** (1×1): LHS `= ω₁ω₂ − ω₂ω₁ = 0` by `mul_comm` (the matrices are
  1×1 — `arc_R1_of_genus_le_one`'s observation); RHS
  `rectBoundaryIntegral (fun z => F₀ z * h₀ z) = ∮ c²·z dz = 0` — either by
  the ladder's `rectBoundaryIntegral_eq_zero_of_…` Cauchy lemma applied to
  the entire function `c²z`, or by direct evaluation of the four interval
  integrals.
* **word_R2** (1×1): LHS `= ω₁·conj ω₂ − ω₂·conj ω₁ = 2i·Im(ω₁ conj ω₂)`;
  RHS `= −boundaryForm h₀ F₀ = −|c|²·∮_{∂[0,1]²} conj z dz = −|c|²·2i`
  (the classic area integral — four explicit interval integrals).  Match:
  choose `c := Real.sqrt (Im (ω₂ * conj ω₁))` when that Im is positive,
  else use the reversed `bLoop` (the loops are the witness's choice; the
  arc-B-period of `bLoop.reverse` is `−ω₂` by `canonicalArcIntegral_reverse`,
  flipping the sign of LHS).  `Im(conj ω₁ · ω₂) ≠ 0` from the
  `LinearIndependent ℝ ![ω₁, ω₂]` hypothesis (standard determinant form).
* **nondeg**: `∑ v_j · h₀ = v₀ · c`, nonzero for `v ≠ 0` since `c ≠ 0` —
  pick any interior point.
* Period matrix entries: `arcAPeriodMatrix = (ω₁)`, `arcBPeriodMatrix = (ω₂)`
  (or `−ω₂`) via `aLoop_period_eq` / `bLoop_period_eq` + the `cω`-basis
  unfolding (basis vector = `ellipticDz` definitionally via `Basis.mk`).

## What it buys

`ellipticSquare_arcBoundaryWordData : ArcBoundaryWordData (elliptic loops) cω`
feeds `periodMatrix_symm`/`periodGram_posDef` (port engines) and the TD-lane
`discreteTopology_of_arcBoundaryWordData` — making the entire
`AX_PeriodCycleBasis` analytic chain CONCRETE at g=1, with only the H₁
fields (`isBasis`/`loops_to_basis`, the `AX_Elliptic_H1_symplectic` residue)
remaining for the full witness.

## Order of work

1. Read `rectBoundaryIntegral` / `boundaryForm` / `wCLM` definitions
   (port-side, read-only) — the exact 4-interval shape drives step 2.
2. The two boundary integrals as standalone lemmas
   (`rectBoundary_self_deriv_zero`, `rectBoundary_conj_eq_two_I` —
   upstreamable).
3. The `cω` basis + period-entry lemmas.
4. Orientation normalization + assembly of the structure literal.
5. Kernel-check: the datum itself should be standard-3 (loops' analyticity
   is theorem-grade per `Witnesses.lean`; NO `AX_Elliptic_H1_symplectic`).
