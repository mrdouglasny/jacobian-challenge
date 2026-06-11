/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Layer3.CechH1Bridge
import Jacobians.Layer3.LinearSystemBridge
import Jacobians.RiemannSurface.Cohomology.RiemannRochBase
import Jacobians.RiemannSurface.Genus
import Jacobians.Bridge.KirovDolbeaultTrace
import KirovDolbeault.Dolbeault.KeystonePackaging
import KirovDolbeault.Dolbeault.ResidueAtom
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Layer-3 flip prep: the two remaining axioms as theorems conditional on the trace residual

L-lane pre-write (docs/planning/FLIP_CHECKLIST.md). Everything between the single
residual analytic input — `CanonicalForm17Data.FrameTraceHypothesis`, needed at
`kirovGenus X = 0` ONLY (`residueAtom_of_genus_split`, PR #194) — and the two remaining
Layer-3 axioms (`Jacobians/Layer3/Cohomology.lean`: `h1coh_zero_finrank`,
`serreDuality_equiv`) is compiled here, so the final flip PR (waiting on the T-lane's
`FrameResidueTrace` construction) is a trivial composition.

## Main statements (all conditional on the genus-split trace residual)

* `h1coh_zero_finrank_of_frameTrace` — the EXACT `h1coh_zero_finrank` statement,
  `Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X`, via
  `finrank H1coh 0 = h1Dim 0` (defeq + `map_zero`) →
  `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace` (port) →
  `kirovGenus = genus` (`bridgeKDFormEquiv`).
* `serreDuality_equiv_exists_of_frameTrace` — the ∃-K form of `serreDuality_equiv`:
  a divisor `K` with `finrank L(K) = genus X` and, for EVERY `D`,
  `Nonempty (H1coh D ≃ₗ[ℂ] Dual ℂ (L(K − D)))`, pinned at the `CechH1Bridge` cover
  `chartDiskCover X`.
* `exists_serreDualityData_cover_of_frameTrace` — the keystone ∃-cover statement from
  the trace residual (the #193 capstone + #194 genus split, one composition).
* `layer3Flip_composition` — the compiled full composition the flip PR will cite.

## The divisor-pin finding (why the ∃-K form, not the axiom verbatim)

`serreDuality_equiv` is stated with `Jacobians.Axioms.canonicalDivisor X` — an OPAQUE
axiom constant (`RiemannSurface/Cohomology/LineBundleBasic.lean:43`) constrained by no
other axiom. No theorem can pin the dimensions of `L(canonicalDivisor X − D)`, so the
axiom's verbatim statement is underivable from ANY analytic input while `canonicalDivisor`
stays opaque. The flip commit therefore ALSO de-opaques `canonicalDivisor`
(axiom → `noncomputable def … := Classical.choose (serreDuality_equiv_exists …)`), after
which the verbatim `serreDuality_equiv` IS `Classical.choose_spec` — compiled here as
`serreDuality_equiv_for_chosen_K`. Net kernel count: −3 (both Layer-3 axioms +
`canonicalDivisor`), not −2. Details: `docs/planning/FLIP_CHECKLIST.md`.

## The cover-pin finding (general-`D` transfer without new machinery)

`H1coh` is pinned to the canonical `chartDiskCover X`, while the #193 capstone exhibits
`SerreDualityData` at its OWN cover (the R-lane separating cover at `g > 0`). The
general-`D` bridge needs no new cover-independence machinery: subtract the PROVEN
cohomological Riemann–Roch (`cohomological_riemannRoch`, Euler form) at the two covers —
the `lDim`/`deg` terms are cover-free, so `h¹_𝔇c(D) − h¹_𝔘(D) = h¹_𝔇c(0) − h¹_𝔘(0)`,
and both `h¹(0)` equal `kirovGenus X` (port `arithmeticGenus` at `𝔘`, the trace-residual
genus identity at `𝔇c`). `ArithmeticGenusTransfer` (D = 0 only) is not needed.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §§16–17.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Module
open Jacobians.RiemannSurface
open Jacobians.Dolbeault

namespace Jacobians.Layer3

/- Name-resolution shim (see `Jacobians/Layer3/CechH1Bridge.lean`): pin the bare names
`Divisor`/`Divisor.deg` in this namespace to our `FreeAbelianGroup` divisor layer. -/
export Jacobians.Axioms (Divisor Divisor.deg)

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-! ### Dictionaries: `H1coh`/`genus`/`riemannRochSpace` vs the port's
`h1Dim`/`kirovGenus`/`lDim` -/

/-- `finrank H1coh D` IS the port's `h1Dim` of the canonical chart-disk cover at the
translated divisor (definitional: `CechH1Bridge`). -/
theorem finrank_H1coh_eq_h1Dim (D : Divisor X) :
    Module.finrank ℂ (H1coh D) =
      (chartDiskCover (X := X)).toFiniteCover.h1Dim
        (FreeAbelianGroup.equivFinsupp X D) := rfl

/-- At `D = 0` the translated divisor is `0` (`map_zero`), so `finrank H1coh 0` is the
canonical cover's arithmetic-genus dimension `h1Dim 0` — the S-lane normal form. -/
theorem finrank_H1coh_zero_eq_h1Dim_zero :
    Module.finrank ℂ (H1coh (0 : Divisor X)) =
      (chartDiskCover (X := X)).toFiniteCover.h1Dim 0 := by
  rw [finrank_H1coh_eq_h1Dim, map_zero]

/-- Our cocycle-form genus is the port's bundle-section genus, via the composite form
bridge `Jacobians.Bridge.bridgeKDFormEquiv`. -/
theorem genus_eq_kirovGenus : genus X = kirovGenus X :=
  (Jacobians.Bridge.bridgeKDFormEquiv (X := X)).finrank_eq

/-- The port's junk-free linear-system dimension at the translated divisor is the
finrank of our Riemann–Roch space (the `LinearSystemBridge` subquotient shuffle). -/
theorem lDim_equivFinsupp (D : Divisor X) :
    Jacobians.lDim (X := X) (FreeAbelianGroup.equivFinsupp X D) =
      Module.finrank ℂ (riemannRochSpace D) :=
  (linearSystemQuotEquivRiemannRoch D).finrank_eq

/-! ### Flip target 1: `h1coh_zero_finrank`, conditional on the trace residual -/

/-- **Flip target 1 (genus-split residual).** The EXACT statement of the Layer-3 axiom
`h1coh_zero_finrank`, conditional on the trace residual in the `kirovGenus X = 0` case
only: `h¹(𝒪_X) = genus X` at the `CechH1Bridge` cover pin. -/
theorem h1coh_zero_finrank_of_frameTrace
    (h0 : kirovGenus X = 0 →
      ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X := by
  rw [finrank_H1coh_zero_eq_h1Dim_zero,
    h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace h0, genus_eq_kirovGenus]

/-- Single-datum form of flip target 1: any canonical §17 datum satisfying its trace
hypothesis (e.g. the canonical `ω₀ = df` datum of the T-lane work order). -/
theorem h1coh_zero_finrank_of_frameTrace' (data : CanonicalForm17Data X)
    (h : data.FrameTraceHypothesis) :
    Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X :=
  h1coh_zero_finrank_of_frameTrace fun _ => ⟨data, h⟩

/-! ### The keystone ∃-cover statement, conditional on the trace residual -/

/-- **The keystone ∃-cover statement from the trace residual** — the #193 capstone
(`exists_serreDualityData_cover_of_genus_split_residueAtom`) composed with the #194
genus-split atom (`exists_residueAtom_of_exists_frameTrace`; at `g > 0` the atom is a
theorem, no residual needed). This is the exact statement replacing the keystone sorry
(`SerreDualityPairing.lean:131`) in the flip. -/
theorem exists_serreDualityData_cover_of_frameTrace
    (h0 : kirovGenus X = 0 →
      ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_cover_of_genus_split_residueAtom
    fun hg => exists_residueAtom_of_exists_frameTrace (h0 hg)

/-! ### Flip target 2: `serreDuality_equiv` in ∃-K form, conditional on the residual -/

/-- **Flip target 2 (∃-K form).** Serre duality at the `CechH1Bridge` cover pin: a
divisor `K` with `dim L(K) = genus X` such that for EVERY divisor `D`,
`H1coh D ≃ₗ[ℂ] Dual ℂ (L(K − D))`. This is the strongest form derivable while
`canonicalDivisor` is opaque (see the module docstring); the flip de-opaques
`canonicalDivisor := Classical.choose` of this statement, making the verbatim
`serreDuality_equiv` its `choose_spec` (`serreDuality_equiv_for_chosen_K` below).

Cover transfer (general `D`): subtract the proven Euler-form Riemann–Roch
(`cohomological_riemannRoch`) at the capstone's cover and at the canonical cover; the
`h¹(0)` base dimensions agree (= `kirovGenus X`) by the port `arithmeticGenus` and the
trace-residual genus identity respectively. -/
theorem serreDuality_equiv_exists_of_frameTrace
    (h0 : kirovGenus X = 0 →
      ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    ∃ K : Divisor X,
      Module.finrank ℂ (riemannRochSpace K) = genus X ∧
      ∀ D : Divisor X,
        Nonempty (H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D))) := by
  classical
  -- the capstone's Serre-duality data at its own (Leray, realizable) cover
  obtain ⟨𝔘, hL, hR, ⟨data⟩⟩ := exists_serreDualityData_cover_of_frameTrace h0
  -- pull the port-side canonical divisor back across the divisor translation
  refine ⟨(FreeAbelianGroup.equivFinsupp X).symm data.K, ?_, fun D => ?_⟩
  · -- `dim L(K) = genus`: `lDim data.K = kirovGenus` is the datum's 17.4 field
    have h2 := lDim_equivFinsupp (X := X)
      ((FreeAbelianGroup.equivFinsupp X).symm data.K)
    rw [AddEquiv.apply_symm_apply] at h2
    rw [← h2, data.hKgenus, genus_eq_kirovGenus]
  · -- divisor translation: `equivFinsupp (K − D) = data.K − equivFinsupp D`
    have htrans : FreeAbelianGroup.equivFinsupp X
          ((FreeAbelianGroup.equivFinsupp X).symm data.K - D)
        = data.K - FreeAbelianGroup.equivFinsupp X D := by
      rw [map_sub, AddEquiv.apply_symm_apply]
    -- the two Euler-form Riemann–Rochs at the translated divisor
    have hccan := cohomological_riemannRoch (chartDiskCover (X := X)).toFiniteCover
      (ChartDiskCover.locallyRealizable _) (FreeAbelianGroup.equivFinsupp X D)
    have hcdat := cohomological_riemannRoch 𝔘 hR (FreeAbelianGroup.equivFinsupp X D)
    rw [(chartDiskCover (X := X)).toFiniteCover.h0Dim_eq_lDim] at hccan
    rw [𝔘.h0Dim_eq_lDim] at hcdat
    -- Serre duality at the capstone cover, both `h¹(0)` base dimensions
    have hserre := data.serre_eq (FreeAbelianGroup.equivFinsupp X D)
    have hag := data.arithmeticGenus
    have hcg := h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace h0
    -- the canonical-cover `h¹(D)` equals the port `lDim (data.K − E)`
    have hkey : (chartDiskCover (X := X)).toFiniteCover.h1Dim
          (FreeAbelianGroup.equivFinsupp X D)
        = Jacobians.lDim (X := X)
            (data.K - FreeAbelianGroup.equivFinsupp X D) := by
      omega
    -- assemble the dimension identity on our side of the bridge
    have hdim : Module.finrank ℂ (H1coh D)
        = Module.finrank ℂ
            (riemannRochSpace
              ((FreeAbelianGroup.equivFinsupp X).symm data.K - D)) := by
      rw [finrank_H1coh_eq_h1Dim, hkey, ← htrans, lDim_equivFinsupp]
    -- finite-dimensional spaces of equal dimension are linearly equivalent
    have hdual : Module.finrank ℂ
          (Module.Dual ℂ
            (riemannRochSpace
              ((FreeAbelianGroup.equivFinsupp X).symm data.K - D)))
        = Module.finrank ℂ
            (riemannRochSpace
              ((FreeAbelianGroup.equivFinsupp X).symm data.K - D)) :=
      Subspace.dual_finrank_eq
    exact ⟨LinearEquiv.ofFinrankEq _ _ (hdim.trans hdual.symm)⟩

/-- Single-datum form of flip target 2. -/
theorem serreDuality_equiv_exists_of_frameTrace' (data : CanonicalForm17Data X)
    (h : data.FrameTraceHypothesis) :
    ∃ K : Divisor X,
      Module.finrank ℂ (riemannRochSpace K) = genus X ∧
      ∀ D : Divisor X,
        Nonempty (H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D))) :=
  serreDuality_equiv_exists_of_frameTrace fun _ => ⟨data, h⟩

/-- **The flip endgame, compiled.** Once the residual is a theorem, the flip de-opaques
`canonicalDivisor X := Classical.choose (serreDuality_equiv_exists_of_frameTrace …)`;
this lemma is then VERBATIM the `serreDuality_equiv` axiom statement (`choose_spec`),
and the `.1` component re-proves `h0_canonical_L3` directly. -/
theorem serreDuality_equiv_for_chosen_K
    (h0 : kirovGenus X = 0 →
      ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis)
    (D : Divisor X) :
    Nonempty (H1coh D ≃ₗ[ℂ]
      Module.Dual ℂ (riemannRochSpace
        (Classical.choose (serreDuality_equiv_exists_of_frameTrace h0) - D))) :=
  (Classical.choose_spec (serreDuality_equiv_exists_of_frameTrace h0)).2 D

/-! ### The full composition the flip PR cites -/

/-- **The compiled full composition** — the exact lemma set of the flip PR: from the
genus-split trace residual alone, (i) the verbatim `h1coh_zero_finrank` statement,
(ii) the ∃-K `serreDuality_equiv` statement, (iii) the keystone ∃-cover statement. -/
theorem layer3Flip_composition
    (h0 : kirovGenus X = 0 →
      ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis) :
    (Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X) ∧
    (∃ K : Divisor X,
      Module.finrank ℂ (riemannRochSpace K) = genus X ∧
      ∀ D : Divisor X,
        Nonempty (H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D)))) ∧
    (∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘)) :=
  ⟨h1coh_zero_finrank_of_frameTrace h0,
   serreDuality_equiv_exists_of_frameTrace h0,
   exists_serreDualityData_cover_of_frameTrace h0⟩

/-- Single-datum form of the full composition (the shape the T-lane hands over: the
canonical `ω₀ = df` datum satisfying its trace hypothesis). -/
theorem layer3Flip_composition' (data : CanonicalForm17Data X)
    (h : data.FrameTraceHypothesis) :
    (Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X) ∧
    (∃ K : Divisor X,
      Module.finrank ℂ (riemannRochSpace K) = genus X ∧
      ∀ D : Divisor X,
        Nonempty (H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D)))) ∧
    (∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘)) :=
  layer3Flip_composition fun _ => ⟨data, h⟩

end Jacobians.Layer3
