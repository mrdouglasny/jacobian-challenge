/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The H₁ basis of the elliptic curve from `π₁(ℂ ⧸ Λ) ≅ Λ`

This file discharges the topological half of the g = 1 period-cycle-basis
witness (formerly the content of `AX_Elliptic_H1_symplectic`):

* `ellipticH1Equiv : H1 (Elliptic ω₁ ω₂ h) 0 ≃+ Λ` — the covering-space
  computation of first homology, specialized from
  `Jacobians.RiemannSurface.h1EquivLattice` (`QuotientCoveringPi1.lean`).
* The Hurewicz classes of the concrete loops compute to lattice elements:
  `aLoop ↦ ω₁`, `bLoop ↦ ω₂`, `bLoopRev ↦ −ω₂` (the lifts are the literal
  straight-line paths `t ↦ t·ω₁` etc.).
* `ellipticH1Basis` — the ℤ-basis of `H1 (Elliptic) 0` obtained by
  transporting the lattice basis `{ω₁, ±ω₂}` (oriented as in
  `orientedPeriod`), with `ellipticH1Basis_eq_loops` aligning it with the
  oriented loop family `ellipticLoops`.
* `ellipticPeriodCycleBasis : PeriodCycleBasis (Elliptic ω₁ ω₂ h) 0` — the
  **fully unconditional** g = 1 witness, feeding the H₁ data into the
  boundary-word datum `ellipticPeriodCycleBasisOfH1`
  (`BoundaryWordElliptic.lean`), whose Hodge fields R1/R2 are already
  proven. `nonempty_periodCycleBasis_elliptic` packages it.

No axioms are used anywhere in this file.
-/
import Jacobians.RiemannSurface.QuotientCoveringPi1
import Jacobians.RiemannSurface.BoundaryWordElliptic

namespace Jacobians.ProjectiveCurve

set_option linter.unusedSectionVars false

open Jacobians.RiemannSurface Jacobians.Axioms
open Jacobians.RiemannSurface.BoundaryWordElliptic

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

/-- The lattice of an elliptic curve, as an `AddSubgroup` of `ℂ` (the form
consumed by the covering-space machinery). -/
noncomputable abbrev ellipticAddLattice : AddSubgroup ℂ :=
  (ellipticLattice ω₁ ω₂ h).toAddSubgroup

instance : DiscreteTopology (ellipticAddLattice ω₁ ω₂ h) :=
  (inferInstance : DiscreteTopology (ellipticLattice ω₁ ω₂ h))

/-- `ω₁` generates the first lattice direction. -/
theorem omega₁_mem_ellipticLattice : ω₁ ∈ ellipticLattice ω₁ ω₂ h :=
  Submodule.subset_span ⟨0, by simp [ellipticRealBasis]⟩

/-- `ω₂` generates the second lattice direction. -/
theorem omega₂_mem_ellipticLattice : ω₂ ∈ ellipticLattice ω₁ ω₂ h :=
  Submodule.subset_span ⟨1, by simp [ellipticRealBasis]⟩

/-- **`H₁(Elliptic, ℤ) ≅ Λ`**: first homology of the elliptic curve is the
period lattice, by lifting loops through the covering `ℂ → ℂ ⧸ Λ`. -/
noncomputable def ellipticH1Equiv :
    H1 (Elliptic ω₁ ω₂ h) (0 : Elliptic ω₁ ω₂ h) ≃+ ellipticAddLattice ω₁ ω₂ h :=
  h1EquivLattice (ellipticAddLattice ω₁ ω₂ h)

/-- Compute `ellipticH1Equiv` on the Hurewicz class of a concrete loop from
an explicit lift through the covering. -/
theorem ellipticH1Equiv_loopToHomology (loop : AnalyticLoop (Elliptic ω₁ ω₂ h) 0)
    (z : ℂ) (hz : z ∈ ellipticAddLattice ω₁ ω₂ h)
    (Γ : unitInterval → ℂ) (hΓ : Continuous Γ) (hΓ0 : Γ 0 = 0) (hΓ1 : Γ 1 = z)
    (hlift : ∀ t, QuotientAddGroup.mk' (ellipticAddLattice ω₁ ω₂ h) (Γ t)
      = loopToPath (X := Elliptic ω₁ ω₂ h) loop t) :
    ellipticH1Equiv ω₁ ω₂ h (loopToHomology loop) = ⟨z, hz⟩ := by
  have hend : pathLiftEnd (ellipticAddLattice ω₁ ω₂ h) (loopToPath (X := Elliptic ω₁ ω₂ h) loop) = z := by
    rw [pathLiftEnd_eq (ellipticAddLattice ω₁ ω₂ h) (loopToPath (X := Elliptic ω₁ ω₂ h) loop) Γ hΓ hΓ0 hlift,
      hΓ1]
  have hcls := h1EquivLattice_loopClass (ellipticAddLattice ω₁ ω₂ h) (loopToPath (X := Elliptic ω₁ ω₂ h) loop)
  show h1EquivLattice (ellipticAddLattice ω₁ ω₂ h) (Additive.ofMul (Abelianization.of
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopToPath (X := Elliptic ω₁ ω₂ h) loop))))) = ⟨z, hz⟩
  rw [hcls]
  exact Subtype.ext hend

/-- The A-cycle class is `ω₁`: its lift is the straight line `t ↦ t·ω₁`. -/
theorem ellipticH1Equiv_aLoop :
    ellipticH1Equiv ω₁ ω₂ h (loopToHomology (aLoop ω₁ ω₂ h))
      = ⟨ω₁, omega₁_mem_ellipticLattice ω₁ ω₂ h⟩ := by
  refine ellipticH1Equiv_loopToHomology ω₁ ω₂ h (aLoop ω₁ ω₂ h) ω₁ _
    (fun t => ((t : ℝ) : ℂ) * ω₁)
    ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    (by simp) (by simp) (fun t => rfl)

/-- The B-cycle class is `ω₂`. -/
theorem ellipticH1Equiv_bLoop :
    ellipticH1Equiv ω₁ ω₂ h (loopToHomology (bLoop ω₁ ω₂ h))
      = ⟨ω₂, omega₂_mem_ellipticLattice ω₁ ω₂ h⟩ := by
  refine ellipticH1Equiv_loopToHomology ω₁ ω₂ h (bLoop ω₁ ω₂ h) ω₂ _
    (fun t => ((t : ℝ) : ℂ) * ω₂)
    ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    (by simp) (by simp) (fun t => rfl)

/-- The reversed B-cycle class is `−ω₂`: its lift from `0` is
`t ↦ (1−t)·ω₂ − ω₂`. -/
theorem ellipticH1Equiv_bLoopRev :
    ellipticH1Equiv ω₁ ω₂ h (loopToHomology (bLoopRev ω₁ ω₂ h))
      = ⟨-ω₂, neg_mem (omega₂_mem_ellipticLattice ω₁ ω₂ h)⟩ := by
  refine ellipticH1Equiv_loopToHomology ω₁ ω₂ h (bLoopRev ω₁ ω₂ h) (-ω₂) _
    (fun t => ((1 - (t : ℝ) : ℝ) : ℂ) * ω₂ - ω₂)
    (((Complex.continuous_ofReal.comp (continuous_const.sub
      continuous_subtype_val)).mul continuous_const).sub continuous_const)
    (by simp) (by simp) ?_
  intro t
  have hω₂0 : QuotientAddGroup.mk' (ellipticAddLattice ω₁ ω₂ h) ω₂ = 0 := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact omega₂_mem_ellipticLattice ω₁ ω₂ h
  show QuotientAddGroup.mk' (ellipticAddLattice ω₁ ω₂ h)
      (((1 - (t : ℝ) : ℝ) : ℂ) * ω₂ - ω₂) = loopToPath (bLoopRev ω₁ ω₂ h) t
  rw [map_sub, hω₂0, sub_zero]
  rfl

/-! ### The lattice ℤ-basis, oriented to match `ellipticLoops` -/

/-- The standard ℤ-basis `{ω₁, ω₂}` of the elliptic lattice. -/
noncomputable def ellipticLatticeBasis :
    Module.Basis (Fin 2) ℤ (ellipticLattice ω₁ ω₂ h) :=
  (ellipticRealBasis ω₁ ω₂ h).restrictScalars ℤ

theorem ellipticLatticeBasis_coe (i : Fin 2) :
    (ellipticLatticeBasis ω₁ ω₂ h i : ℂ) = ![ω₁, ω₂] i := by
  rw [ellipticLatticeBasis, Module.Basis.restrictScalars_apply]
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

/-- The oriented ℤ-basis `{ω₁, ±ω₂}` of the elliptic lattice: the second
vector is `orientedPeriod ω₁ ω₂`, matching the orientation normalization of
`ellipticLoops`. -/
noncomputable def ellipticOrientedLatticeBasis :
    Module.Basis (Fin 2) ℤ (ellipticLattice ω₁ ω₂ h) :=
  (ellipticLatticeBasis ω₁ ω₂ h).unitsSMul
    ![1, if 0 < (ω₂ * (starRingEnd ℂ) ω₁).im then 1 else -1]

theorem ellipticOrientedLatticeBasis_coe_zero :
    (ellipticOrientedLatticeBasis ω₁ ω₂ h 0 : ℂ) = ω₁ := by
  rw [ellipticOrientedLatticeBasis, Module.Basis.unitsSMul_apply]
  simp [ellipticLatticeBasis_coe]

theorem ellipticOrientedLatticeBasis_coe_one :
    (ellipticOrientedLatticeBasis ω₁ ω₂ h 1 : ℂ) = orientedPeriod ω₁ ω₂ := by
  rw [ellipticOrientedLatticeBasis, Module.Basis.unitsSMul_apply, orientedPeriod]
  split_ifs with hpos <;>
    simp [ellipticLatticeBasis_coe, Units.smul_def]

/-! ### The H₁ basis and its alignment with the oriented loops -/

/-- The lattice-to-homology ℤ-linear equivalence. -/
noncomputable def ellipticLatticeToH1 :
    (ellipticLattice ω₁ ω₂ h) ≃ₗ[ℤ] H1 (Elliptic ω₁ ω₂ h) (0 : Elliptic ω₁ ω₂ h) :=
  AddEquiv.toIntLinearEquiv (ellipticH1Equiv ω₁ ω₂ h).symm

/-- **The ℤ-basis of `H₁(Elliptic, ℤ)`** transported from the oriented
lattice basis (rank `2 = 2·g` at `g = 1`). -/
noncomputable def ellipticH1Basis :
    Module.Basis (Fin (2 * genus (Elliptic ω₁ ω₂ h))) ℤ
      (H1 (Elliptic ω₁ ω₂ h) (0 : Elliptic ω₁ ω₂ h)) :=
  ((ellipticOrientedLatticeBasis ω₁ ω₂ h).map (ellipticLatticeToH1 ω₁ ω₂ h)).reindex
    (finCongr (by rw [genus_Elliptic_eq_one ω₁ ω₂ h]))

/-- The transported basis vectors are exactly the Hurewicz classes of the
oriented elliptic loops. -/
theorem ellipticH1Basis_eq_loops (i : Fin (2 * genus (Elliptic ω₁ ω₂ h))) :
    ellipticH1Basis ω₁ ω₂ h i = loopToHomology (ellipticLoops ω₁ ω₂ h i) := by
  rw [ellipticH1Basis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  have hval : (((finCongr (by rw [genus_Elliptic_eq_one ω₁ ω₂ h] :
      2 = 2 * genus (Elliptic ω₁ ω₂ h))).symm i : Fin 2) : ℕ) = (i : ℕ) := rfl
  by_cases hi : (i : ℕ) = 0
  · -- A-slot
    have hj : (finCongr (by rw [genus_Elliptic_eq_one ω₁ ω₂ h] :
        2 = 2 * genus (Elliptic ω₁ ω₂ h))).symm i = (0 : Fin 2) := by
      apply Fin.ext
      rw [hval, hi]
      rfl
    rw [hj, show ellipticLoops ω₁ ω₂ h i = aLoop ω₁ ω₂ h by
      simp [ellipticLoops, hi]]
    have hb : ellipticOrientedLatticeBasis ω₁ ω₂ h 0
        = ⟨ω₁, omega₁_mem_ellipticLattice ω₁ ω₂ h⟩ :=
      Subtype.ext (ellipticOrientedLatticeBasis_coe_zero ω₁ ω₂ h)
    rw [hb]
    show (ellipticH1Equiv ω₁ ω₂ h).symm _ = _
    rw [← ellipticH1Equiv_aLoop ω₁ ω₂ h, AddEquiv.symm_apply_apply]
  · -- B-slot
    have hj : (finCongr (by rw [genus_Elliptic_eq_one ω₁ ω₂ h] :
        2 = 2 * genus (Elliptic ω₁ ω₂ h))).symm i = (1 : Fin 2) := by
      apply Fin.ext
      rw [hval]
      have h2 : (i : ℕ) < 2 := by
        simpa [genus_Elliptic_eq_one ω₁ ω₂ h] using i.isLt
      simp only [Fin.val_one]
      omega
    rw [hj, show ellipticLoops ω₁ ω₂ h i
        = (if 0 < (ω₂ * (starRingEnd ℂ) ω₁).im then bLoop ω₁ ω₂ h
            else bLoopRev ω₁ ω₂ h) by
      simp [ellipticLoops, hi]]
    show (ellipticH1Equiv ω₁ ω₂ h).symm (ellipticOrientedLatticeBasis ω₁ ω₂ h 1) = _
    rw [AddEquiv.symm_apply_eq]
    split_ifs with hpos
    · rw [ellipticH1Equiv_bLoop ω₁ ω₂ h]
      refine Subtype.ext ?_
      rw [ellipticOrientedLatticeBasis_coe_one]
      unfold orientedPeriod
      rw [if_pos hpos]
    · rw [ellipticH1Equiv_bLoopRev ω₁ ω₂ h]
      refine Subtype.ext ?_
      rw [ellipticOrientedLatticeBasis_coe_one]
      unfold orientedPeriod
      rw [if_neg hpos]

/-! ### The unconditional g = 1 witness -/

/-- **The fully unconditional `PeriodCycleBasis` witness for the elliptic
curve**: the H₁ topology fields come from the covering-space computation
above, the Hodge fields R1/R2 from the boundary-word datum
(`ellipticArcBoundaryWordData`). No axiom is involved. -/
noncomputable def ellipticPeriodCycleBasis :
    PeriodCycleBasis (Elliptic ω₁ ω₂ h) 0 :=
  ellipticPeriodCycleBasisOfH1 ω₁ ω₂ h (ellipticH1Basis ω₁ ω₂ h)
    (ellipticH1Basis_eq_loops ω₁ ω₂ h)

/-- The g = 1 instantiation of the period-cycle-basis content, axiom-free. -/
theorem nonempty_periodCycleBasis_elliptic :
    Nonempty (PeriodCycleBasis (Elliptic ω₁ ω₂ h) 0) :=
  ⟨ellipticPeriodCycleBasis ω₁ ω₂ h⟩

end Jacobians.ProjectiveCurve
