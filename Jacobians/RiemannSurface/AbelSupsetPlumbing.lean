/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.AbelPlumbing
import Jacobians.RiemannSurface.Cohomology.DegreeTheorem

/-!
# Abel ⊇ plumbing (SUP lane, S-block of `docs/planning/SUP_ROUTE.md`)

Toward the discharge of `AX_AbelSupset`
(`PrincipalDivisors X ≤ (abelJacobiDiv X).ker`) on the Liouville /
symmetric-product route (`docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`,
route refresh in `docs/planning/SUP_ROUTE.md`). This file sits BELOW
`Jacobians/Axioms/AbelTheorem.lean` in the import graph (Phase-C in-place
conversion pattern) and does not touch `AX_AbelSupset`.

* **S1 (kernel converse).** `mem_ker_of_divisorPeriodVector_mem_lattice` —
  the converse of A1's `divisorPeriodVector_mem_lattice_of_mem_ker`: a
  degree-0 divisor whose basepoint-arc period vector lies in the period
  lattice is in the Abel–Jacobi kernel. With the degree theorem
  (`deg_divisor_eq_zero`) this reduces `AX_AbelSupset` to the named
  hypothesis `PrincipalPeriodVectorInLattice`
  (`abel_supset_of_principalPeriodVectorInLattice`).

* **S2 (fiber divisor).** `MeromorphicFunctionField.fiberDivisor` — the
  fiber of `toP1 f` over `y : ℙ¹` as a divisor, weighted by the local
  mapping degrees `mapAnalyticOrderAt (toP1 f)` — and the identification
  `divisor_eq_fiberDivisor_zero_sub_infty`:
  `divisor f = fiberDivisor 0 − fiberDivisor ∞` for nonconstant `f`
  (coefficientwise from `toP1_eq_zero_iff` / `toP1_eq_infty_iff` /
  `mapAnalyticOrderAt_toP1*`). This is the divisor side of the Jacobi-map
  evaluation `Φ(0) − Φ(∞) = AJ(div f)` for the fiber Abel–Jacobi map `Φ`.

Conditionality: the same `AX_PeriodCycleBasis` pin as the rest of the
Jacobian layer; no other axioms.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open MeromorphicFunctionField
open Filter OnePoint

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## S1: the kernel converse and the lattice-membership reduction -/

/-- **S1 (kernel converse).** A degree-0 divisor whose basepoint-arc period
vector lies in the period lattice is in the Abel–Jacobi kernel — the
converse of `divisorPeriodVector_mem_lattice_of_mem_ker`, via the A1
factorization `ulift_abelJacobiDiv_apply`. -/
theorem mem_ker_of_divisorPeriodVector_mem_lattice {D : Divisor X}
    (hdeg : D ∈ (Divisor.deg X).ker)
    (hv : divisorPeriodVector (Classical.arbitrary X) D ∈
      periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)) :
    D ∈ (abelJacobiDiv X).ker := by
  have hdeg0 : Divisor.deg X D = 0 := hdeg
  have h1 := ulift_abelJacobiDiv_apply (X := X) D
  rw [hdeg0, zero_zsmul, sub_zero] at h1
  have h0 : (QuotientAddGroup.mk'
      (periodLatticeInBasis X (Classical.arbitrary X)
        (jacobianBasis X)).toAddSubgroup)
      (divisorPeriodVector (Classical.arbitrary X) D) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr hv
  show abelJacobiDiv X D = 0
  refine AddEquiv.ulift.injective ?_
  rw [h1, h0, map_zero]
  rfl

/-- **The S1 target / Liouville-route output.** Every nonzero global
meromorphic function's divisor has its basepoint-arc period vector in the
period lattice: `∑_P ord_P(f) · (∫_{x₀}^{P} ω_i)_i ∈ Λ`. This is the
ambient-space form of `AX_AbelSupset`; the Liouville route (S4–S6 of
`docs/planning/SUP_ROUTE.md`) discharges it. -/
def PrincipalPeriodVectorInLattice (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ f : MeromorphicFunctionField X,
    divisorPeriodVector (Classical.arbitrary X)
        (MeromorphicFunctionField.divisor f) ∈
      periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)

/-- **S1 (reduction).** Over the named lattice-membership hypothesis, the
`AX_AbelSupset` statement holds verbatim: every principal divisor is in the
Abel–Jacobi kernel. Uses the degree theorem (`deg_divisor_eq_zero`) for the
degree-0 hypothesis of the kernel converse. -/
theorem abel_supset_of_principalPeriodVectorInLattice
    (h : PrincipalPeriodVectorInLattice X) :
    PrincipalDivisors X ≤ (abelJacobiDiv X).ker := by
  intro D hD
  rw [PrincipalDivisors] at hD
  rcases hD with ⟨f, hdiv⟩
  have hdivisor : MeromorphicFunctionField.divisor f = D := by
    rw [show MeromorphicFunctionField.divHom f =
        Multiplicative.ofAdd (MeromorphicFunctionField.divisor f) from rfl] at hdiv
    exact Multiplicative.ofAdd.injective hdiv
  have hdeg : D ∈ (Divisor.deg X).ker := by
    show Divisor.deg X D = 0
    rw [← hdivisor]
    exact deg_divisor_eq_zero f
  exact mem_ker_of_divisorPeriodVector_mem_lattice hdeg (hdivisor ▸ h f)

/-! ## S2: the fiber divisor and the zero/pole fiber identification -/

namespace MeromorphicFunctionField

/-- Two divisors with equal coefficients everywhere are equal. -/
theorem divisor_ext {D E : Divisor X}
    (h : ∀ p, FreeAbelianGroup.coeff p D = FreeAbelianGroup.coeff p E) :
    D = E :=
  (FreeAbelianGroup.equivFinsupp X).injective (Finsupp.ext h)

/-- The coefficient of a generator: `coeff p (of q)` is `1` at `q` and `0`
elsewhere. -/
theorem coeff_of (p q : X) :
    FreeAbelianGroup.coeff p (FreeAbelianGroup.of q) =
      Finsupp.single q 1 p := by
  rw [FreeAbelianGroup.coeff, AddMonoidHom.comp_apply,
    FreeAbelianGroup.toFinsupp_of]
  rfl

/-- **S2 (fiber divisor).** The fiber of `toP1 f` over `y : ℙ¹` as a
divisor: each fiber point weighted by its local mapping degree
`mapAnalyticOrderAt (toP1 f)`. For a nonconstant `f` this is the divisor
`f⁻¹(y)` of the pencil member, of constant degree `deg f`
(`toP1_weightedFiberSum_const`). -/
def fiberDivisor (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    (y : ProjectiveLine) : Divisor X :=
  ∑ p ∈ (toP1_fiber_finite hf y).toFinset,
    (mapAnalyticOrderAt (toP1 f) p : ℤ) • FreeAbelianGroup.of p

/-- The fiber-divisor coefficient at a fiber point is the local mapping
degree. -/
theorem coeff_fiberDivisor_of_mem (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) {y : ProjectiveLine} {p : X} (hp : toP1 f p = y) :
    FreeAbelianGroup.coeff p (fiberDivisor f hf y) =
      (mapAnalyticOrderAt (toP1 f) p : ℤ) := by
  classical
  have hmem : p ∈ (toP1_fiber_finite hf y).toFinset := by
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    exact hp
  rw [fiberDivisor, map_sum,
    Finset.sum_eq_single_of_mem p hmem (fun q _ hqp => by
      rw [map_zsmul, coeff_of, Finsupp.single_apply, if_neg hqp, smul_zero]),
    map_zsmul, coeff_of, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
    mul_one]

/-- The fiber-divisor coefficient vanishes off the fiber. -/
theorem coeff_fiberDivisor_of_ne (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) {y : ProjectiveLine} {p : X} (hp : toP1 f p ≠ y) :
    FreeAbelianGroup.coeff p (fiberDivisor f hf y) = 0 := by
  classical
  rw [fiberDivisor, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hqp : q ≠ p := by
    rintro rfl
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hq
    exact hp hq
  rw [map_zsmul, coeff_of, Finsupp.single_apply, if_neg hqp, smul_zero]

/-- **S2 (zero/pole fiber identification).** The divisor of a nonconstant
meromorphic function is the fiber divisor over `0` minus the fiber divisor
over `∞`: zeros with multiplicity minus poles with multiplicity. -/
theorem divisor_eq_fiberDivisor_zero_sub_infty
    (f : MeromorphicFunctionField X) (hf : Nonconstant f) :
    MeromorphicFunctionField.divisor f =
      fiberDivisor f hf (((0 : ℂ) : ProjectiveLine)) -
        fiberDivisor f hf (∞ : ProjectiveLine) := by
  refine divisor_ext fun p => ?_
  rw [map_sub, coeff_divisor f p]
  have hne_top := orderAtMF_ne_top f p
  have hcoe := WithTop.coe_untop₀_of_ne_top hne_top
  rcases lt_trichotomy (orderAtMF p f) 0 with hneg | hzero | hpos
  · -- pole: `toP1 f p = ∞`, not `0`
    have hinfty : toP1 f p = (∞ : ProjectiveLine) :=
      (toP1_eq_infty_iff f p).mpr hneg
    have hnot_zero : toP1 f p ≠ (((0 : ℂ) : ProjectiveLine)) := by
      intro h0
      exact absurd ((toP1_eq_zero_iff f p).mp h0) (not_lt_of_gt hneg)
    rw [coeff_fiberDivisor_of_ne f hf hnot_zero,
      coeff_fiberDivisor_of_mem f hf hinfty, mapAnalyticOrderAt_toP1 f hinfty]
    have hu_neg : (orderAtMF p f).untop₀ < 0 := by
      rw [← hcoe] at hneg
      exact_mod_cast hneg
    omega
  · -- regular nonzero value: neither `0` nor `∞`
    have hnot_zero : toP1 f p ≠ (((0 : ℂ) : ProjectiveLine)) := by
      intro h0
      have := (toP1_eq_zero_iff f p).mp h0
      rw [hzero] at this
      exact lt_irrefl _ this
    have hnot_infty : toP1 f p ≠ (∞ : ProjectiveLine) := by
      intro hinf
      have := (toP1_eq_infty_iff f p).mp hinf
      rw [hzero] at this
      exact lt_irrefl _ this
    rw [coeff_fiberDivisor_of_ne f hf hnot_zero,
      coeff_fiberDivisor_of_ne f hf hnot_infty, hzero]
    simp
  · -- zero: `toP1 f p = 0`, not `∞`
    have hzero' : toP1 f p = (((0 : ℂ) : ProjectiveLine)) :=
      (toP1_eq_zero_iff f p).mpr hpos
    have hnot_infty : toP1 f p ≠ (∞ : ProjectiveLine) := by
      intro hinf
      exact absurd ((toP1_eq_infty_iff f p).mp hinf) (not_lt_of_gt hpos)
    rw [coeff_fiberDivisor_of_mem f hf hzero',
      coeff_fiberDivisor_of_ne f hf hnot_infty,
      mapAnalyticOrderAt_toP1_zero f hzero']
    have hu_pos : 0 < (orderAtMF p f).untop₀ := by
      rw [← hcoe] at hpos
      exact_mod_cast hpos
    omega

end MeromorphicFunctionField

end Jacobians.RiemannSurface
