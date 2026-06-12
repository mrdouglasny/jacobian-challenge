/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Axioms.AbelJacobiDivDef
import Jacobians.RiemannSurface.MeromorphicFunctionField

/-!
# Abel ⊆ root-side plumbing (A-block of `docs/planning/AB_ROUTE.md`)

Engine-agnostic assembly for the ⊆ direction of `AX_AbelTheorem`
(`(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker ≤ PrincipalDivisors X`),
written against a NAMED ENGINE HYPOTHESIS — the Forster §20 weak-solution
output (`E5`-shape, `exists_meromorphic_of_oneChain`) is in flight on the
primary account's port-side lane; nothing here imports it.

* **A1 (kernel unfolding)** — `abelJacobiDiv_eq_comp` factors the
  Abel–Jacobi divisor map through the explicit ambient lift, so kernel
  membership of a degree-0 divisor unfolds to period-lattice membership of
  its basepoint-arc period vector
  (`divisorPeriodVector_mem_lattice_of_mem_ker`), and lattice membership
  expands over the pinned cycle basis into a ℤ-combination of the pinned
  loops (`hasZeroPeriodLoopPresentation_of_mem_ker`). The chain shape
  "basepoint arcs − ℤ-combination of pinned loops, all `jacobianBasis`
  periods zero" is exactly `HasZeroPeriodLoopPresentation`.

  *Conditionality flag (audit-row note per AB_ROUTE A1):* the expansion is
  relative to the `AX_PeriodCycleBasis` pin — its `loops_to_basis`
  completeness field — the same conditionality as the rest of the Jacobian
  layer. Every `Classical.choice (AX_PeriodCycleBasis x₀)` term is
  definitionally the SAME witness (proof irrelevance on the `Nonempty`
  argument), so the loops here are the ones already inside
  `loopIntegralToH1` / `periodMapInBasis`.

* **A2 (divisor bridge)** — fused into A1's output shape: the data the
  engine consumes (arcs weighted by `D`, pinned loops, vanishing periods)
  is stated fully root-side, so the port↔root divisor faithfulness is part
  of the ENGINE's obligation when it discharges
  `ZeroPeriodChainSolvability`, not a separate root-side rung.

* **A3 (assembly)** — `abel_subset_of_engine`: the named hypothesis
  `ZeroPeriodChainSolvability` (degree-0 + zero-period presentation ⟹
  principal) yields the verbatim ⊆ inclusion. `AX_AbelTheorem` is not
  imported here (this file sits BELOW the theorem in the import graph
  since the 2026-06-12 split-flip: `Axioms/AbelTheorem.lean` now imports
  the E6 adapter, which imports this file). The hypothesis is DISCHARGED
  in `Jacobians/Bridge/AbelEngineAdapter.lean`
  (`zeroPeriodChainSolvability_of_engine`), and
  `AX_AbelTheorem := le_antisymm` is a theorem there over the remainder
  axiom `AX_AbelSupset`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The pinned cycle-basis witness. Definitionally equal to the
`Classical.choice` term inside `loopIntegralToH1` (hence inside
`periodMap` / `periodMapInBasis`): the `Nonempty` argument is a proof, so
any two `Classical.choice (AX_PeriodCycleBasis x₀)` terms are defeq. -/
def pinnedCycleBasis (x₀ : X) : PeriodCycleBasis X x₀ :=
  Classical.choice (AX_PeriodCycleBasis x₀)

/-- The ambient period vector of a divisor: `D = ∑ n_P · (P)` is sent to
`∑ n_P · (∫_{x₀}^{P} ω_i)_i` — the basepoint-arc side of the 1-chain. -/
def divisorPeriodVector (x₀ : X) : Divisor X →+ (Fin (genus X) → ℂ) :=
  FreeAbelianGroup.lift (fun P => ofCurveAmbient X x₀ P)

@[simp]
theorem divisorPeriodVector_of (x₀ P : X) :
    divisorPeriodVector x₀ (FreeAbelianGroup.of P) = ofCurveAmbient X x₀ P :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **A1, factorization step (pointwise).** Under the universe lift, the
Abel–Jacobi image of a divisor is the lattice-quotient class of
`divisorPeriodVector D − (deg D) • (basepoint constant)`. -/
theorem ulift_abelJacobiDiv_apply (D : Divisor X) :
    AddEquiv.ulift (abelJacobiDiv X D) =
      (QuotientAddGroup.mk'
          (periodLatticeInBasis X (Classical.arbitrary X)
            (jacobianBasis X)).toAddSubgroup)
        (divisorPeriodVector (Classical.arbitrary X) D -
          (Divisor.deg X D) •
            ofCurveAmbient X (Classical.arbitrary X)
              (Classical.arbitrary X)) := by
  induction D using FreeAbelianGroup.induction_on with
  | zero =>
      simp only [map_zero, zero_zsmul, sub_zero]
      rfl
  | of P =>
      rw [show abelJacobiDiv X (FreeAbelianGroup.of P)
            = ofCurveImpl X (Classical.arbitrary X) P from
          FreeAbelianGroup.lift_apply_of _ _,
        divisorPeriodVector_of,
        show Divisor.deg X (FreeAbelianGroup.of P : Divisor X) = 1 by
          simp [Divisor.deg],
        one_zsmul]
      rfl
  | neg x ih =>
      calc AddEquiv.ulift (abelJacobiDiv X (-FreeAbelianGroup.of x))
          = -(AddEquiv.ulift (abelJacobiDiv X (FreeAbelianGroup.of x))) := by
            rw [map_neg, map_neg]
        _ = (QuotientAddGroup.mk'
              (periodLatticeInBasis X (Classical.arbitrary X)
                (jacobianBasis X)).toAddSubgroup)
            (-(divisorPeriodVector (Classical.arbitrary X)
                (FreeAbelianGroup.of x) -
              Divisor.deg X (FreeAbelianGroup.of x : Divisor X) •
                ofCurveAmbient X (Classical.arbitrary X)
                  (Classical.arbitrary X))) := by
            rw [ih]; exact (map_neg _ _).symm
        _ = _ := by
            congr 1
            rw [map_neg, map_neg, neg_zsmul]
            abel
  | add D₁ D₂ ih₁ ih₂ =>
      calc AddEquiv.ulift (abelJacobiDiv X (D₁ + D₂))
          = AddEquiv.ulift (abelJacobiDiv X D₁) +
              AddEquiv.ulift (abelJacobiDiv X D₂) := by
            rw [map_add, map_add]
        _ = (QuotientAddGroup.mk'
              (periodLatticeInBasis X (Classical.arbitrary X)
                (jacobianBasis X)).toAddSubgroup)
            ((divisorPeriodVector (Classical.arbitrary X) D₁ -
              Divisor.deg X D₁ •
                ofCurveAmbient X (Classical.arbitrary X)
                  (Classical.arbitrary X)) +
             (divisorPeriodVector (Classical.arbitrary X) D₂ -
              Divisor.deg X D₂ •
                ofCurveAmbient X (Classical.arbitrary X)
                  (Classical.arbitrary X))) := by
            rw [ih₁, ih₂]; exact (map_add _ _ _).symm
        _ = _ := by
            congr 1
            rw [map_add, map_add, add_zsmul]
            abel

/-- **A1, lattice step.** A degree-0 divisor in the Abel–Jacobi kernel has
its ambient period vector in the period lattice. -/
theorem divisorPeriodVector_mem_lattice_of_mem_ker {D : Divisor X}
    (hker : D ∈ (abelJacobiDiv X).ker) (hdeg : D ∈ (Divisor.deg X).ker) :
    divisorPeriodVector (Classical.arbitrary X) D ∈
      periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X) := by
  have h0 : abelJacobiDiv X D = 0 := hker
  have hdeg0 : Divisor.deg X D = 0 := hdeg
  have h1 := ulift_abelJacobiDiv_apply (X := X) D
  rw [h0, map_zero, hdeg0, zero_zsmul, sub_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).mp h1.symm

/-- **The A1 output / engine input.** The divisor `D` admits a zero-period
1-chain presentation over the pinned cycle basis: the basepoint arcs
weighted by `D`, minus a ℤ-combination of the pinned loops, have vanishing
periods against every `jacobianBasis` form. Stated at the
`periodMapInBasis` level; this is the data the Forster §20 engine consumes
(AB_ROUTE A2 note: the port↔root divisor faithfulness is the engine's
obligation when discharging `ZeroPeriodChainSolvability`). -/
def HasZeroPeriodLoopPresentation (x₀ : X) (D : Divisor X) : Prop :=
  ∃ m : Fin (2 * genus X) → ℤ,
    divisorPeriodVector x₀ D =
      ∑ j, m j •
        periodMapInBasis X x₀ (jacobianBasis X)
          (loopToHomology ((pinnedCycleBasis x₀).loops j))

/-- Period-lattice membership expands over the pinned cycle basis. -/
theorem hasZeroPeriodLoopPresentation_of_mem_lattice {x₀ : X} {D : Divisor X}
    (hv : divisorPeriodVector x₀ D ∈
      periodLatticeInBasis X x₀ (jacobianBasis X)) :
    HasZeroPeriodLoopPresentation x₀ D := by
  obtain ⟨h, hh⟩ := hv
  refine ⟨fun j => (pinnedCycleBasis x₀).isBasis.repr h j, ?_⟩
  rw [← hh]
  have hexpand :
      h = ∑ j, (pinnedCycleBasis x₀).isBasis.repr h j •
        loopToHomology ((pinnedCycleBasis x₀).loops j) := by
    conv_lhs => rw [← (pinnedCycleBasis x₀).isBasis.sum_repr h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(pinnedCycleBasis x₀).loops_to_basis j]
  calc periodMapInBasis X x₀ (jacobianBasis X) h
      = periodMapInBasis X x₀ (jacobianBasis X)
          (∑ j, (pinnedCycleBasis x₀).isBasis.repr h j •
            loopToHomology ((pinnedCycleBasis x₀).loops j)) := by
        rw [← hexpand]
    _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul]

/-- **A1 (kernel unfolding), headline.** A degree-0 divisor in the
Abel–Jacobi kernel has a zero-period 1-chain presentation over the pinned
cycle basis. Conditionality: the `AX_PeriodCycleBasis` pin (its
`loops_to_basis` field) — same as the rest of the Jacobian layer. -/
theorem hasZeroPeriodLoopPresentation_of_mem_ker {D : Divisor X}
    (hker : D ∈ (abelJacobiDiv X).ker) (hdeg : D ∈ (Divisor.deg X).ker) :
    HasZeroPeriodLoopPresentation (Classical.arbitrary X) D :=
  hasZeroPeriodLoopPresentation_of_mem_lattice
    (divisorPeriodVector_mem_lattice_of_mem_ker hker hdeg)

/-- **The named engine hypothesis** (Forster §20 / Weierstrass output,
E5-shape `exists_meromorphic_of_oneChain` composed with the divisor
bridge): every degree-0 divisor with a zero-period 1-chain presentation is
principal. The port-side engine lane discharges this; nothing here
imports it. -/
def ZeroPeriodChainSolvability (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ D : Divisor X, D ∈ (Divisor.deg X).ker →
    HasZeroPeriodLoopPresentation (Classical.arbitrary X) D →
    D ∈ PrincipalDivisors X

/-- **A3 (assembly).** Over the named engine hypothesis, the ⊆ direction
of `AX_AbelTheorem` holds verbatim: the degree-0 Abel–Jacobi kernel is
contained in the principal divisors. `AX_AbelTheorem` is not used. -/
theorem abel_subset_of_engine (hEngine : ZeroPeriodChainSolvability X) :
    (abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker ≤ PrincipalDivisors X :=
  fun _D hD =>
    hEngine _ hD.2 (hasZeroPeriodLoopPresentation_of_mem_ker hD.1 hD.2)

end Jacobians.RiemannSurface
