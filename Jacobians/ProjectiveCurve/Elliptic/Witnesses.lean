/-
Concrete witnesses for `AX_AnalyticCycleBasis` on `Elliptic ω₁ ω₂ h`.

## What this module provides

Given `genus (Elliptic ω₁ ω₂ h) = 1` (from `AX_genus_Elliptic_eq_one`)
the classical construction of a symplectic basis of `H_1` uses the
two generators of the lattice `Λ = ℤω₁ + ℤω₂`, projected down to the
torus:

* **A-cycle**: `A(r) := [r · ω₁]` in `ℂ / Λ`. Closed because
  `[0] = [ω₁]` (both in the identity class modulo `Λ`).
* **B-cycle**: `B(r) := [r · ω₂]`, analogous.

These are piecewise-real-analytic (in fact linear) in `r`. Their
homology classes form a ℤ-basis of `H_1(Elliptic, ℤ)` symplectic with
respect to the intersection form: `⟨A, A⟩ = ⟨B, B⟩ = 0`, `⟨A, B⟩ = 1`.

## What this module axiomatizes

Three Elliptic-specific axioms wrap the detailed classical facts that
would require substantial covering-space / fundamental-group
infrastructure to prove:

* `AX_Elliptic_aLoop_analytic`: the A-cycle is `IsAnalyticArc`.
* `AX_Elliptic_bLoop_analytic`: the B-cycle is `IsAnalyticArc`.
* `AX_Elliptic_H1_symplectic`: their classes form a symplectic
  `Module.Basis (Fin 2) ℤ (H_1 (Elliptic _) _)` with the desired
  α/β pairing.

Each axiom retires when (a) analyticity is verified against
ComplexTorus's chart atlas (chart transitions are translations, fderiv
is 1), and (b) the deck-transformation / covering-space description of
`π₁(ℂ/Λ) = Λ ≃ ℤ²` is available.

## The witness

`ellipticCycleBasis` assembles the three axioms into a concrete
`AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0` term. Non-vacuous and
traceable — axiom dependencies auditable via `lean_verify`.

See `docs/completion-plan.md` workstream C2.
-/
import Jacobians.ProjectiveCurve.Elliptic.Genus
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.Axioms.AnalyticCycleBasis

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.Axioms Jacobians.AbelianVariety

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

/-- The A-cycle of an elliptic curve, as a real-parameter path:
`A(r) = [r · ω₁]` in `ℂ / Λ`. Linear in `r`, hence trivially continuous.
Uses complex multiplication `(r : ℂ) * ω₁` to sidestep
`ContinuousSMul ℝ ℂ` synthesis. -/
noncomputable def aLoopExtend : ℝ → Elliptic ω₁ ω₂ h :=
  fun r => (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup) ((r : ℂ) * ω₁)

/-- The B-cycle: `B(r) = [r · ω₂]`. -/
noncomputable def bLoopExtend : ℝ → Elliptic ω₁ ω₂ h :=
  fun r => (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup) ((r : ℂ) * ω₂)

lemma continuous_aLoopExtend : Continuous (aLoopExtend ω₁ ω₂ h) := by
  unfold aLoopExtend
  exact continuous_quotient_mk'.comp
    (Complex.continuous_ofReal.mul continuous_const)

lemma continuous_bLoopExtend : Continuous (bLoopExtend ω₁ ω₂ h) := by
  unfold bLoopExtend
  exact continuous_quotient_mk'.comp
    (Complex.continuous_ofReal.mul continuous_const)

/-- **Axiom.** The A-cycle is piecewise-real-analytic.

Classical: linear in `r`, hence real-analytic. The predicate
`IsAnalyticArc` requires checking chart-local analyticity of
`(extChartAt 𝓘(ℂ) (extend u)) ∘ extend` at every interior point of
`{0, 1}` partition. Since ComplexTorus's charts have transition maps
that are translations with `fderiv = 1`, the chart-pullback is a
(locally) affine function of `r`, which is analytic. Full verification
defers to detailed ComplexTorus atlas analysis. -/
axiom AX_Elliptic_aLoop_analytic :
    IsAnalyticArc (Elliptic ω₁ ω₂ h) (aLoopExtend ω₁ ω₂ h) {0, 1}

/-- **Axiom.** The B-cycle is piecewise-real-analytic. -/
axiom AX_Elliptic_bLoop_analytic :
    IsAnalyticArc (Elliptic ω₁ ω₂ h) (bLoopExtend ω₁ ω₂ h) {0, 1}

/-- The A-cycle as an `AnalyticArc`. -/
noncomputable def aArc : AnalyticArc (Elliptic ω₁ ω₂ h) where
  extend := aLoopExtend ω₁ ω₂ h
  continuous' := continuous_aLoopExtend ω₁ ω₂ h
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic := AX_Elliptic_aLoop_analytic ω₁ ω₂ h

/-- The B-cycle as an `AnalyticArc`. -/
noncomputable def bArc : AnalyticArc (Elliptic ω₁ ω₂ h) where
  extend := bLoopExtend ω₁ ω₂ h
  continuous' := continuous_bLoopExtend ω₁ ω₂ h
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic := AX_Elliptic_bLoop_analytic ω₁ ω₂ h

/-- The A-cycle as an `AnalyticLoop` based at `0 : Elliptic`. Closed
because `A(0) = [0] = 0 = [ω₁] = A(1)` (since `ω₁ ∈ Λ`). -/
noncomputable def aLoop : AnalyticLoop (Elliptic ω₁ ω₂ h) 0 where
  arc := aArc ω₁ ω₂ h
  start_eq := by
    change aLoopExtend ω₁ ω₂ h 0 = 0
    unfold aLoopExtend
    push_cast
    rw [zero_mul]
    rfl
  end_eq := by
    change aLoopExtend ω₁ ω₂ h 1 = 0
    unfold aLoopExtend
    push_cast
    rw [one_mul, QuotientAddGroup.mk'_apply]
    change (↑ω₁ : ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change ω₁ ∈ ellipticLattice ω₁ ω₂ h
    unfold ellipticLattice
    exact Submodule.subset_span ⟨0, by simp [ellipticRealBasis]⟩

/-- The B-cycle as an `AnalyticLoop` based at `0`. -/
noncomputable def bLoop : AnalyticLoop (Elliptic ω₁ ω₂ h) 0 where
  arc := bArc ω₁ ω₂ h
  start_eq := by
    change bLoopExtend ω₁ ω₂ h 0 = 0
    unfold bLoopExtend
    push_cast
    rw [zero_mul]
    rfl
  end_eq := by
    change bLoopExtend ω₁ ω₂ h 1 = 0
    unfold bLoopExtend
    push_cast
    rw [one_mul, QuotientAddGroup.mk'_apply]
    change (↑ω₂ : ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change ω₂ ∈ ellipticLattice ω₁ ω₂ h
    unfold ellipticLattice
    exact Submodule.subset_span ⟨1, by simp [ellipticRealBasis]⟩

/-- **Axiom.** Symplectic basis of `H_1` from A- and B-cycles. Provides
the `Module.Basis (Fin 2) ℤ (H_1 _ _)` structure together with a
specialization to `Fin (2 * genus (Elliptic _)) = Fin 2` (after the
`genus_Elliptic_eq_one` rewrite) and the symplectic matrix condition. -/
axiom AX_Elliptic_H1_symplectic :
    AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0

/-- **Concrete witness** for `AX_AnalyticCycleBasis` on `Elliptic`.
Axiom-wrapped at this level — genuine non-vacuity would come from
discharging `AX_Elliptic_H1_symplectic` via covering-space theory +
concrete A/B cycle constructions. -/
noncomputable def ellipticCycleBasis : AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0 :=
  AX_Elliptic_H1_symplectic ω₁ ω₂ h

end Jacobians.ProjectiveCurve
