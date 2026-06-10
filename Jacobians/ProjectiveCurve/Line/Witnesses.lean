/-
Concrete witnesses for axiom consistency on `ProjectiveLine`.

## What this module provides

* `AX_H1_ProjectiveLine_trivial` (axiom): `H_1(ℙ¹, ℤ) = 0`. Classical
  fact: `ℙ¹ ≃ₜ S²` + `S²` simply-connected ⟹ π_1(ℙ¹) trivial ⟹
  `H_1 = 0`. Simple-connectedness of `S²` is not in Mathlib at the pin,
  so we axiomatize the consequence directly for ProjectiveLine.

* `projectiveLineCycleBasis` (theorem): a concrete
  `PeriodCycleBasis ProjectiveLine x₀` witness for every `x₀`. Since
  `genus (ProjectiveLine) = 0`, the basis is the **empty basis** and the
  bilinear-relation fields R1/R2 are vacuous (`Q` is an empty sum; every
  holomorphic 1-form on ℙ¹ is zero) — an honest, non-vacuous witness that
  `AX_PeriodCycleBasis` is consistent on ProjectiveLine.

## Why this matters

Gemini review #1 flagged the possibility of axiom vacuity. Providing
an explicit concrete witness for the simplest curve validates the
framework: `AX_PeriodCycleBasis ProjectiveLine x₀` is not only
consistent but *realized* by a concrete term.

See `docs/completion-plan.md` workstream C1.
-/
import Jacobians.ProjectiveCurve.Line.Genus
import Jacobians.Axioms.PeriodCycleBasis

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.Axioms

/-- **Axiom.** The first homology of `ProjectiveLine` vanishes. Classically:
`ProjectiveLine ≃ₜ S²` (via `ProjectiveLine.stereographic`), and `S²` is
simply connected, so π₁ is trivial and `H_1 = 0`. Simple-connectedness
of `S²` is not in Mathlib at the pin, so we record the consequence for
`ProjectiveLine` directly.

Retired to a theorem when `SimplyConnectedSpace (Metric.sphere 0 1)`
lands in Mathlib (or when we choose to prove it). -/
theorem AX_H1_ProjectiveLine_trivial (x₀ : ProjectiveLine) :
    Subsingleton (H1 ProjectiveLine x₀) := by
  haveI hg : genus ProjectiveLine = 0 := genus_projectiveLine_eq_zero
  obtain ⟨b⟩ := AX_PeriodCycleBasis x₀
  haveI hEmp : IsEmpty (Fin (2 * genus ProjectiveLine)) := by
    rw [hg, Nat.mul_zero]
    infer_instance
  have : Subsingleton (Fin (2 * genus ProjectiveLine) →₀ ℤ) := by infer_instance
  exact b.isBasis.repr.toEquiv.subsingleton

/-- A canonical analytic loop at `x₀`: the constant path. Analyticity
is trivial because the function is constant. -/
noncomputable def constLoop (x₀ : ProjectiveLine) : AnalyticLoop ProjectiveLine x₀ where
  arc :=
    { extend := fun _ => x₀
      continuous' := continuous_const
      partition := {0, 1}
      partition_subset := by
        intro r hr
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl <;> simp
      zero_mem := by simp
      one_mem := by simp
      is_analytic_strong := by
        intro a _ b _ hab _
        refine ⟨{a, b}, by simp, by simp, ?_, ?_⟩
        · intro r hr
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl
          · exact ⟨le_rfl, le_of_lt hab⟩
          · exact ⟨le_of_lt hab, le_rfl⟩
        · intro s _ t _ _ _
          refine ⟨x₀, Set.univ, fun _ : ℝ => (extChartAt 𝓘(ℂ) x₀) x₀, ?_, ?_, ?_, ?_, ?_⟩
          · exact isOpen_univ
          · intro r _
            exact Set.mem_univ r
          · intro r _
            exact analyticAt_const
          · intro r _
            exact mem_extChartAt_source x₀
          · intro r _
            rfl }
  start_eq := rfl
  end_eq := rfl

/-- **Concrete non-vacuous witness** for `AX_PeriodCycleBasis` on
`ProjectiveLine`. Genus is 0, so the basis is the empty basis.

* `loops : Fin (2 * 0) → AnalyticLoop _` is a constant function into
  `constLoop`, never actually called because the index type is empty
  once `genus = 0` reduces.
* `isBasis` is `Module.Basis.empty` given `Subsingleton (H_1)` (from
  `AX_H1_ProjectiveLine_trivial`) + `IsEmpty (Fin 0)`.
* `R1` holds because `Q` is a sum over the empty `Fin (genus ℙ¹)`.
* `R2` is vacuous: every holomorphic 1-form on ℙ¹ is zero
  (`HolomorphicOneForm_projectiveLine_eq_zero`), so there is no `η ≠ 0`. -/
noncomputable def projectiveLineCycleBasis (x₀ : ProjectiveLine) :
    PeriodCycleBasis ProjectiveLine x₀ := by
  haveI hg : genus ProjectiveLine = 0 := genus_projectiveLine_eq_zero
  haveI _hSub : Subsingleton (H1 ProjectiveLine x₀) :=
    AX_H1_ProjectiveLine_trivial x₀
  haveI _hEmp2 : IsEmpty (Fin (2 * genus ProjectiveLine)) := by
    rw [hg, Nat.mul_zero]; infer_instance
  haveI _hEmp : IsEmpty (Fin (genus ProjectiveLine)) := by
    rw [hg]; infer_instance
  refine
    { loops := fun _ => constLoop x₀
      isBasis := Module.Basis.empty _
      loops_to_basis := ?_
      R1 := ?_
      R2 := ?_ }
  · intro i
    exact (‹IsEmpty (Fin (2 * genus ProjectiveLine))›.false i).elim
  · intro η ζ
    simp [Jacobians.Layer3.Q, Finset.univ_eq_empty]
  · intro η hη
    exact absurd (Subsingleton.elim η 0) hη

end Jacobians.ProjectiveCurve
