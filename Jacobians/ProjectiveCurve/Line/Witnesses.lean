/-
Concrete witnesses for axiom consistency on `ProjectiveLine`.

## What this module provides

* `AX_H1_ProjectiveLine_trivial` (axiom): `H_1(ℙ¹, ℤ) = 0`. Classical
  fact: `ℙ¹ ≃ₜ S²` + `S²` simply-connected ⟹ π_1(ℙ¹) trivial ⟹
  `H_1 = 0`. Simple-connectedness of `S²` is not in Mathlib at the pin,
  so we axiomatize the consequence directly for ProjectiveLine.

* `projectiveLineCycleBasis` (theorem): a concrete
  `AnalyticCycleBasis ProjectiveLine x₀` witness for every `x₀`. Since
  `genus (ProjectiveLine) = 0`, the basis is the **empty basis** —
  an honest, non-vacuous witness that `AX_AnalyticCycleBasis` is
  consistent on ProjectiveLine.

## Why this matters

Gemini review #1 flagged the possibility of axiom vacuity. Providing
an explicit concrete witness for the simplest curve validates the
framework: `AX_AnalyticCycleBasis ProjectiveLine x₀` is not only
consistent but *realized* by a concrete term.

See `docs/completion-plan.md` workstream C1.
-/
import Jacobians.ProjectiveCurve.Line.Genus
import Jacobians.Axioms.AnalyticCycleBasis

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
axiom AX_H1_ProjectiveLine_trivial (x₀ : ProjectiveLine) :
    Subsingleton (H1 ProjectiveLine x₀)

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
      is_analytic := by
        intro s _ t _ _ u _
        exact analyticAt_const }
  start_eq := rfl
  end_eq := rfl

/-- **Concrete non-vacuous witness** for `AX_AnalyticCycleBasis` on
`ProjectiveLine`. Genus is 0, so the basis is the empty basis.

* `loops : Fin (2 * 0) → AnalyticLoop _` is a constant function into
  `constLoop`, never actually called because the index type is empty
  once `genus = 0` reduces.
* `isBasis` is `Module.Basis.empty` given `Subsingleton (H_1)` (from
  `AX_H1_ProjectiveLine_trivial`) + `IsEmpty (Fin 0)`.
* `symplectic` is vacuously true because `Fin (genus ℙ¹) = Fin 0`
  is empty. -/
noncomputable def projectiveLineCycleBasis (x₀ : ProjectiveLine) :
    AnalyticCycleBasis ProjectiveLine x₀ := by
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
      symplectic := ?_ }
  intro i _
  exact (‹IsEmpty (Fin (genus ProjectiveLine))›.false i).elim

end Jacobians.ProjectiveCurve
