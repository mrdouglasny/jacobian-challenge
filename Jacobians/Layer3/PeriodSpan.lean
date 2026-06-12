/-
# B-3 corollaries: the period lattice spans (downstream forms)

The dissection-free non-degeneracy engine
(`RiemannSurface/PeriodNondegeneracy.lean`, Forster §21.4) specialized to the
forms the rest of the development consumes:

* `span_choiceCycleBasis_arcPeriodFunctional_eq_top` — non-degeneracy over the
  CHOSEN `AX_PeriodCycleBasis` loops' arc-period functionals;
* `span_range_loopIntegralToH1_eq_top` — the `H₁`-level period image spans;
* `span_periodLatticeInBasis_eq_top` — coordinate form: the "span half" of
  `IsZLattice` for `periodLatticeInBasis`, independent of the bundled `R2`.

These route through the chosen witness only to identify arbitrary-loop
functionals with `loopIntegralToH1` values (`LoopIntegralHom`), so they carry
`AX_PeriodCycleBasis` in their closure; the engine headline itself
(`span_loopPeriodFunctional_eq_top`) does not.

Consequence (issue #206 finding): NONE of these downstream forms may be
cited inside an `AX_PeriodCycleBasis` discharge chain — that would be
circular. Discharge-grade spanning is the axiom-free layer:
`span_loopPeriodFunctional_eq_top` / `span_real_loopPeriodLattice_eq_top` /
`loopDevValH1Hom`.
-/
import Jacobians.RiemannSurface.PeriodNondegeneracy
import Jacobians.RiemannSurface.LoopIntegralHom
import Jacobians.Axioms.PeriodLatticeBase

namespace Jacobians.Layer3

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Every analytic-loop period functional is the `loopIntegralToH1` value of
the loop's homology class (developing-value bridge). -/
theorem loopPeriodFunctional_eq_loopIntegralToH1 (x₀ : X)
    (γ : AnalyticLoop X x₀) :
    loopPeriodFunctional x₀ γ =
      loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology γ) := by
  refine LinearMap.ext fun form => ?_
  rw [loopPeriodFunctional_apply,
    ← loopDevValH1Hom_eq_loopIntegralToH1_apply x₀ form
      (Jacobians.Axioms.loopToHomology γ),
    loopDevValH1Hom_loopToHomology]

/-- **C2: the `H₁`-level period image spans ℝ-linearly** (Forster §21.4
non-degeneracy, transported along the homology identification).

**WARNING — axiom-downstream, NOT usable in `AX_PeriodCycleBasis` discharge
chains** (issue #206 finding): `loopIntegralToH1` is *defined* via
`Classical.choice (AX_PeriodCycleBasis x₀)` (`LoopIntegral.lean`), so this
spanning statement lives downstream of the axiom being discharged — citing
it in a discharge chain is circular. Discharge-grade spanning lives in the
axiom-free layer: `span_loopPeriodFunctional_eq_top`
(`PeriodNondegeneracy.lean`, over `loopPeriodFunctional` /
`canonicalArcIntegral`) and its coordinate form
`span_real_loopPeriodLattice_eq_top` (`PeriodDiscreteness.lean`); the
axiom-free `H₁`-level functional is `loopDevValH1Hom`
(`LoopIntegralHom.lean`). -/
theorem span_range_loopIntegralToH1_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range (loopIntegralToH1 x₀)) = ⊤ := by
  rw [eq_top_iff, ← span_loopPeriodFunctional_eq_top x₀]
  apply Submodule.span_mono
  rintro _ ⟨γ, rfl⟩
  exact ⟨Jacobians.Axioms.loopToHomology γ,
    (loopPeriodFunctional_eq_loopIntegralToH1 x₀ γ).symm⟩

/-- **C1: non-degeneracy over the CHOSEN `AX_PeriodCycleBasis` loops' arc
periods.** The ℝ-span of the `2g` chosen arc-period functionals is the whole
dual `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`: no nonzero ℝ-linear functional kills
the chosen periods. -/
theorem span_choiceCycleBasis_arcPeriodFunctional_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range fun i : Fin (2 * genus X) =>
      arcPeriodFunctional
        ((Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)).loops i).arc
        fun form => AX_cycleBasisLoop_integrable x₀
          (Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)) i form)
      = ⊤ := by
  classical
  set cb := Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀) with hcb
  set gens : Fin (2 * genus X) → (HolomorphicOneForm X →ₗ[ℂ] ℂ) := fun i =>
    arcPeriodFunctional (cb.loops i).arc
      (fun form => AX_cycleBasisLoop_integrable x₀ cb i form) with hgens
  rw [eq_top_iff, ← span_loopPeriodFunctional_eq_top x₀, Submodule.span_le]
  rintro _ ⟨γ, rfl⟩
  have hL : loopPeriodFunctional x₀ γ =
      (loopIntegralToH1 x₀).toIntLinearMap (Jacobians.Axioms.loopToHomology γ) :=
    loopPeriodFunctional_eq_loopIntegralToH1 x₀ γ
  have hmemZ : (loopIntegralToH1 x₀).toIntLinearMap
      (Jacobians.Axioms.loopToHomology γ) ∈
        Submodule.span ℤ (Set.range gens) := by
    have h1 : Jacobians.Axioms.loopToHomology γ ∈
        Submodule.span ℤ (Set.range cb.isBasis) := by
      rw [cb.isBasis.span_eq]
      trivial
    have h2 := Submodule.mem_map_of_mem
      (f := (loopIntegralToH1 x₀).toIntLinearMap) h1
    rw [Submodule.map_span] at h2
    have himg : ⇑(loopIntegralToH1 x₀).toIntLinearMap '' Set.range cb.isBasis
        = Set.range gens := by
      rw [← Set.range_comp]
      refine congrArg Set.range (funext fun i => ?_)
      change loopIntegralToH1 x₀ (cb.isBasis i) = gens i
      rw [cb.loops_to_basis i]
      simpa [hcb, hgens] using loopIntegralToH1_loop (X := X) x₀ i
    rw [himg] at h2
    exact h2
  rw [hL]
  exact Submodule.span_subset_span ℤ ℝ (Set.range gens) hmemZ

/-- **C3 (coordinate form): the period lattice spans `ℂ^g` over ℝ** — the
"span half" of `IsZLattice ℝ (periodLatticeInBasis X x₀ b)`, obtained from
the maximum-principle engine instead of the bundled Hodge-positivity `R2`. -/
theorem span_periodLatticeInBasis_eq_top (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Submodule.span ℝ
        ((Jacobians.Axioms.periodLatticeInBasis X x₀ b :
          Submodule ℤ (Fin (genus X) → ℂ)) : Set (Fin (genus X) → ℂ)) = ⊤ := by
  classical
  set e : (HolomorphicOneForm X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
    b.dualBasis.equivFun with he
  have hset : ((Jacobians.Axioms.periodLatticeInBasis X x₀ b :
      Submodule ℤ (Fin (genus X) → ℂ)) : Set (Fin (genus X) → ℂ))
      = ⇑e '' Set.range (loopIntegralToH1 x₀) := by
    ext v
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨loopIntegralToH1 x₀ γ, ⟨γ, rfl⟩, rfl⟩
    · rintro ⟨F, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ, rfl⟩
  rw [hset,
    show ⇑e = ⇑(e.toLinearMap.restrictScalars ℝ) from rfl,
    ← Submodule.map_span, span_range_loopIntegralToH1_eq_top x₀,
    Submodule.map_top, LinearMap.range_eq_top]
  exact fun v => ⟨e.symm v, e.apply_symm_apply v⟩

end

end Jacobians.Layer3
