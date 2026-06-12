/-
# P10 — the polynomial boundary-word engine at general genus

Route note: `docs/planning/P10_BW_HYPERELLIPTIC_ROUTE.md` (Decision 1,
Route P). Generalizes the merged g = 1 witness pattern
(`BoundaryWordElliptic.lean`, #220/#225) to arbitrary genus: there the
cut pullbacks were `h = c`, `F = c·z` — the polynomial family
`P i = C c * X` with the orientation constant `c` as 1×1 Cholesky
tuning. Here we take ANY polynomial primitive family
`P : Fin (genus X) → ℂ[X]`, set `F i := eval (P i)`,
`h i := eval (derivative (P i))`, and prove every per-genus-uniform
field of `ArcBoundaryWordDataInterior`:

* the four regularity fields — free, polynomials are entire;
* `word_R1`'s contour side — `∮_{∂box} F_i·h_j dz = 0` by Cauchy
  (`rectBoundaryIntegral_poly_mul`), reducing the R1 word to the bare
  matrix identity `AᵀB = BᵀA`;
* `nondeg` — a nonzero polynomial has finitely many roots while the
  open box image is infinite (`exists_openBox_eval_ne_zero`).

The two remaining inputs (`hsymm`, `hgram`) are exactly the classical
period relations in finitary matrix form — the named walls a family
witness must supply (hyperelliptic instantiation:
`Jacobians/ProjectiveCurve/Hyperelliptic/BoundaryWord.lean`).
Downstream, `ArcBoundaryWordDataInterior.periodGram_posDef` DERIVES R2
positive-definiteness from the Gram word; nothing here assumes
positivity.
-/
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWordInterior
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Jacobians.RiemannSurface
namespace BoundaryWordPolynomial

open Polynomial Matrix

/-- Cauchy on the box for a product of polynomial evaluations: the
`word_R1` right side vanishes for any polynomial cut data. -/
theorem rectBoundaryIntegral_poly_mul (p q : Polynomial ℂ) :
    Jacobians.rectBoundaryIntegral (fun z => p.eval z * q.eval z) = 0 :=
  Jacobians.rectBoundaryIntegral_eq_zero_of_differentiableOn
    ((p.differentiable.mul q.differentiable).differentiableOn)

/-- `wCLM` is injective (it is `Complex.equivRealProdCLM.symm`). -/
theorem wCLM_injective : Function.Injective ⇑Jacobians.wCLM := by
  intro p q hpq
  rw [Jacobians.wCLM_apply, Jacobians.wCLM_apply] at hpq
  exact Prod.ext (by simpa using congrArg Complex.re hpq)
    (by simpa using congrArg Complex.im hpq)

/-- A nonzero polynomial is nonzero somewhere on the open unit box: the
box image is infinite, the root set finite. The `nondeg` engine. -/
theorem exists_openBox_eval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1,
      q.eval (Jacobians.wCLM p) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hq
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hbox : (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1).Infinite :=
    Set.infinite_prod.mpr
      (Or.inl ⟨Set.Ioo_infinite (by norm_num : (0:ℝ) < 1), ⟨1 / 2, by norm_num⟩⟩)
  refine Set.Infinite.mono ?_ (hbox.image wCLM_injective.injOn)
  rintro z ⟨p, hp, rfl⟩
  exact hall p hp

section Engine

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-- **The polynomial boundary-word engine.** Given any loop family and
form basis, a polynomial primitive family `P` with linearly independent
derivatives, the R1 matrix identity `AᵀB = BᵀA`, and the R2 Gram word
(the conjugated boundary identity for the polynomial data), assemble the
full `ArcBoundaryWordDataInterior`. All regularity fields, the Cauchy
side of `word_R1`, and `nondeg` are proven here, uniformly in the genus;
`hsymm`/`hgram` are the family-specific analytic content. -/
noncomputable def polyArcBoundaryWordData
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (P : Fin (genus X) → Polynomial ℂ)
    (hind : LinearIndependent ℂ fun j => (P j).derivative)
    (hsymm : (arcAPeriodMatrix loops fun m => cω m)ᵀ
          * (arcBPeriodMatrix loops fun m => cω m)
        = (arcBPeriodMatrix loops fun m => cω m)ᵀ
          * (arcAPeriodMatrix loops fun m => cω m))
    (hgram : ∀ i j,
      ((arcAPeriodMatrix loops fun m => cω m)ᵀ
            * (arcBPeriodMatrix loops fun m => cω m).map (starRingEnd ℂ)
          - (arcBPeriodMatrix loops fun m => cω m)ᵀ
            * (arcAPeriodMatrix loops fun m => cω m).map (starRingEnd ℂ)) i j
        = - Jacobians.boundaryForm (fun z => ((P j).derivative).eval z)
            (fun z => (P i).eval z)) :
    ArcBoundaryWordDataInterior loops cω where
  h := fun j z => ((P j).derivative).eval z
  F := fun i z => (P i).eval z
  hhc := fun i => ((P i).derivative.differentiable.continuous).continuousOn
  hFc := fun i => ((P i).differentiable.continuous).continuousOn
  hh := fun i z _ => ((P i).derivative.differentiable z).hasDerivAt
  hF := fun i z _ => (P i).hasDerivAt z
  word_R1 := by
    intro i j
    rw [hsymm, sub_self, Matrix.zero_apply]
    exact (rectBoundaryIntegral_poly_mul (P i) ((P j).derivative)).symm
  word_R2 := hgram
  nondeg := by
    intro v hv
    have hq : (∑ j, v j • (P j).derivative) ≠ 0 := fun h0 =>
      hv (funext fun j => Fintype.linearIndependent_iff.mp hind v h0 j)
    obtain ⟨p, hp, hne⟩ := exists_openBox_eval_ne_zero hq
    refine ⟨p, hp, fun h0 => hne ?_⟩
    rw [Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_smul, smul_eq_mul] using h0

end Engine

end BoundaryWordPolynomial
end Jacobians.RiemannSurface
