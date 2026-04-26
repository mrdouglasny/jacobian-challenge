/-
# Phase OA1 — Affine smooth-locus charts on `HyperellipticAffine H`

Builds two families of `PartialHomeomorph`s on `HyperellipticAffine H`:
* `affineChartProjX` — chart `(x, y) ↦ x`, valid where `y ≠ 0`.
* `affineChartProjY` — chart `(x, y) ↦ y`, valid where `f'(x) ≠ 0`
  (equivalently, where `(x, 0)` is a simple root of `f` — the
  "branch points" of the hyperelliptic projection).

Squarefreeness of `f` ⇒ at every affine point, at least one of these
is well-defined; together they cover `HyperellipticAffine H`.

## Mathlib API

* `Mathlib.Analysis.Calculus.InverseFunctionTheorem` — extracts
  `PartialHomeomorph` from a smooth bijection with invertible
  differential.
* `Polynomial.IsRoot`, `Polynomial.derivative`, `Polynomial.squarefree_iff_no_repeated_roots`
  — for the squarefree-implies-`f'(α) ≠ 0` argument at roots.

See `docs/hyperelliptic-odd-atlas-plan.md` §OA1.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.GeneralResults.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic

namespace Jacobians.ProjectiveCurve.HyperellipticAffine

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData}

/-- The smooth locus where the projection `(x, y) ↦ x` is a local chart:
the set of points `(x, y)` with `y ≠ 0`. Open in `HyperellipticAffine H`. -/
def smoothLocusY (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { p | p.val.2 ≠ 0 }

/-- The smooth locus where the projection `(x, y) ↦ y` is a local chart:
the set of points `(x, y)` with `f'(x) ≠ 0` (equivalently, `(x, 0)` is
a simple root of `f`). Open in `HyperellipticAffine H`. -/
def smoothLocusX (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { p | (Polynomial.derivative H.f).eval p.val.1 ≠ 0 }

/-- If `x` is a root of the squarefree defining polynomial `f`, then `f'(x) ≠ 0`.
This is the algebraic input behind the branch-point chart `(x, y) ↦ y`. -/
theorem eval_derivative_ne_zero_of_eval_eq_zero (H : HyperellipticData) {x : ℂ}
    (hx : H.f.eval x = 0) : H.f.derivative.eval x ≠ 0 := by
  intro hder
  have hf_ne : H.f ≠ 0 := by
    intro h0
    have hdeg := H.h_degree
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hroot : H.f.IsRoot x := Polynomial.IsRoot.def.mpr hx
  have hrootder : H.f.derivative.IsRoot x := Polynomial.IsRoot.def.mpr hder
  have hmult : 1 < H.f.rootMultiplicity x := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hf_ne]
    exact ⟨hroot, hrootder⟩
  have hsq_dvd : (Polynomial.X - Polynomial.C x) ^ 2 ∣ H.f := by
    rw [← Polynomial.le_rootMultiplicity_iff hf_ne]
    omega
  have hsq_dvd' : (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C x) ∣ H.f := by
    simpa [pow_two] using hsq_dvd
  have hirr : Irreducible (Polynomial.X - Polynomial.C x : Polynomial ℂ) :=
    Polynomial.irreducible_X_sub_C x
  have hsqfree :=
    (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hf_ne).1 H.h_squarefree
  exact hsqfree _ hirr hsq_dvd'

/-- A point with `y = 0` automatically lies in the `x`-chart smooth locus,
because squarefreeness rules out repeated roots. -/
theorem mem_smoothLocusX_of_y_eq_zero (H : HyperellipticData) {p : HyperellipticAffine H}
    (hp : p.val.2 = 0) : p ∈ smoothLocusX H := by
  change H.f.derivative.eval p.val.1 ≠ 0
  apply eval_derivative_ne_zero_of_eval_eq_zero
  have htmp : (0 : ℂ) = H.f.eval p.val.1 := by
    simpa [hp] using p.property
  exact htmp.symm

/-- `smoothLocusY` is open: it is the nonvanishing locus of the continuous
`y`-coordinate on the affine curve. -/
theorem isOpen_smoothLocusY (H : HyperellipticData) : IsOpen (smoothLocusY H) := by
  let f : HyperellipticAffine H → ℂ := fun p => p.val.2
  have hcont : Continuous f := continuous_subtype_val.snd
  have hclosed : IsClosed {p : HyperellipticAffine H | f p = 0} :=
    isClosed_eq hcont (continuous_const : Continuous fun _ : HyperellipticAffine H => (0 : ℂ))
  simpa [smoothLocusY, f, Set.compl_setOf] using hclosed.isOpen_compl

/-- `smoothLocusX` is open: it is the nonvanishing locus of the continuous
function `p ↦ f'(x(p))`. -/
theorem isOpen_smoothLocusX (H : HyperellipticData) : IsOpen (smoothLocusX H) := by
  let f : HyperellipticAffine H → ℂ := fun p => (Polynomial.derivative H.f).eval p.val.1
  have hcont : Continuous f := (Polynomial.continuous _).comp continuous_subtype_val.fst
  have hclosed : IsClosed {p : HyperellipticAffine H | f p = 0} :=
    isClosed_eq hcont (continuous_const : Continuous fun _ : HyperellipticAffine H => (0 : ℂ))
  simpa [smoothLocusX, f, Set.compl_setOf] using hclosed.isOpen_compl

/-- **Squarefree ⇒ smooth locus covers everything.** Every point of
`HyperellipticAffine H` lies in `smoothLocusY ∪ smoothLocusX`. -/
theorem smoothLocus_cover (H : HyperellipticData) :
    smoothLocusY H ∪ smoothLocusX H = Set.univ := by
  -- At any point (x₀, y₀) with y₀² = f(x₀):
  -- if y₀ ≠ 0 then (x₀, y₀) ∈ smoothLocusY;
  -- if y₀ = 0 then f(x₀) = 0, and squarefreeness ⇒ f'(x₀) ≠ 0,
  -- so (x₀, y₀) ∈ smoothLocusX.
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hpY : p ∈ smoothLocusY H
  · exact Or.inl hpY
  · right
    have hpY0 : p.val.2 = 0 := by
      simpa [smoothLocusY] using hpY
    exact mem_smoothLocusX_of_y_eq_zero H hpY0

/-  The `(x, y) ↦ x` chart on `smoothLocusY` is built from a local inverse to
the square map at `y₀ ≠ 0`, so that `x ↦ (x, y(x))` is defined near the base
point. -/
/-- Local inverse package for the square map `y ↦ y²` at a point where
`y ≠ 0`. -/
noncomputable def squareLocalHomeomorph (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) : OpenPartialHomeomorph ℂ ℂ := by
  let c : ℂ := p.val.2 * 2
  have hc : c ≠ 0 := by
    simpa [smoothLocusY, c] using mul_ne_zero hp (show (2 : ℂ) ≠ 0 by norm_num)
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    apply ContinuousLinearMap.ext
    intro z
    change (p.val.2 * 2) * z = z * (p.val.2 * 2)
    ring
  have hf : HasFDerivAt (fun y : ℂ => y ^ 2) (e' : ℂ →L[ℂ] ℂ) p.val.2 := by
    simpa [hmap, c, pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_pow 2 p.val.2).hasFDerivAt
  have hcont : ContDiffAt ℂ ω (fun y : ℂ => y ^ 2) p.val.2 := by
    simpa using (contDiffAt_id.pow 2 : ContDiffAt ℂ ω (fun y : ℂ => y ^ 2) p.val.2)
  exact hcont.toOpenPartialHomeomorph (fun y : ℂ => y ^ 2) hf (by simp)

/-- The `(x, y) ↦ x` chart on `smoothLocusY`, built from a local inverse to
`y ↦ y²` near the base point. -/
noncomputable def affineChartProjX (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ := by
  classical
  let e := squareLocalHomeomorph (H := H) p hp
  let source : Set (HyperellipticAffine H) := { q | q.val.2 ∈ e.source }
  let target : Set ℂ := { x | H.f.eval x ∈ e.target }
  letI : DecidablePred fun x : ℂ => x ∈ target := Classical.decPred _
  let invFun : ℂ → HyperellipticAffine H := fun x =>
    if hx : x ∈ target then
      ⟨(x, e.symm (H.f.eval x)), by
        change (e.symm (H.f.eval x)) ^ 2 = H.f.eval x
        simpa [e, squareLocalHomeomorph] using
          (e.right_inv (by simpa [target] using hx))⟩
    else Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.1
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change H.f.eval q.val.1 ∈ e.target
            simpa [e, squareLocalHomeomorph, q.property] using e.map_source hq
          map_target' := by
            intro x hx
            dsimp [invFun]
            simp only [hx, dite_true, source]
            exact e.map_target (by simpa [target] using hx)
          left_inv' := by
            intro q hq
            have hy : q.val.2 ∈ e.source := hq
            have hx : q.val.1 ∈ target := by
              simpa [target, e, squareLocalHomeomorph, q.property] using e.map_source hy
            dsimp [invFun]
            rw [dif_pos hx]
            apply Subtype.ext
            have hy' : e.symm (H.f.eval q.val.1) = q.val.2 := by
              simpa [e, squareLocalHomeomorph, q.property] using e.left_inv hy
            exact Prod.ext rfl hy'
          right_inv' := by
            intro x hx
            dsimp [invFun]
            simp [hx] }
      open_source := by
        simpa [source] using e.open_source.preimage continuous_subtype_val.snd
      open_target := by
        simpa [target] using e.open_target.preimage ((Polynomial.continuous H.f))
      continuousOn_toFun := by
        simpa [source] using continuous_subtype_val.fst.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun x : target => invFun x)
        have hEq :
            (fun x : target => invFun x) =
              (fun x : target =>
                ⟨((x : ℂ), e.symm (H.f.eval (x : ℂ))), by
                  change (e.symm (H.f.eval (x : ℂ))) ^ 2 = H.f.eval (x : ℂ)
                  simpa [target, e, squareLocalHomeomorph] using (e.right_inv x.property)⟩) := by
          funext x
          have hx' : H.f.eval (x : ℂ) ∈ e.target := x.property
          change
            (if hx : H.f.eval (x : ℂ) ∈ e.target then
              ⟨((x : ℂ), e.symm (H.f.eval (x : ℂ))), by
                change (e.symm (H.f.eval (x : ℂ))) ^ 2 = H.f.eval (x : ℂ)
                simpa [target, e, squareLocalHomeomorph] using (e.right_inv hx)⟩
             else Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))) =
            ⟨((x : ℂ), e.symm (H.f.eval (x : ℂ))), by
              change (e.symm (H.f.eval (x : ℂ))) ^ 2 = H.f.eval (x : ℂ)
              simpa [target, e, squareLocalHomeomorph] using (e.right_inv x.property)⟩
          rw [dif_pos hx']
        rw [hEq]
        have hsecond : Continuous (fun x : target => e.symm (H.f.eval (x : ℂ))) := by
          have hsecondOn : ContinuousOn (fun x : ℂ => e.symm (H.f.eval x)) target := by
            simpa [Function.comp] using
              (ContinuousOn.comp (s := target) (t := e.target) e.symm.continuousOn
                ((Polynomial.continuous H.f).continuousOn) (by
                  intro x hx
                  simpa [target] using hx))
          simpa [Set.restrict] using continuousOn_iff_continuous_restrict.mp hsecondOn
        exact Continuous.subtype_mk (continuous_subtype_val.prodMk hsecond) (by
          intro x
          change (e.symm (Polynomial.eval (x : ℂ) H.f)) ^ 2 = Polynomial.eval (x : ℂ) H.f
          simpa [target, e, squareLocalHomeomorph] using (e.right_inv x.property))
      }

/-- The chosen `x`-projection chart is defined at its base point. -/
theorem affineChartProjX_mem_source (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) :
    p ∈ (affineChartProjX p hp).source := by
  let e := squareLocalHomeomorph (H := H) p hp
  change p.val.2 ∈ e.source
  dsimp [e, squareLocalHomeomorph]
  let c : ℂ := p.val.2 * 2
  have hc : c ≠ 0 := by
    simpa [smoothLocusY, c] using mul_ne_zero hp (show (2 : ℂ) ≠ 0 by norm_num)
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    apply ContinuousLinearMap.ext
    intro z
    change (p.val.2 * 2) * z = z * (p.val.2 * 2)
    ring
  have hf : HasFDerivAt (fun y : ℂ => y ^ 2) (e' : ℂ →L[ℂ] ℂ) p.val.2 := by
    simpa [hmap, c, pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_pow 2 p.val.2).hasFDerivAt
  exact ContDiffAt.mem_toOpenPartialHomeomorph_source
    (contDiffAt_id.pow 2 : ContDiffAt ℂ ω (fun y : ℂ => y ^ 2) p.val.2) (hf' := hf) (hn := by simp)

@[simp] theorem affineChartProjX_symm_apply_fst (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) {x : ℂ} (hx : x ∈ (affineChartProjX p hp).target) :
    (((affineChartProjX p hp).symm x : HyperellipticAffine H).val.1) = x := by
  classical
  have hx' : Polynomial.eval x H.f ∈ (squareLocalHomeomorph (H := H) p hp).target := by
    simpa [affineChartProjX] using hx
  dsimp [affineChartProjX]
  rw [dif_pos hx']

@[simp] theorem affineChartProjX_symm_apply_snd (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) {x : ℂ} (hx : x ∈ (affineChartProjX p hp).target) :
    (((affineChartProjX p hp).symm x : HyperellipticAffine H).val.2) =
      (squareLocalHomeomorph (H := H) p hp).symm (H.f.eval x) := by
  classical
  have hx' : Polynomial.eval x H.f ∈ (squareLocalHomeomorph (H := H) p hp).target := by
    simpa [affineChartProjX] using hx
  dsimp [affineChartProjX]
  rw [dif_pos hx']

/-- Local inverse package for the polynomial map `x ↦ f(x)` at a point where
`f'(x) ≠ 0`. -/
noncomputable def polynomialLocalHomeomorph (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) : OpenPartialHomeomorph ℂ ℂ := by
  let c : ℂ := H.f.derivative.eval p.val.1
  have hc : c ≠ 0 := hp
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    ext z
    simp [e', c, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hf : HasFDerivAt (fun x : ℂ => H.f.eval x) (e' : ℂ →L[ℂ] ℂ) p.val.1 := by
    simpa [hmap] using (Polynomial.hasDerivAt H.f p.val.1).hasFDerivAt
  exact (Polynomial.contDiff_aeval H.f ω).contDiffAt.toOpenPartialHomeomorph
    (fun x : ℂ => H.f.eval x) hf (by simp)

/-- The `(x, y) ↦ y` chart on `smoothLocusX`, built from a local inverse to
`x ↦ f(x)` near the base point. -/
noncomputable def affineChartProjY (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ := by
  classical
  let e := polynomialLocalHomeomorph (H := H) p hp
  let source : Set (HyperellipticAffine H) := { q | q.val.1 ∈ e.source }
  let target : Set ℂ := { y | y ^ 2 ∈ e.target }
  letI : DecidablePred fun y : ℂ => y ∈ target := Classical.decPred _
  let invFun : ℂ → HyperellipticAffine H := fun y =>
    if hy : y ∈ target then
      ⟨(e.symm (y ^ 2), y), by
        have hy' : y ^ 2 ∈ e.target := hy
        change y ^ 2 = H.f.eval (e.symm (y ^ 2))
        simpa [e] using (e.right_inv hy').symm⟩
    else Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.2
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change q.val.2 ^ 2 ∈ e.target
            simpa [source, e, q.property] using e.map_source hq
          map_target' := by
            intro y hy
            dsimp [invFun]
            simp only [hy, dite_true, source]
            exact e.map_target (by simpa [target] using hy)
          left_inv' := by
            intro q hq
            have hy : q.val.2 ∈ target := by
              change q.val.2 ^ 2 ∈ e.target
              simpa [source, e, q.property] using e.map_source hq
            simp [invFun, hy]
            apply Subtype.ext
            have hx : e.symm (q.val.2 ^ 2) = q.val.1 := by
              simpa [e, q.property] using e.left_inv hq
            exact Prod.ext hx rfl
          right_inv' := by
            intro y hy
            dsimp [invFun]
            simp [hy] }
      open_source := by
        simpa [source] using e.open_source.preimage continuous_subtype_val.fst
      open_target := by
        simpa [target] using e.open_target.preimage ((continuous_id'.pow 2))
      continuousOn_toFun := by
        simpa [source] using continuous_subtype_val.snd.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun y : target => invFun y)
        have hEq :
            (fun y : target => invFun y) =
              (fun y : target =>
                ⟨(e.symm ((y : ℂ) ^ 2), y), by
                  change (y : ℂ) ^ 2 = H.f.eval (e.symm ((y : ℂ) ^ 2))
                  simpa [target, e] using (e.right_inv y.property).symm⟩) := by
          funext y
          have hy' : ((y : ℂ) ^ 2) ∈ e.target := y.property
          change
            (if hy : ((y : ℂ) ^ 2 ∈ e.target) then
              ⟨(e.symm ((y : ℂ) ^ 2), y), by
                change (y : ℂ) ^ 2 = H.f.eval (e.symm ((y : ℂ) ^ 2))
                simpa [target, e] using (e.right_inv hy).symm⟩
             else Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))) =
            ⟨(e.symm ((y : ℂ) ^ 2), y), by
              change (y : ℂ) ^ 2 = H.f.eval (e.symm ((y : ℂ) ^ 2))
              simpa [target, e] using (e.right_inv y.property).symm⟩
          rw [dif_pos hy']
        rw [hEq]
        have hfirst : Continuous (fun y : target => e.symm ((y : ℂ) ^ 2)) := by
          have hfirstOn : ContinuousOn (fun y : ℂ => e.symm (y ^ 2)) target := by
            simpa [Function.comp] using
              (ContinuousOn.comp (s := target) (t := e.target) e.symm.continuousOn
                ((continuous_id'.pow 2).continuousOn) (by
                  intro y hy
                  simpa [target] using hy))
          simpa [Set.restrict] using continuousOn_iff_continuous_restrict.mp hfirstOn
        exact Continuous.subtype_mk (Continuous.prodMk hfirst continuous_subtype_val) (by
          intro y
          change (y : ℂ) ^ 2 = H.f.eval (e.symm ((y : ℂ) ^ 2))
          simpa [target, e] using (e.right_inv y.property).symm)
      }

/-- The chosen `y`-projection chart is defined at its base point. -/
theorem affineChartProjY_mem_source (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) :
    p ∈ (affineChartProjY p hp).source := by
  let e := polynomialLocalHomeomorph (H := H) p hp
  change p.val.1 ∈ e.source
  dsimp [e, polynomialLocalHomeomorph]
  let c : ℂ := H.f.derivative.eval p.val.1
  have hc : c ≠ 0 := hp
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hf : HasFDerivAt (fun x : ℂ => H.f.eval x) (e' : ℂ →L[ℂ] ℂ) p.val.1 := by
    convert (Polynomial.hasDerivAt H.f p.val.1).hasFDerivAt using 1
    ext z
    simp [e', c, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  exact ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((Polynomial.contDiff_aeval H.f ω).contDiffAt) (hf' := hf) (hn := by simp)

@[simp] theorem affineChartProjY_symm_apply_fst (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) {y : ℂ} (hy : y ∈ (affineChartProjY p hp).target) :
    (((affineChartProjY p hp).symm y : HyperellipticAffine H).val.1) =
      (polynomialLocalHomeomorph (H := H) p hp).symm (y ^ 2) := by
  classical
  have hy' : y ^ 2 ∈ (polynomialLocalHomeomorph (H := H) p hp).target := by
    simpa [affineChartProjY] using hy
  dsimp [affineChartProjY]
  rw [dif_pos hy']

@[simp] theorem affineChartProjY_symm_apply_snd (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) {y : ℂ} (hy : y ∈ (affineChartProjY p hp).target) :
    (((affineChartProjY p hp).symm y : HyperellipticAffine H).val.2) = y := by
  classical
  have hy' : y ^ 2 ∈ (polynomialLocalHomeomorph (H := H) p hp).target := by
    simpa [affineChartProjY] using hy
  dsimp [affineChartProjY]
  rw [dif_pos hy']

/-- Choose one of the two affine chart families at a point, using the open cover
`smoothLocusY ∪ smoothLocusX = univ`. -/
noncomputable def affineChartAt (p : HyperellipticAffine H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ := by
  by_cases hpY : p ∈ smoothLocusY H
  · exact affineChartProjX p hpY
  · have hpY0 : p.val.2 = 0 := by
      simpa [smoothLocusY] using hpY
    exact affineChartProjY p (mem_smoothLocusX_of_y_eq_zero H hpY0)

@[simp] theorem affineChartAt_of_mem_smoothLocusY (p : HyperellipticAffine H)
    (hpY : p ∈ smoothLocusY H) :
    affineChartAt p = affineChartProjX p hpY := by
  simp [affineChartAt, hpY]

@[simp] theorem affineChartAt_of_not_mem_smoothLocusY (p : HyperellipticAffine H)
    (hpY : p ∉ smoothLocusY H) :
    affineChartAt p =
      affineChartProjY p
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)) := by
  simp [affineChartAt, hpY]

/-- **Affine `ChartedSpace` instance.** Combine the two chart families
above; `chartAt p` chooses `affineChartProjX p hp` if `p ∈ smoothLocusY`,
otherwise `affineChartProjY p hp`. -/
noncomputable instance affine_chartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (HyperellipticAffine H) where
  atlas := Set.range (affineChartAt (H := H))
  chartAt := affineChartAt (H := H)
  mem_chart_source p := by
    by_cases hpY : p ∈ smoothLocusY H
    · rw [affineChartAt_of_mem_smoothLocusY (H := H) p hpY]
      exact affineChartProjX_mem_source p hpY
    · rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpY]
      exact affineChartProjY_mem_source p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY))
  chart_mem_atlas p := ⟨p, rfl⟩

/-- Remaining OA1 compatibility boundary: `x`-chart followed by `x`-chart. -/
theorem affineChartProjX_compat_affineChartProjX
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) (hq : q ∈ smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjX p hp).symm.trans (affineChartProjX q hq)) : ℂ → ℂ)
      (((affineChartProjX p hp).symm.trans (affineChartProjX q hq)).source) := by
  let ep := affineChartProjX (H := H) p hp
  let eq := affineChartProjX (H := H) q hq
  exact ContDiffOn.congr
    (f := fun x : ℂ => x)
    (s := (ep.symm.trans eq).source)
    contDiffOn_id
    (by
      intro x hx
      have hx0 : x ∈ ep.target := hx.1
      change ep (ep.symm x) = x
      exact ep.right_inv hx0)

theorem affineChartProjX_trans_affineChartProjY_apply
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) (hq : q ∈ smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)).source)) :
    (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)) x) =
      (squareLocalHomeomorph (H := H) p hp).symm (H.f.eval x) := by
  have hx0 : x ∈ (affineChartProjX p hp).target := hx.1
  change (((affineChartProjX p hp).symm x : HyperellipticAffine H).val.2) =
    (squareLocalHomeomorph (H := H) p hp).symm (H.f.eval x)
  simpa using affineChartProjX_symm_apply_snd (H := H) p hp hx0

/-- The inverse branch for `y ↦ y²` chosen by `squareLocalHomeomorph` is smooth on its target. -/
theorem squareLocalHomeomorph_contDiffOn_symm (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) :
    ContDiffOn ℂ ω (squareLocalHomeomorph (H := H) p hp).symm
      (squareLocalHomeomorph (H := H) p hp).target := by
  let c : ℂ := p.val.2 * 2
  have hc : c ≠ 0 := by
    simpa [smoothLocusY, c] using mul_ne_zero hp (show (2 : ℂ) ≠ 0 by norm_num)
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    apply ContinuousLinearMap.ext
    intro z
    change (p.val.2 * 2) * z = z * (p.val.2 * 2)
    ring
  have hf' : HasFDerivAt (fun y : ℂ => y ^ 2) (e' : ℂ →L[ℂ] ℂ) p.val.2 := by
    simpa [hmap, c, pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_pow 2 p.val.2).hasFDerivAt
  have hf : ContDiffAt ℂ ω (fun y : ℂ => y ^ 2) p.val.2 := by
    simpa using (contDiffAt_id.pow 2 : ContDiffAt ℂ ω (fun y : ℂ => y ^ 2) p.val.2)
  simpa [squareLocalHomeomorph, c, e'] using
    (Jacobians.GeneralResults.contDiffOn_symm_toOpenPartialHomeomorph
      (f := fun y : ℂ => y ^ 2) (a := p.val.2) hf hf' (by simp))

/-- Remaining OA1 compatibility boundary: `x`-chart followed by `y`-chart. -/
theorem affineChartProjX_compat_affineChartProjY
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) (hq : q ∈ smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)) : ℂ → ℂ)
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)).source) := by
  let e := squareLocalHomeomorph (H := H) p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    squareLocalHomeomorph_contDiffOn_symm (H := H) p hp
  have hpoly : ContDiffOn ℂ ω (fun x : ℂ => H.f.eval x)
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)).source) :=
    (Polynomial.contDiff_aeval H.f ω).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => H.f.eval x)
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)).source) e.target := by
    intro x hx
    simpa [affineChartProjX, e] using hx.1
  refine ContDiffOn.congr (hsymm.comp hpoly hmaps) ?_
  intro x hx
  simpa [e] using affineChartProjX_trans_affineChartProjY_apply (H := H) p q hp hq hx

/-- Remaining OA1 compatibility boundary: `y`-chart followed by `x`-chart. -/
theorem affineChartProjY_trans_affineChartProjX_apply
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusX H) (hq : q ∈ smoothLocusY H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)).source)) :
    (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)) y) =
      (polynomialLocalHomeomorph (H := H) p hp).symm (y ^ 2) := by
  have hy0 : y ∈ (affineChartProjY p hp).target := hy.1
  change (((affineChartProjY p hp).symm y : HyperellipticAffine H).val.1) =
    (polynomialLocalHomeomorph (H := H) p hp).symm (y ^ 2)
  simpa using affineChartProjY_symm_apply_fst (H := H) p hp hy0

/-- The inverse branch for `x ↦ f(x)` chosen by `polynomialLocalHomeomorph` is smooth on
its target. -/
theorem polynomialLocalHomeomorph_contDiffOn_symm (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) :
    ContDiffOn ℂ ω (polynomialLocalHomeomorph (H := H) p hp).symm
      (polynomialLocalHomeomorph (H := H) p hp).target := by
  let c : ℂ := H.f.derivative.eval p.val.1
  have hc : c ≠ 0 := hp
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    apply ContinuousLinearMap.ext
    intro z
    simp [e', c, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hf' : HasFDerivAt (fun x : ℂ => H.f.eval x) (e' : ℂ →L[ℂ] ℂ) p.val.1 := by
    simpa [hmap] using (Polynomial.hasDerivAt H.f p.val.1).hasFDerivAt
  have hf : ContDiffAt ℂ ω (fun x : ℂ => H.f.eval x) p.val.1 := by
    simpa using (Polynomial.contDiff_aeval H.f ω).contDiffAt
  simpa [polynomialLocalHomeomorph, c, e'] using
    (Jacobians.GeneralResults.contDiffOn_symm_toOpenPartialHomeomorph
      (f := fun x : ℂ => H.f.eval x) (a := p.val.1) hf hf' (by simp))

/-- Remaining OA1 compatibility boundary: `y`-chart followed by `x`-chart. -/
theorem affineChartProjY_compat_affineChartProjX
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusX H) (hq : q ∈ smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)) : ℂ → ℂ)
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)).source) := by
  let e := polynomialLocalHomeomorph (H := H) p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    polynomialLocalHomeomorph_contDiffOn_symm (H := H) p hp
  have hsquare : ContDiffOn ℂ ω (fun y : ℂ => y ^ 2)
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)).source) :=
    (contDiff_id.pow 2).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => y ^ 2)
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)).source) e.target := by
    intro y hy
    simpa [affineChartProjY, e] using hy.1
  refine ContDiffOn.congr (hsymm.comp hsquare hmaps) ?_
  intro y hy
  simpa [e] using affineChartProjY_trans_affineChartProjX_apply (H := H) p q hp hq hy

/-- Remaining OA1 compatibility boundary: `y`-chart followed by `y`-chart. -/
theorem affineChartProjY_compat_affineChartProjY
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusX H) (hq : q ∈ smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjY p hp).symm.trans (affineChartProjY q hq)) : ℂ → ℂ)
      (((affineChartProjY p hp).symm.trans (affineChartProjY q hq)).source) := by
  let ep := affineChartProjY (H := H) p hp
  let eq := affineChartProjY (H := H) q hq
  exact ContDiffOn.congr
    (f := fun y : ℂ => y)
    (s := (ep.symm.trans eq).source)
    contDiffOn_id
    (by
      intro y hy
      have hy0 : y ∈ ep.target := hy.1
      change ep (ep.symm y) = y
      exact ep.right_inv hy0)

/-- Chart-transition compatibility for the chosen affine chart package. -/
theorem affineChartAt_compat (p q : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((affineChartAt (H := H) p).symm.trans (affineChartAt (H := H) q)) : ℂ → ℂ)
      (((affineChartAt (H := H) p).symm.trans (affineChartAt (H := H) q)).source) := by
  by_cases hpY : p ∈ smoothLocusY H
  · by_cases hqY : q ∈ smoothLocusY H
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjX_compat_affineChartProjX p q hpY hqY
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjX_compat_affineChartProjY p q hpY
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hqY))
  · by_cases hqY : q ∈ smoothLocusY H
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjY_compat_affineChartProjX p q
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)) hqY
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjY_compat_affineChartProjY p q
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY))
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hqY))

/-- Manifold structure on the affine odd hyperelliptic chart package,
assembled from the four chart-compatibility lemmas above. -/
noncomputable instance affine_isManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticAffine H) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
    affineChartAt_compat (H := H) p q

attribute [instance] affine_isManifold

end Jacobians.ProjectiveCurve.HyperellipticAffine
