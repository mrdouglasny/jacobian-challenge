/-
# Phase OA2 — Chart at infinity on `HyperellipticOdd H h`

In the odd-degree case `deg f = 2g + 1`, the smooth model
`HyperellipticOdd H h := OnePoint (HyperellipticAffine H)` has a single
point at infinity, which is also a **branch point** of the
hyperelliptic projection `(x, y) ↦ x`.

The standard chart at infinity uses the uniformizer `t := y / x^{g+1}`.
Near `t = 0`, on the curve `y² = f(x)` with `deg f = 2g + 1`:
* `x = 1 / (lc(f) · t²) · (1 + O(t))` (where `lc(f)` is the leading
  coefficient);
* `y = 1 / (lc(f)^{(2g+1)/2} · t^{2g+1}) · (1 + O(t))`.

So the inverse `t ↦ (x(t), y(t))` is an analytic bijection from a
punctured disk `0 < |t| < ε` onto a punctured neighborhood of `∞`,
extending continuously by `t = 0 ↦ OnePoint.infty`.

## Mathlib API

* `OnePoint.openEmbedding_coe : OpenEmbedding ((↑) : X → OnePoint X)` —
  affine charts pull back to `OnePoint X` for points coming from `X`.
* `OnePoint.continuous_iff_continuousAt_infty` — for verifying
  continuity at `∞`.
* No general "chart at the added point" lemma in Mathlib; we construct
  the `PartialHomeomorph` by hand.

See `docs/hyperelliptic-odd-atlas-plan.md` §OA2.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff Topology
open OnePoint

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

private noncomputable def infinityRootPolynomial (H : HyperellipticData) (t : ℂ) :
    Polynomial ℂ :=
  Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) - H.f

private theorem infinityRootPolynomial_degree_pos (H : HyperellipticData) {t : ℂ}
    (ht : t ≠ 0) : 0 < (infinityRootPolynomial H t).degree := by
  classical
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hterm_nat :
      (Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) : Polynomial ℂ).natDegree =
        H.f.natDegree + 1 := by
    simpa using Polynomial.natDegree_C_mul_X_pow (R := ℂ)
      (H.f.natDegree + 1) (t ^ 2) ht2
  have hlt :
      H.f.natDegree <
        (Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) :
          Polynomial ℂ).natDegree := by
    calc
      H.f.natDegree < H.f.natDegree + 1 := Nat.lt_succ_self _
      _ =
          (Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) :
            Polynomial ℂ).natDegree := hterm_nat.symm
  have hpoly_nat : (infinityRootPolynomial H t).natDegree = H.f.natDegree + 1 := by
    unfold infinityRootPolynomial
    calc
      (Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) - H.f :
          Polynomial ℂ).natDegree =
          (Polynomial.C (t ^ 2) * Polynomial.X ^ (H.f.natDegree + 1) :
            Polynomial ℂ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
      _ = H.f.natDegree + 1 := hterm_nat
  rw [← Polynomial.natDegree_pos_iff_degree_pos]
  rw [hpoly_nat]
  exact Nat.succ_pos _

private theorem infinityRootPolynomial_exists_root (H : HyperellipticData) {t : ℂ}
    (ht : t ≠ 0) : ∃ x : ℂ, (infinityRootPolynomial H t).eval x = 0 := by
  obtain ⟨x, hx⟩ := Complex.exists_root (infinityRootPolynomial_degree_pos H ht)
  exact ⟨x, Polynomial.IsRoot.def.mp hx⟩

private noncomputable def infinityInverseX (H : HyperellipticData) (t : ℂ) : ℂ :=
  if ht : t = 0 then
    (Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))).val.1
  else
    Classical.choose (infinityRootPolynomial_exists_root H ht)

private theorem infinityInverseX_spec (H : HyperellipticData) {t : ℂ} (ht : t ≠ 0) :
    (infinityRootPolynomial H t).eval (infinityInverseX H t) = 0 := by
  unfold infinityInverseX
  rw [dif_neg ht]
  exact Classical.choose_spec (infinityRootPolynomial_exists_root H ht)

private theorem odd_natDegree_add_one_eq_two_mul_genus_add_one
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    H.f.natDegree + 1 = 2 * (H.genus + 1) := by
  unfold HyperellipticData.genus
  have hodd := Nat.two_mul_div_two_add_one_of_odd h
  omega

/-- The local inverse `t ↦ (x(t), y(t))` on a punctured disk near
`t = 0`, mapping into `HyperellipticAffine H`. Concretely, with
`g := (deg f - 1) / 2`, we have `x = 1/t²·(1 + O(t))` and
`y = 1/t^{2g+1}·(1 + O(t))` after normalizing by `lc(f)`. Domain:
`{ t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < someRadius }`. -/
noncomputable def infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ℂ → HyperellipticAffine H := fun t => by
  by_cases ht : t = 0
  · exact Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))
  · let x : ℂ := infinityInverseX H t
    refine ⟨(x, t * x ^ (H.genus + 1)), ?_⟩
    have hroot := infinityInverseX_spec H ht
    have hEval : t ^ 2 * x ^ (H.f.natDegree + 1) = H.f.eval x := by
      have hroot' : t ^ 2 * x ^ (H.f.natDegree + 1) - H.f.eval x = 0 := by
        simpa [infinityRootPolynomial, x] using hroot
      exact sub_eq_zero.mp hroot'
    calc
      (t * x ^ (H.genus + 1)) ^ 2 = t ^ 2 * x ^ (2 * (H.genus + 1)) := by ring
      _ = t ^ 2 * x ^ (H.f.natDegree + 1) := by
        rw [odd_natDegree_add_one_eq_two_mul_genus_add_one H h]
      _ = H.f.eval x := hEval

/-- Forward infinity coordinate: `∞ ↦ 0` and `(x, y) ↦ y / x^(g+1)` on the
affine locus. -/
noncomputable def infinityForward (H : HyperellipticData) (h : Odd H.f.natDegree) :
    HyperellipticOdd H h → ℂ :=
  OnePoint.rec 0 fun p : HyperellipticAffine H => p.val.2 / p.val.1 ^ (H.genus + 1)

/-- Backward infinity coordinate as a total map: `0 ↦ ∞`, and nonzero values use
the algebraic inverse map into the affine locus. -/
noncomputable def infinityBackward (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ℂ → HyperellipticOdd H h := fun t =>
  if t = 0 then
    ∞
  else
    ((infinityInverseMap H h t : HyperellipticAffine H) : OnePoint (HyperellipticAffine H))

/-- The chart at infinity: `PartialHomeomorph (HyperellipticOdd H h) ℂ`
sending a neighborhood of `OnePoint.infty` to a neighborhood of
`0 ∈ ℂ`, with `OnePoint.infty ↦ 0`.

The forward map (going `HyperellipticOdd → ℂ`) is `(x, y) ↦ y / x^{g+1}`
on the affine part where `x ≠ 0`, extended by `infty ↦ 0`. The inverse
map is `infinityInverseMap` extended by `0 ↦ infty`. -/
-- TODO: replace this axiom with the analytic branch of `infinityInverseMap`
-- near `t = 0` and the cocompact continuity proof for the forward coordinate.
axiom infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) :
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ

/-- The infinity chart is defined at the point `∞`. -/
-- TODO: immediate once `infinityChart.source` is the intended neighborhood of `∞`.
axiom infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `x`-chart. -/
-- TODO: needs the analytic branch/formula API for `infinityChart.symm` on a punctured disk.
axiom infinityChart_compat_affineLiftProjX
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source

/-- Remaining OA2 local boundary: the lifted affine `x`-chart followed by the infinity chart. -/
-- TODO: needs the explicit forward formula `p ↦ y / x^(g+1)` and source exclusion `x ≠ 0`.
axiom affineLiftProjX_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `y`-chart. -/
-- TODO: needs the analytic branch/formula API for the `y(t)` coordinate on a punctured disk.
axiom infinityChart_compat_affineLiftProjY
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source

/-- Remaining OA2 local boundary: the lifted affine `y`-chart followed by the infinity chart. -/
-- TODO: needs the explicit forward formula on the affine branch-point chart overlap.
axiom affineLiftProjY_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source

end Jacobians.ProjectiveCurve.HyperellipticOdd
