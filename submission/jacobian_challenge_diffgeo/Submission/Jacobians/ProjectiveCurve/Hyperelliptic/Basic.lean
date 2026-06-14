/-
# Hyperelliptic curves: basic definitions

Shared definitions for hyperelliptic curves:

- `HyperellipticData`
- `HyperellipticAffine`
- subsidiary affine-chart axioms
- `HyperellipticOdd`

The even pushout construction lives in `Hyperelliptic/Even.lean`, and
the public wrapper file `Hyperelliptic.lean` imports both this file and
the even construction.
-/
import Submission.Jacobians.AbelianVariety.ComplexTorus
import Submission.Jacobians.RiemannSurface.Genus
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homotopy.Lifting

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- Data specifying a hyperelliptic curve: a squarefree polynomial
`f ∈ ℂ[x]` of degree at least 3. -/
structure HyperellipticData where
  /-- The defining polynomial `f` of the hyperelliptic curve `y² = f(x)`. -/
  f : Polynomial ℂ
  /-- Squarefree: the curve has no singularities over the roots of `f`. -/
  h_squarefree : Squarefree f
  /-- Degree `≥ 3` so the genus `g = ⌊(d-1)/2⌋` is positive. -/
  h_degree : 3 ≤ f.natDegree

namespace HyperellipticData

/-- The genus of a hyperelliptic curve: `g = ⌊(d - 1) / 2⌋`. -/
def genus (H : HyperellipticData) : ℕ := (H.f.natDegree - 1) / 2

/-- **Faithfulness witness** for `genus` (odd degree): for `deg f = 2g + 1`
the genus is exactly `g`. Guards the `(d - 1) / 2` formula against an
off-by-one. See `DEFINITIONS_AUDIT.md`. -/
theorem genus_eq_of_natDegree_eq_two_mul_add_one
    (H : HyperellipticData) (g : ℕ) (h : H.f.natDegree = 2 * g + 1) :
    H.genus = g := by
  unfold genus; rw [h]; omega

/-- **Faithfulness witness** for `genus` (even degree): for `deg f = 2g + 2`
the genus is exactly `g`. Together with the odd-degree witness this pins the
combinatorial genus formula on both parities. -/
theorem genus_eq_of_natDegree_eq_two_mul_add_two
    (H : HyperellipticData) (g : ℕ) (h : H.f.natDegree = 2 * g + 2) :
    H.genus = g := by
  unfold genus; rw [h]; omega

/-- The curve has a branch point at infinity iff `deg f` is odd. -/
def hasBranchAtInfinity (H : HyperellipticData) : Bool :=
  Odd H.f.natDegree

/-- **Faithfulness witness** for `hasBranchAtInfinity`: it is `true` exactly
when `deg f` is odd (pins the otherwise-unused predicate to its docstring). -/
theorem hasBranchAtInfinity_eq_true_iff (H : HyperellipticData) :
    H.hasBranchAtInfinity = true ↔ Odd H.f.natDegree := by
  simp [hasBranchAtInfinity]

end HyperellipticData

lemma reverse_eval_inv_eq {H : HyperellipticData}
    (x : ℂ) (hx : x ≠ 0) :
    (H.f.reverse).eval x⁻¹ = H.f.eval x * x⁻¹ ^ H.f.natDegree := by
  haveI := invertibleOfNonzero hx
  have key := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) x H.f
  have hinv : (⅟x : ℂ) = x⁻¹ := invOf_eq_inv x
  simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id, hinv] at key
  have hx_pow : (x ^ H.f.natDegree) ≠ 0 := pow_ne_zero _ hx
  have h2 : (H.f.eval x * x⁻¹ ^ H.f.natDegree) * x ^ H.f.natDegree = H.f.eval x := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]
  rw [← mul_right_cancel₀ hx_pow (key.trans h2.symm)]


/-- **Affine hyperelliptic curve**: the subtype `{(x, y) | y² = f(x)}`
of `ℂ × ℂ`. Closed in `ℂ × ℂ`, so it inherits topology, T2, and local
compactness. -/
def HyperellipticAffine (H : HyperellipticData) : Type :=
  { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 }

namespace HyperellipticAffine

variable {H : HyperellipticData}

instance : TopologicalSpace (HyperellipticAffine H) :=
  inferInstanceAs (TopologicalSpace { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 })

instance : T2Space (HyperellipticAffine H) :=
  inferInstanceAs (T2Space { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 })

/-- The affine locus is closed in `ℂ × ℂ` as the zero-set of
`(x, y) ↦ y² - f(x)`. -/
theorem isClosed_carrier (H : HyperellipticData) :
    IsClosed { p : ℂ × ℂ | p.2 ^ 2 = H.f.eval p.1 } := by
  have hcont : Continuous (fun p : ℂ × ℂ => p.2 ^ 2 - H.f.eval p.1) := by
    have h1 : Continuous (fun p : ℂ × ℂ => p.2 ^ 2) :=
      (continuous_snd).pow 2
    have h2 : Continuous (fun p : ℂ × ℂ => H.f.eval p.1) :=
      (Polynomial.continuous H.f).comp continuous_fst
    exact h1.sub h2
  have : { p : ℂ × ℂ | p.2 ^ 2 = H.f.eval p.1 } =
      { p : ℂ × ℂ | p.2 ^ 2 - H.f.eval p.1 = 0 } := by
    ext p
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_eq hcont continuous_const

instance : LocallyCompactSpace (HyperellipticAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- A witness: pick a root `a` of `f`, then `(a, 0)` lies on the affine
curve. -/
noncomputable instance : Nonempty (HyperellipticAffine H) := by
  have hnatDeg : 0 < H.f.natDegree := by
    have : 3 ≤ H.f.natDegree := H.h_degree
    omega
  have hf_ne : H.f ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hnatDeg
    omega
  have hdeg : 0 < H.f.degree := by
    rw [Polynomial.degree_eq_natDegree hf_ne]
    exact_mod_cast hnatDeg
  obtain ⟨a, ha⟩ := Complex.exists_root hdeg
  refine ⟨⟨(a, 0), ?_⟩⟩
  simp [Polynomial.IsRoot.def.mp ha]

/-- The finite branch locus of the affine hyperelliptic projection. -/
def roots (H : HyperellipticData) : Set ℂ :=
  H.f.rootSet ℂ

theorem roots_finite (H : HyperellipticData) : (roots H).Finite := by
  simpa [roots] using Polynomial.rootSet_finite H.f ℂ

theorem polynomial_ne_zero (H : HyperellipticData) : H.f ≠ 0 := by
  intro h
  have hdeg := H.h_degree
  simp_all

theorem mem_roots_iff_eval_eq_zero (H : HyperellipticData) {x : ℂ} :
    x ∈ roots H ↔ H.f.eval x = 0 := by
  simpa [roots, Polynomial.aeval_def] using
    Polynomial.mem_rootSet_of_ne (p := H.f) (S := ℂ) (polynomial_ne_zero H) (a := x)

theorem roots_countable (H : HyperellipticData) : (roots H).Countable :=
  (roots_finite H).countable

theorem root_compl_pathConnected (H : HyperellipticData) : IsPathConnected (roots H)ᶜ := by
  exact (roots_countable H).isPathConnected_compl_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)

noncomputable def sqMap : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} :=
  fun z => ⟨(z : ℂ) ^ 2, pow_ne_zero 2 z.2⟩

theorem sqMap_covering : IsCoveringMap sqMap := by
  simpa [sqMap] using (isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num : (2 : ℂ) ≠ 0))

theorem y_ne_zero_base_mem {p : HyperellipticAffine H} (hp : p.val.2 ≠ 0) :
    p.val.1 ∈ (roots H)ᶜ := by
  rw [Set.mem_compl_iff, mem_roots_iff_eval_eq_zero]
  grind

theorem lift_joined_to_target_fiber {p q : HyperellipticAffine H}
    (hp : p.val.2 ≠ 0) (hbase : JoinedIn (roots H)ᶜ p.val.1 q.val.1) :
    ∃ r : HyperellipticAffine H,
      r.val.1 = q.val.1 ∧ r.val.2 ^ 2 = q.val.2 ^ 2 ∧ Joined p r := by
  let γpath := hbase.somePath
  let γbase : C(unitInterval, {z : ℂ // z ∈ (roots H)ᶜ}) :=
    ⟨fun t => ⟨γpath t, hbase.somePath_mem t⟩,
      γpath.continuous.subtype_mk (fun t => hbase.somePath_mem t)⟩
  let γf : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨H.f.eval (γbase t : ℂ), by
        have hz : (γbase t : ℂ) ∉ roots H := (γbase t).property
        rwa [mem_roots_iff_eval_eq_zero] at hz⟩,
      ((Polynomial.continuous H.f).comp
          (continuous_subtype_val.comp γbase.continuous)).subtype_mk (by
        intro t
        have hz : (γbase t : ℂ) ∉ roots H := (γbase t).property
        rwa [mem_roots_iff_eval_eq_zero] at hz)⟩
  let y0 : {z : ℂ // z ≠ 0} := ⟨p.val.2, hp⟩
  have h0 : γf 0 = sqMap y0 := by
    apply Subtype.ext
    change H.f.eval (γbase 0 : ℂ) = p.val.2 ^ 2
    have hγ0 : γpath 0 = p.val.1 := γpath.source'
    simpa [γbase, γf, y0, sqMap, hγ0] using p.property.symm
  let η := sqMap_covering.liftPath γf y0 h0
  let r : HyperellipticAffine H := ⟨(q.val.1, (η 1 : ℂ)), by
    have hl := congr_fun (sqMap_covering.liftPath_lifts γf y0 h0) 1
    have hγ1 : γpath 1 = q.val.1 := γpath.target'
    have hη : ((η 1 : {z : ℂ // z ≠ 0}) : ℂ) ^ 2 = H.f.eval q.val.1 := by
      simpa [Function.comp_apply, sqMap, γf, γbase, hγ1] using congrArg Subtype.val hl
    grind⟩
  refine ⟨r, rfl, ?_, ?_⟩
  · have hl := congr_fun (sqMap_covering.liftPath_lifts γf y0 h0) 1
    have hγ1 : γpath 1 = q.val.1 := γpath.target'
    have hη : ((η 1 : {z : ℂ // z ≠ 0}) : ℂ) ^ 2 = H.f.eval q.val.1 := by
      simpa [Function.comp_apply, sqMap, γf, γbase, hγ1] using congrArg Subtype.val hl
    grind
  · refine ⟨Path.mk ?_ ?_ ?_⟩
    · refine ⟨fun t => ⟨((γbase t : ℂ), (η t : ℂ)), ?_⟩, ?_⟩
      · have hl := congr_fun (sqMap_covering.liftPath_lifts γf y0 h0) t
        simpa [Function.comp_apply, sqMap, γf, γbase] using congrArg Subtype.val hl
      · exact (Continuous.prodMk (continuous_subtype_val.comp γbase.continuous)
          (continuous_subtype_val.comp η.continuous)).subtype_mk (by
          intro t
          have hl := congr_fun (sqMap_covering.liftPath_lifts γf y0 h0) t
          simpa [Function.comp_apply, sqMap, γf, γbase] using congrArg Subtype.val hl)
    · apply Subtype.ext
      have hη0 := sqMap_covering.liftPath_zero γf y0 h0
      exact Prod.ext γpath.source' (by grind)
    · apply Subtype.ext
      exact Prod.ext γpath.target' rfl

/-- If `x` is a root of the squarefree defining polynomial `f`, then `f'(x) ≠ 0`. -/
theorem branch_eval_derivative_ne_zero_of_eval_eq_zero (H : HyperellipticData) {x : ℂ}
    (hx : H.f.eval x = 0) : H.f.derivative.eval x ≠ 0 := by
  intro hder
  have hf_ne' : H.f ≠ 0 := polynomial_ne_zero H
  have hroot : H.f.IsRoot x := Polynomial.IsRoot.def.mpr hx
  have hrootder : H.f.derivative.IsRoot x := Polynomial.IsRoot.def.mpr hder
  have hmult : 1 < H.f.rootMultiplicity x := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hf_ne']
    simp_all
  have hsq_dvd : (Polynomial.X - Polynomial.C x) ^ 2 ∣ H.f := by
    rw [← Polynomial.le_rootMultiplicity_iff hf_ne']
    grind
  have hsq_dvd' : (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C x) ∣ H.f := by
    simpa [pow_two] using hsq_dvd
  have hirr : Irreducible (Polynomial.X - Polynomial.C x : Polynomial ℂ) :=
    Polynomial.irreducible_X_sub_C x
  have hsqfree :=
    (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hf_ne').1 H.h_squarefree
  simp_all

noncomputable def branchPolynomialLocalHomeomorph (p : HyperellipticAffine H)
    (hp : H.f.derivative.eval p.val.1 ≠ 0) : OpenPartialHomeomorph ℂ ℂ := by
  let c : ℂ := H.f.derivative.eval p.val.1
  have hc : c ≠ 0 := hp
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hmap : ((e' : ℂ →L[ℂ] ℂ)) = ContinuousLinearMap.toSpanSingleton ℂ c := by
    ext
    simp [e', c, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hfder : HasFDerivAt (fun x : ℂ => H.f.eval x) (e' : ℂ →L[ℂ] ℂ) p.val.1 := by
    simpa [hmap] using (Polynomial.hasDerivAt H.f p.val.1).hasFDerivAt
  exact (Polynomial.contDiff_aeval H.f ω).contDiffAt.toOpenPartialHomeomorph
    (fun x : ℂ => H.f.eval x) hfder (by simp)

theorem branchPolynomialLocalHomeomorph_mem_source (p : HyperellipticAffine H)
    (hp : H.f.derivative.eval p.val.1 ≠ 0) :
    p.val.1 ∈ (branchPolynomialLocalHomeomorph (H := H) p hp).source := by
  let e := branchPolynomialLocalHomeomorph (H := H) p hp
  change p.val.1 ∈ e.source
  dsimp [e, branchPolynomialLocalHomeomorph]
  let c : ℂ := H.f.derivative.eval p.val.1
  have hc : c ≠ 0 := hp
  let e' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hfder : HasFDerivAt (fun x : ℂ => H.f.eval x) (e' : ℂ →L[ℂ] ℂ) p.val.1 := by
    convert (Polynomial.hasDerivAt H.f p.val.1).hasFDerivAt using 1
    ext
    simp [e', c, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  exact ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((Polynomial.contDiff_aeval H.f ω).contDiffAt) (hf' := hfder) (hn := by simp)

theorem branch_zero_target_mem {p : HyperellipticAffine H} (hp0 : p.val.2 = 0)
    (hpder : H.f.derivative.eval p.val.1 ≠ 0) :
    (0 : ℂ) ∈ (branchPolynomialLocalHomeomorph (H := H) p hpder).target := by
  let e := branchPolynomialLocalHomeomorph (H := H) p hpder
  have hsrc : p.val.1 ∈ e.source := branchPolynomialLocalHomeomorph_mem_source (H := H) p hpder
  have hmap := e.map_source hsrc
  have hval : H.f.eval p.val.1 = 0 := by grind
  simpa [e, branchPolynomialLocalHomeomorph, hval] using hmap

theorem exists_small_branch_parameter {p : HyperellipticAffine H} (hp0 : p.val.2 = 0)
    (hpder : H.f.derivative.eval p.val.1 ≠ 0) :
    ∃ y : ℂ, y ≠ 0 ∧ ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * y) ^ 2 ∈ (branchPolynomialLocalHomeomorph (H := H) p hpder).target := by
  let e := branchPolynomialLocalHomeomorph (H := H) p hpder
  have h0 : (0 : ℂ) ∈ e.target := branch_zero_target_mem (H := H) hp0 hpder
  rcases Metric.isOpen_iff.mp e.open_target 0 h0 with ⟨r, hrpos, hrsub⟩
  let δ : ℝ := min r 1 / 2
  have hδpos : 0 < δ := by grind
  refine ⟨(δ : ℂ), by exact_mod_cast hδpos.ne', ?_⟩
  intro t
  apply hrsub
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  have ht : ‖(((t : ℝ) : ℂ))‖ ≤ 1 := by
    have ht01 : 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 := t.2
    rw [Complex.norm_real, Real.norm_of_nonneg ht01.1]
    simp_all
  have hnorm : ‖(((t : ℝ) : ℂ) * (δ : ℂ)) ^ 2‖ =
      (‖(((t : ℝ) : ℂ))‖ * δ) ^ 2 := by
    simp [norm_pow, Complex.norm_real, Real.norm_of_nonneg hδpos.le]
  rw [hnorm]
  have hδle1 : δ ≤ 1 := by grind
  have hδltr : δ < r := by grind
  have hmul_le : ‖(((t : ℝ) : ℂ))‖ * δ ≤ δ := by simp_all
  have hmul_nonneg : 0 ≤ ‖(((t : ℝ) : ℂ))‖ * δ := mul_nonneg (norm_nonneg _) hδpos.le
  nlinarith

theorem branch_joined_parameter {p : HyperellipticAffine H} (hp0 : p.val.2 = 0)
    (hpder : H.f.derivative.eval p.val.1 ≠ 0) {y : ℂ}
    (hstay : ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * y) ^ 2 ∈ (branchPolynomialLocalHomeomorph (H := H) p hpder).target) :
    let e := branchPolynomialLocalHomeomorph (H := H) p hpder
    let q : HyperellipticAffine H := ⟨(e.symm (y ^ 2), y), by
      have hy : y ^ 2 ∈ e.target := by simpa using hstay 1
      change y ^ 2 = H.f.eval (e.symm (y ^ 2))
      simpa [e] using (e.right_inv hy).symm⟩
    Joined p q := by
  intro e q
  refine ⟨Path.mk ?_ ?_ ?_⟩
  · refine ⟨fun t => ⟨(e.symm ((((t : ℝ) : ℂ) * y) ^ 2), ((t : ℝ) : ℂ) * y), ?_⟩, ?_⟩
    · have ht : (((t : ℝ) : ℂ) * y) ^ 2 ∈ e.target := by grind
      change (((t : ℝ) : ℂ) * y) ^ 2 = H.f.eval (e.symm ((((t : ℝ) : ℂ) * y) ^ 2))
      simpa [e] using (e.right_inv ht).symm
    · apply Continuous.subtype_mk
      apply Continuous.prodMk
      · have harg : Continuous fun t : unitInterval => (((t : ℝ) : ℂ) * y) ^ 2 := by
          exact ((Complex.continuous_ofReal.comp
            (continuous_subtype_val : Continuous fun t : unitInterval => (t : ℝ))).mul
              continuous_const).pow 2
        exact e.continuousOn_symm.comp_continuous harg (by intro t; grind)
      · exact (Complex.continuous_ofReal.comp
          (continuous_subtype_val : Continuous fun t : unitInterval => (t : ℝ))).mul
            continuous_const
  · apply Subtype.ext
    have hsrc : p.val.1 ∈ e.source := by
      simpa [e] using branchPolynomialLocalHomeomorph_mem_source (H := H) p hpder
    have hleft : e.symm (0 : ℂ) = p.val.1 := by
      have hmap : e p.val.1 = 0 := by
        have hp_eval : H.f.eval p.val.1 = 0 := by grind
        simp [e, branchPolynomialLocalHomeomorph, hp_eval]
      simpa [hmap] using e.left_inv hsrc
    exact Prod.ext (by simpa using hleft) (by simpa using hp0.symm)
  · apply Subtype.ext
    exact Prod.ext (by simp [q]) (by simp [q])

theorem exists_branch_nearby_joined {p : HyperellipticAffine H} (hp0 : p.val.2 = 0) :
    ∃ q : HyperellipticAffine H, q.val.2 ≠ 0 ∧ Joined p q := by
  have hp_eval : H.f.eval p.val.1 = 0 := by grind
  have hpder : H.f.derivative.eval p.val.1 ≠ 0 :=
    branch_eval_derivative_ne_zero_of_eval_eq_zero H hp_eval
  rcases exists_small_branch_parameter (H := H) hp0 hpder with ⟨y, hyne, hstay⟩
  let e := branchPolynomialLocalHomeomorph (H := H) p hpder
  let q : HyperellipticAffine H := ⟨(e.symm (y ^ 2), y), by
    have hy : y ^ 2 ∈ e.target := by simpa using hstay 1
    change y ^ 2 = H.f.eval (e.symm (y ^ 2))
    simpa [e] using (e.right_inv hy).symm⟩
  refine ⟨q, by grind, ?_⟩
  simpa [q, e] using branch_joined_parameter (H := H) hp0 hpder hstay

theorem branch_fiber_joined {p : HyperellipticAffine H} (hp0 : p.val.2 = 0)
    (hpder : H.f.derivative.eval p.val.1 ≠ 0) {y : ℂ}
    (hstay : ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * y) ^ 2 ∈ (branchPolynomialLocalHomeomorph (H := H) p hpder).target)
    {r : HyperellipticAffine H}
    (hrx : r.val.1 = (branchPolynomialLocalHomeomorph (H := H) p hpder).symm (y ^ 2))
    (hry : r.val.2 ^ 2 = y ^ 2) : Joined p r := by
  let e := branchPolynomialLocalHomeomorph (H := H) p hpder
  let qPlus : HyperellipticAffine H := ⟨(e.symm (y ^ 2), y), by
    grind⟩
  have hplus : Joined p qPlus := by
    simpa [qPlus, e] using branch_joined_parameter (H := H) hp0 hpder hstay
  have hstayNeg : ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * (-y)) ^ 2 ∈ e.target := by
    intro t
    grind
  let qMinus : HyperellipticAffine H := ⟨(e.symm ((-y) ^ 2), -y), by
    grind⟩
  have hminus : Joined p qMinus := by
    simpa [qMinus, e] using branch_joined_parameter (H := H) hp0 hpder hstayNeg
  rcases eq_or_eq_neg_of_sq_eq_sq r.val.2 y hry with hy' | hy'
  · convert hplus using 1
    apply Subtype.ext
    grind
  · convert hminus using 1
    apply Subtype.ext
    grind

theorem exists_branch_point (H : HyperellipticData) :
    ∃ p : HyperellipticAffine H, p.val.2 = 0 := by
  have hnatDeg : 0 < H.f.natDegree := lt_of_lt_of_le (by norm_num : 0 < 3) H.h_degree
  have hf_ne' : H.f ≠ 0 := polynomial_ne_zero H
  have hdeg : 0 < H.f.degree := by
    rw [Polynomial.degree_eq_natDegree hf_ne']
    simp_all
  obtain ⟨a, ha⟩ := Complex.exists_root hdeg
  refine ⟨⟨(a, 0), ?_⟩, rfl⟩
  simp [Polynomial.IsRoot.def.mp ha]

theorem nonbranch_joined_to_hub (hub : HyperellipticAffine H) (hhub0 : hub.val.2 = 0)
    (hhubder : H.f.derivative.eval hub.val.1 ≠ 0) {y : ℂ} (hyne : y ≠ 0)
    (hstay : ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * y) ^ 2 ∈ (branchPolynomialLocalHomeomorph (H := H) hub hhubder).target)
    (p : HyperellipticAffine H) (hp_ne : p.val.2 ≠ 0) : Joined p hub := by
  let e := branchPolynomialLocalHomeomorph (H := H) hub hhubder
  let b : HyperellipticAffine H := ⟨(e.symm (y ^ 2), y), by
    have hy : y ^ 2 ∈ e.target := by simpa [e] using hstay 1
    change y ^ 2 = H.f.eval (e.symm (y ^ 2))
    simpa [e] using (e.right_inv hy).symm⟩
  have hb_ne : b.val.2 ≠ 0 := by grind
  have hbase : JoinedIn (roots H)ᶜ p.val.1 b.val.1 :=
    (root_compl_pathConnected H).joinedIn p.val.1 (y_ne_zero_base_mem (H := H) hp_ne)
      b.val.1 (y_ne_zero_base_mem (H := H) hb_ne)
  rcases lift_joined_to_target_fiber (H := H) hp_ne hbase with ⟨r, hrx, hry, hpr⟩
  have hhubr : Joined hub r := by
    apply branch_fiber_joined (H := H) hhub0 hhubder hstay <;> grind
  exact hpr.trans hhubr.symm

theorem joined_to_chosen_hub (hub : HyperellipticAffine H) (hhub0 : hub.val.2 = 0)
    (hhubder : H.f.derivative.eval hub.val.1 ≠ 0) {y : ℂ} (hyne : y ≠ 0)
    (hstay : ∀ t : unitInterval,
      (((t : ℝ) : ℂ) * y) ^ 2 ∈ (branchPolynomialLocalHomeomorph (H := H) hub hhubder).target)
    (p : HyperellipticAffine H) : Joined p hub := by
  by_cases hp0 : p.val.2 = 0
  · rcases exists_branch_nearby_joined (H := H) hp0 with ⟨q, hq_ne, hpq⟩
    exact hpq.trans (nonbranch_joined_to_hub (H := H) hub hhub0 hhubder hyne hstay q hq_ne)
  · exact nonbranch_joined_to_hub (H := H) hub hhub0 hhubder hyne hstay p hp0

theorem pathConnectedSpace (H : HyperellipticData) :
    PathConnectedSpace (HyperellipticAffine H) := by
  rcases exists_branch_point H with ⟨hub, hhub0⟩
  have hhub_eval : H.f.eval hub.val.1 = 0 := by grind
  have hhubder : H.f.derivative.eval hub.val.1 ≠ 0 :=
    branch_eval_derivative_ne_zero_of_eval_eq_zero H hhub_eval
  rcases exists_small_branch_parameter (H := H) hhub0 hhubder with ⟨y, hyne, hstay⟩
  refine ⟨⟨hub⟩, ?_⟩
  intro p q
  exact (joined_to_chosen_hub (H := H) hub hhub0 hhubder hyne hstay p).trans
    (joined_to_chosen_hub (H := H) hub hhub0 hhubder hyne hstay q).symm

/-- The affine hyperelliptic curve is connected. -/
instance AX_HyperellipticAffine_connected (H : HyperellipticData) :
    ConnectedSpace (HyperellipticAffine H) := by
  letI : PathConnectedSpace (HyperellipticAffine H) := pathConnectedSpace H
  infer_instance

/-- **Axiom (NOT VERIFIED).** The affine hyperelliptic curve is
noncompact. -/
instance : NoncompactSpace (HyperellipticAffine H) := by
  refine ⟨?_⟩
  intro hcompact
  let π : HyperellipticAffine H → ℂ := fun p => p.val.1
  have hπ : Continuous π := continuous_subtype_val.fst
  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨y, hy⟩ : ∃ y : ℂ, H.f.eval x = y * y :=
      (Complex.isSquare (H.f.eval x)).exists_mul_self
    refine ⟨⟨(x, y), ?_⟩, rfl⟩
    simp [sq, hy]
  have himage : π '' (Set.univ : Set (HyperellipticAffine H)) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hsurj x with ⟨p, rfl⟩
      exact ⟨p, Set.mem_univ _, rfl⟩
  have hcompactC : IsCompact (Set.univ : Set ℂ) := by
    simpa [himage] using hcompact.image hπ
  exact (inferInstance : NoncompactSpace ℂ).noncompact_univ hcompactC

end HyperellipticAffine

def HyperellipticOdd (H : HyperellipticData) (_h : Odd H.f.natDegree) : Type :=
  OnePoint (HyperellipticAffine H)


namespace HyperellipticOdd

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

instance : TopologicalSpace (HyperellipticOdd H h) :=
  inferInstanceAs (TopologicalSpace (OnePoint (HyperellipticAffine H)))

instance : T2Space (HyperellipticOdd H h) :=
  inferInstanceAs (T2Space (OnePoint (HyperellipticAffine H)))

instance : CompactSpace (HyperellipticOdd H h) :=
  inferInstanceAs (CompactSpace (OnePoint (HyperellipticAffine H)))

instance : Nonempty (HyperellipticOdd H h) :=
  inferInstanceAs (Nonempty (OnePoint (HyperellipticAffine H)))

instance : ConnectedSpace (HyperellipticOdd H h) :=
  inferInstanceAs (ConnectedSpace (OnePoint (HyperellipticAffine H)))

/-- Coercion from affine points to the odd projective curve. -/
def coe (a : HyperellipticAffine H) : HyperellipticOdd H h := OnePoint.some a

/-- The point at infinity on the odd projective curve. -/
def infty : HyperellipticOdd H h := OnePoint.infty

instance : Coe (HyperellipticAffine H) (HyperellipticOdd H h) where
  coe := coe

end HyperellipticOdd

end Jacobians.ProjectiveCurve
