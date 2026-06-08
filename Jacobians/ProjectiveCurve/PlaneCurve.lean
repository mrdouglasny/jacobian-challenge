/-
# Smooth projective plane curves

A smooth projective plane curve is `X = {[x : y : z] ∈ ℙ² | F(x, y, z) = 0}`
where `F ∈ ℂ[x, y, z]` is a homogeneous polynomial of degree `d ≥ 1`
whose gradient `∇F` has no common zero with `F` on `ℂ³ \ {0}` (smoothness).

**Genus.** For smooth `X` of degree `d ≥ 3`: `g = (d - 1)(d - 2) / 2`
(Plücker formula). For `d = 1` (line) or `d = 2` (conic): `g = 0`.

## Scope of this module (refactored 2026-04-23)

- `HomogeneousPoly n d`: a homogeneous polynomial of degree `d` in
  `n + 1` variables.
- `PlaneCurveData`: `F` with smoothness + `deg F ≥ 1` hypotheses.
- `PlaneCurveAffine`: the affine patch `{F(x, y, 1) = 0}` in `ℂ²`.
- **`PlaneCurve H := OnePoint (PlaneCurveAffine H)`** — real `def` via
  one-point compactification (2026-04-23). This glues the points at
  infinity (where `z = 0`) into a single point, which is correct when
  `X ∩ {z = 0}` is a single projective point, lossy otherwise (the
  atlas work needs to handle this case properly).
- Topology / T2 / compact / connected / nonempty instances are real
  `instance`s via OnePoint infrastructure (+ subsidiary axioms for
  affine-level connectedness and noncompactness).
- `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` stay **axiomatic** (atlas
  construction; classical but nontrivial).
-/
import Mathlib

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- A homogeneous polynomial of degree `d` in `n + 1` variables over `ℂ`. -/
structure HomogeneousPoly (n d : ℕ) where
  /-- The underlying polynomial in `(Fin (n + 1))`-indexed variables. -/
  val : MvPolynomial (Fin (n + 1)) ℂ
  /-- Homogeneity of degree `d`. -/
  homogeneous : val.IsHomogeneous d

/-- Data specifying a smooth projective plane curve `{F = 0} ⊂ ℙ²`. -/
structure PlaneCurveData where
  /-- Degree of the defining polynomial, `≥ 1`. -/
  d : ℕ
  h_deg : 1 ≤ d
  /-- The defining homogeneous polynomial `F ∈ ℂ[x, y, z]` of degree `d`. -/
  F : HomogeneousPoly 2 d
  /-- Smoothness: on `ℂ³ \ {0}`, `F = 0` implies some partial derivative
  is nonzero. -/
  h_smooth : ∀ v : Fin 3 → ℂ, v ≠ 0 → F.val.eval v = 0 →
    (∃ i : Fin 3, (MvPolynomial.pderiv i F.val).eval v ≠ 0)
  /-- Irreducibility: `{F = 0}` is an irreducible curve — the standard meaning of
  a "smooth plane curve". Rules out reducible loci (e.g. `F = xy`, two lines)
  whose affine patch can be disconnected. -/
  h_irreducible : Irreducible F.val
  /-- The curve is **not** the line at infinity `{z = 0}` (equivalently `z ∤ F`).
  Together with irreducibility this guarantees the `z = 1` affine patch is
  nonempty, connected, and noncompact — closing the `F = z` soundness hole
  (where the patch is empty). The third variable `z` is `MvPolynomial.X 2`. -/
  h_not_at_infinity : ¬ (MvPolynomial.X (2 : Fin 3) ∣ F.val)

namespace PlaneCurveData

/-- The genus of a smooth projective plane curve of degree `d`:
`g = (d - 1)(d - 2) / 2` (Plücker). -/
def genus (H : PlaneCurveData) : ℕ := (H.d - 1) * (H.d - 2) / 2

end PlaneCurveData

/-- **Affine plane curve**: the subtype of `ℂ²` cut out by the
dehomogenization `F(x, y, 1) = 0`. -/
def PlaneCurveAffine (H : PlaneCurveData) : Type :=
  { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 }

namespace PlaneCurveAffine

variable {H : PlaneCurveData}

instance : TopologicalSpace (PlaneCurveAffine H) :=
  inferInstanceAs (TopologicalSpace
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

instance : T2Space (PlaneCurveAffine H) :=
  inferInstanceAs (T2Space
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

/-- The affine locus is closed: preimage of `0` under the continuous
map `(x, y) ↦ F(x, y, 1)`. -/
theorem isClosed_carrier (H : PlaneCurveData) :
    IsClosed { p : ℂ × ℂ | H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 } := by
  have hcont : Continuous (fun p : ℂ × ℂ =>
      H.F.val.eval ![p.1, p.2, (1 : ℂ)]) := by
    have hvec : Continuous (fun p : ℂ × ℂ => (![p.1, p.2, (1 : ℂ)] : Fin 3 → ℂ)) := by
      refine continuous_pi (fun i => ?_)
      fin_cases i
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_const
    exact (MvPolynomial.continuous_eval H.F.val).comp hvec
  exact isClosed_eq hcont continuous_const

/-- Local compactness inherited via the closed-subtype route. -/
instance : LocallyCompactSpace (PlaneCurveAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### The affine-patch axiom layer — soundness restored 2026-06-04

These three axioms were **false as stated** for a curve lying in the line at
infinity `z = 0` (e.g. `F = z`: the `z = 1` patch `{F(x,y,1)=0} = ∅`, which is not
nonempty, not connected, and — being compact — not noncompact). That hole is now
closed at the **data** level: `PlaneCurveData` carries `h_irreducible` and
`h_not_at_infinity` (`z ∤ F`). For irreducible `F` with `z ∤ F` the curve is not
the line at infinity, it meets the `z = 1` chart, and (being a smooth irreducible
projective curve minus finitely many points at infinity) its affine patch is
genuinely nonempty, connected, and noncompact — so the statements below are
**true** (still axioms = unproven, but sound). Non-vacuous: e.g. the smooth conic
`F = x²+y²+z²` satisfies every field. -/

private abbrev NonZVar : Type := {i : Fin 3 // i ≠ (2 : Fin 3)}

private noncomputable def zAsOption (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Option NonZVar) ℂ :=
  MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm F

private noncomputable def zPolynomial (F : MvPolynomial (Fin 3) ℂ) :
    Polynomial (MvPolynomial NonZVar ℂ) :=
  MvPolynomial.optionEquivLeft ℂ NonZVar (zAsOption F)

private noncomputable def affinePolynomial (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial NonZVar ℂ :=
  Polynomial.eval 1 (zPolynomial F)

private lemma exists_eval_eq_zero_of_not_isUnit_mvPolynomial
    {σ : Type*} [Finite σ] (P : MvPolynomial σ ℂ) (hP : ¬ IsUnit P) :
    ∃ x : σ → ℂ, MvPolynomial.eval x P = 0 := by
  let I : Ideal (MvPolynomial σ ℂ) := Ideal.span ({P} : Set (MvPolynomial σ ℂ))
  by_contra hzero
  have : MvPolynomial.zeroLocus ℂ I = (∅ : Set (σ → ℂ)) := by
    ext x
    constructor
    · intro hx
      have : MvPolynomial.aeval x P = 0 := hx P (Ideal.subset_span (by simp))
      have : MvPolynomial.eval x P = 0 := by assumption
      exact (hzero ⟨x, this⟩).elim
    · simp
  have hrad : I.radical = ⊤ := by
    calc
      I.radical = MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
        simp only [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
      _ = MvPolynomial.vanishingIdeal ℂ (∅ : Set (σ → ℂ)) := by rw [this]
      _ = ⊤ := MvPolynomial.vanishingIdeal_empty
  have : I = ⊤ := (Ideal.radical_eq_top).mp hrad
  have : (1 : MvPolynomial σ ℂ) ∈ I := by
    rw [this]
    exact Submodule.mem_top
  rw [Ideal.mem_span_singleton] at this
  exact hP (isUnit_of_dvd_one this)

private lemma affinePolynomial_eval_eq (F : MvPolynomial (Fin 3) ℂ) (x : NonZVar → ℂ) :
    MvPolynomial.eval x (affinePolynomial F) =
      MvPolynomial.eval (fun i : Fin 3 =>
        if h : i = (2 : Fin 3) then (1 : ℂ) else x ⟨i, h⟩) F := by
  unfold affinePolynomial zPolynomial zAsOption
  rw [← Polynomial.eval_one_map (MvPolynomial.eval x)
    ((MvPolynomial.optionEquivLeft ℂ NonZVar)
      ((MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm) F))]
  rw [← MvPolynomial.optionEquivLeft_elim_eval]
  rw [MvPolynomial.eval_rename]
  have hfun :
      ((fun o : Option NonZVar ↦ o.elim (1 : ℂ) x) ∘
          (Equiv.optionSubtypeNe (2 : Fin 3)).symm) =
        (fun i : Fin 3 ↦ if h : i = (2 : Fin 3) then (1 : ℂ) else x ⟨i, h⟩) := by
    funext i
    by_cases h : i = (2 : Fin 3) <;> simp [*]
  simp [*]

private lemma optionElim_degree (u : NonZVar →₀ ℕ) (k : ℕ) :
    (u.optionElim k).degree = u.degree + k := by
  simp [Finsupp.degree_eq_sum, Nat.add_comm]

private lemma coeff_affinePolynomial_eq_coeff_zAsOption_zero
    {F : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hF : F.IsHomogeneous d)
    (u : NonZVar →₀ ℕ) (hu : u.degree = d) :
    MvPolynomial.coeff u (affinePolynomial F) =
      MvPolynomial.coeff (u.optionElim 0) (zAsOption F) := by
  unfold affinePolynomial zPolynomial
  rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, MvPolynomial.coeff_sum]
  trans MvPolynomial.coeff u (((MvPolynomial.optionEquivLeft ℂ NonZVar) (zAsOption F)).coeff 0)
  · refine Finset.sum_eq_single (M := ℂ) (0 : ℕ) ?_ ?_
    · intro i _hi hne
      rw [MvPolynomial.optionEquivLeft_coeff_coeff]
      have : (zAsOption F).IsHomogeneous d := by
        unfold zAsOption
        exact hF.rename_isHomogeneous
      exact this.coeff_eq_zero (by grind [optionElim_degree])
    · simp
  · rw [MvPolynomial.optionEquivLeft_coeff_coeff]

private lemma optionElim_zero_subtypeDomain_eq_mapDomain
    (m : Fin 3 →₀ ℕ) (hmz : m (2 : Fin 3) = 0) :
    (m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))).optionElim 0 =
      m.mapDomain (Equiv.optionSubtypeNe (2 : Fin 3)).symm := by
  ext o
  cases o with simp [Finsupp.mapDomain_equiv_apply, hmz]

private lemma subtypeDomain_degree_eq_of_z_eq_zero
    {F : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hF : F.IsHomogeneous d)
    {m : Fin 3 →₀ ℕ} (hm : m ∈ F.support) (hmz : m (2 : Fin 3) = 0) :
    (m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))).degree = d := by
  have hmdeg : m.degree = d := (hF.degree_eq_sum_deg_support hm).symm
  have hmap := congrArg Finsupp.degree (optionElim_zero_subtypeDomain_eq_mapDomain m hmz)
  rw [optionElim_degree, Nat.add_zero, Finsupp.degree_mapDomain] at hmap
  exact hmap.trans hmdeg

private lemma affinePolynomial_not_isUnit (H : PlaneCurveData) :
    ¬ IsUnit (affinePolynomial H.F.val) := by
  intro hunit
  obtain ⟨c, _hc, hc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := affinePolynomial H.F.val)).mp hunit
  have hcoeff_zero :
      ∀ m ∈ H.F.val.support, m (2 : Fin 3) = 0 → False := by
    intro m hm hmz
    let u : NonZVar →₀ ℕ := m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))
    have hudeg : u.degree = H.d :=
      subtypeDomain_degree_eq_of_z_eq_zero H.F.homogeneous hm hmz
    have hune : u ≠ 0 := by
      intro hzero
      have : u.degree = 0 := by simp [hzero]
      have hd0 : H.d = 0 := hudeg ▸ this
      exact (Nat.not_succ_le_zero 0) (by simpa [hd0] using H.h_deg)
    have hsurvive :
        MvPolynomial.coeff u (affinePolynomial H.F.val) =
          MvPolynomial.coeff m H.F.val := by
      calc
        MvPolynomial.coeff u (affinePolynomial H.F.val)
            = MvPolynomial.coeff (u.optionElim 0) (zAsOption H.F.val) :=
              coeff_affinePolynomial_eq_coeff_zAsOption_zero H.F.homogeneous u hudeg
        _ = MvPolynomial.coeff (m.mapDomain (Equiv.optionSubtypeNe (2 : Fin 3)).symm)
              (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm H.F.val) := by
              rw [optionElim_zero_subtypeDomain_eq_mapDomain m hmz]
              rfl
        _ = MvPolynomial.coeff m H.F.val := by
              rw [MvPolynomial.coeff_rename_mapDomain]
              exact (Equiv.optionSubtypeNe (2 : Fin 3)).symm.injective
    have hleft_zero : MvPolynomial.coeff u (affinePolynomial H.F.val) = 0 := by
      rw [hc]
      have h0u : ¬ (0 : NonZVar →₀ ℕ) = u := fun h => hune h.symm
      rw [MvPolynomial.coeff_C]
      simp [h0u]
    have : MvPolynomial.coeff m H.F.val ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    exact this (hsurvive ▸ hleft_zero)
  have :
      H.F.val ∈ Ideal.span (MvPolynomial.X '' ({(2 : Fin 3)} : Set (Fin 3))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    exact ⟨(2 : Fin 3), by simp, by
      by_contra hmz
      exact hcoeff_zero m hm (by simpa using hmz)⟩
  have : H.F.val ∈ Ideal.span ({MvPolynomial.X (2 : Fin 3)} :
        Set (MvPolynomial (Fin 3) ℂ)) := by
    simpa using this
  rw [Ideal.mem_span_singleton] at this
  exact H.h_not_at_infinity this

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The `z = 1` affine patch is nonempty: an irreducible `F` with `z ∤ F` dehomogenises
to a nonconstant `F(x,y,1)`, which has a zero over `ℂ`. -/
theorem AX_PlaneCurveAffine_nonempty (H : PlaneCurveData) :
    Nonempty (PlaneCurveAffine H) := by
  obtain ⟨x, hx⟩ :=
    exists_eval_eq_zero_of_not_isUnit_mvPolynomial (affinePolynomial H.F.val)
      (affinePolynomial_not_isUnit H)
  refine ⟨⟨(x ⟨0, by decide⟩, x ⟨1, by decide⟩), ?_⟩⟩
  rw [affinePolynomial_eval_eq H.F.val x] at hx
  have : ![x ⟨0, by decide⟩, x ⟨1, by decide⟩, 1] =
  (fun i : Fin 3 ↦ if h : i = (2 : Fin 3) then 1 else x ⟨i, h⟩) := by
    funext i
    fin_cases i <;> simp
  grind

attribute [instance] AX_PlaneCurveAffine_nonempty

private def nonZVarEquivFin2 : NonZVar ≃ Fin 2 where
  toFun i := if (i : Fin 3) = 0 then 0 else 1
  invFun j := if j = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
  left_inv := by grind
  right_inv := by grind

private noncomputable def affinePolynomialFin2 (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.renameEquiv ℂ nonZVarEquivFin2 (affinePolynomial F)

private lemma affinePolynomialFin2_eval_eq (F : MvPolynomial (Fin 3) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (affinePolynomialFin2 F) =
      MvPolynomial.eval ![v 0, v 1, (1 : ℂ)] F := by
  unfold affinePolynomialFin2
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
    affinePolynomial_eval_eq]
  congr
  funext i
  fin_cases i <;> simp [nonZVarEquivFin2]

private noncomputable def fin1Polynomial (P : MvPolynomial (Fin 1) ℂ) : Polynomial ℂ :=
  Polynomial.map (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)) (MvPolynomial.finSuccEquiv ℂ 0 P)

private lemma fin1Polynomial_eval (P : MvPolynomial (Fin 1) ℂ) (x : ℂ) :
    Polynomial.eval x (fin1Polynomial P) = MvPolynomial.eval (fun _ : Fin 1 => x) P := by
  unfold fin1Polynomial
  change Polynomial.eval x
      (Polynomial.map (MvPolynomial.eval finZeroElim) (MvPolynomial.finSuccEquiv ℂ 0 P)) = _
  rw [← MvPolynomial.eval_eq_eval_mv_eval' finZeroElim x P]
  congr
  funext i
  fin_cases i
  simp

private lemma fin1Polynomial_ne_zero {P : MvPolynomial (Fin 1) ℂ} (hP : P ≠ 0) :
    fin1Polynomial P ≠ 0 := by
  unfold fin1Polynomial
  have : MvPolynomial.finSuccEquiv ℂ 0 P ≠ 0 := by
    simp_all
  exact (Polynomial.map_ne_zero_iff (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective).mpr this

private lemma finite_zeroSet_fin1 (P : MvPolynomial (Fin 1) ℂ) (hP : P ≠ 0) :
    ({x : ℂ | MvPolynomial.eval (fun _ : Fin 1 => x) P = 0}).Finite := by
  let p := fin1Polynomial P
  have : p ≠ 0 := fin1Polynomial_ne_zero hP
  refine (p.roots.toFinset.finite_toSet.subset ?_)
  intro x hx
  have hxroot : Polynomial.IsRoot p x := by
    rw [Polynomial.IsRoot.def]
    simpa [p, fin1Polynomial_eval P x] using hx
  simp_all

private lemma exists_zero_first_of_degreeOf_pos (P : MvPolynomial (Fin 2) ℂ)
    (hdeg : 0 < MvPolynomial.degreeOf (0 : Fin 2) P) :
    ∃ R : Set ℂ, R.Finite ∧
      ∀ x ∉ R, ∃ y : ℂ, MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 => x)) P = 0 := by
  let p : Polynomial (MvPolynomial (Fin 1) ℂ) := MvPolynomial.finSuccEquiv ℂ 1 P
  let L : MvPolynomial (Fin 1) ℂ := p.leadingCoeff
  have hpdeg : 0 < p.natDegree := by
    simpa [p, MvPolynomial.natDegree_finSuccEquiv] using hdeg
  have : p ≠ 0 := by
    intro hp0
    simp_all
  have : L ≠ 0 := by
    simpa [L] using (Polynomial.leadingCoeff_ne_zero.mpr this)
  refine ⟨{x : ℂ | MvPolynomial.eval (fun _ : Fin 1 => x) L = 0}, finite_zeroSet_fin1 L this, ?_⟩
  intro x _
  let q : Polynomial ℂ := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) p
  have : q.coeff p.natDegree ≠ 0 := by
    have hxL : MvPolynomial.eval (fun _ : Fin 1 => x) L ≠ 0 := by grind
    simpa [q, L, Polynomial.coeff_map, Polynomial.coeff_natDegree] using hxL
  have : 0 < q.natDegree :=
    lt_of_lt_of_le hpdeg (Polynomial.le_natDegree_of_ne_zero this)
  have hqpos : 0 < q.degree := Polynomial.natDegree_pos_iff_degree_pos.mp this
  obtain ⟨y, hy⟩ := Complex.exists_root hqpos
  refine ⟨y, ?_⟩
  have : Polynomial.eval y q = 0 := Polynomial.IsRoot.def.mp hy
  rw [MvPolynomial.eval_eq_eval_mv_eval' (fun _ : Fin 1 => x) y P]
  grind

private lemma eq_C_of_degreeOf_fin2_eq_zero (P : MvPolynomial (Fin 2) ℂ)
    (h0 : MvPolynomial.degreeOf (0 : Fin 2) P = 0)
    (h1 : MvPolynomial.degreeOf (1 : Fin 2) P = 0) :
    P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
  ext m
  rw [MvPolynomial.coeff_C]
  by_cases hm : m = 0
  · simp [hm]
  · have hcoeff : MvPolynomial.coeff m P = 0 := by
      by_contra hne
      have hs : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
      have : m (0 : Fin 2) = 0 := Nat.eq_zero_of_le_zero
          (by simpa [h0] using MvPolynomial.le_degreeOf_of_mem_support (p := P) (0 : Fin 2) hs)
      have hm1 : m (1 : Fin 2) = 0 := Nat.eq_zero_of_le_zero
          (by simpa [h1] using MvPolynomial.le_degreeOf_of_mem_support (p := P) (1 : Fin 2) hs)
      have : m = 0 := by
        ext i
        fin_cases i <;> simp_all
      simp_all
    simp_all

private lemma eq_zero_or_exists_degreeOf_pos_of_not_isUnit_fin2 (P : MvPolynomial (Fin 2) ℂ)
    (hP : ¬ IsUnit P) :
    P = 0 ∨ 0 < MvPolynomial.degreeOf (0 : Fin 2) P ∨
      0 < MvPolynomial.degreeOf (1 : Fin 2) P := by
  by_cases hzero : P = 0
  · simp_all
  · right
    by_cases h0 : 0 < MvPolynomial.degreeOf (0 : Fin 2) P
    · simp_all
    · right
      by_contra h1pos
      have hd0 : MvPolynomial.degreeOf (0 : Fin 2) P = 0 := Nat.eq_zero_of_not_pos h0
      have hd1 : MvPolynomial.degreeOf (1 : Fin 2) P = 0 := Nat.eq_zero_of_not_pos h1pos
      have hC := eq_C_of_degreeOf_fin2_eq_zero P hd0 hd1
      have : MvPolynomial.coeff 0 P ≠ 0 := by
        grind
      exact hP (by
        rw [hC]
        exact (MvPolynomial.isUnit_iff_eq_C_of_isReduced
          (P := MvPolynomial.C (MvPolynomial.coeff 0 P))).mpr
          ⟨MvPolynomial.coeff 0 P, IsUnit.mk0 _ this, rfl⟩)

private def swapFin2 : Fin 2 ≃ Fin 2 where
  toFun i := if i = 0 then 1 else 0
  invFun i := if i = 0 then 1 else 0
  left_inv := by grind
  right_inv := by grind

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The affine patch is connected: the projective curve is connected (irreducible),
and removing the finitely many points at infinity leaves a connected real surface. -/
axiom AX_PlaneCurveAffine_connected (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_connected

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The affine patch is noncompact: by Bézout the degree-`d` curve meets `z = 0` in
`≥ 1` point, so the affine patch is the compact projective curve minus a nonempty
finite set. -/
theorem AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
    NoncompactSpace (PlaneCurveAffine H) := by
  let P : MvPolynomial (Fin 2) ℂ := affinePolynomialFin2 H.F.val
  have : ¬ IsUnit P := by
    intro hunit
    exact affinePolynomial_not_isUnit H (by
      simpa [P, affinePolynomialFin2] using
        hunit.map ((MvPolynomial.renameEquiv ℂ nonZVarEquivFin2).symm :
          MvPolynomial (Fin 2) ℂ →+* MvPolynomial NonZVar ℂ))
  refine ⟨?_⟩
  intro hcompact
  rcases eq_zero_or_exists_degreeOf_pos_of_not_isUnit_fin2 P this with hP0 | hdeg
  · let π : PlaneCurveAffine H → ℂ := fun p => p.val.1
    have hπ : Continuous π := continuous_subtype_val.fst
    have : Function.Surjective π := by
      intro x
      refine ⟨⟨(x, 0), ?_⟩, rfl⟩
      have hz : MvPolynomial.eval ![x, 0] P = 0 := by simp [hP0]
      simpa [P, affinePolynomialFin2_eval_eq H.F.val ![x, 0]] using hz
    have : π '' (Set.univ : Set (PlaneCurveAffine H)) = Set.univ := by
      ext x
      constructor
      · simp
      · intro _
        rcases this x with ⟨p, rfl⟩
        simp
    have : IsCompact (Set.univ : Set ℂ) := by
      simpa [this] using hcompact.image hπ
    exact (inferInstance : NoncompactSpace ℂ).noncompact_univ this
  · rcases hdeg with hdeg0 | hdeg1
    · obtain ⟨R, hRfinite, hRproj⟩ := exists_zero_first_of_degreeOf_pos P hdeg0
      let π : PlaneCurveAffine H → ℂ := fun p => p.val.2
      have : Continuous π := continuous_subtype_val.snd
      have : IsCompact (Set.range π) := by
        simpa only [Set.image_univ] using hcompact.image this
      have hunion : Set.range π ∪ R = Set.univ := by
        ext x
        constructor
        · simp
        · intro _
          by_cases hxR : x ∈ R
          · simp_all
          · rcases hRproj x hxR with ⟨y, hy⟩
            refine Or.inl ⟨⟨(y, x), ?_⟩, rfl⟩
            have hy' : MvPolynomial.eval ![y, x] P = 0 := by
              have hvec :
                  (Fin.cons y (fun _ : Fin 1 => x) : Fin 2 → ℂ) = ![y, x] := by
                funext i
                fin_cases i <;> rfl
              simp_all
            simpa [P, affinePolynomialFin2_eval_eq H.F.val ![y, x]] using hy'
      have : IsCompact (Set.univ : Set ℂ) := by
        simpa [hunion] using this.union hRfinite.isCompact
      exact (inferInstance : NoncompactSpace ℂ).noncompact_univ this
    · let Q : MvPolynomial (Fin 2) ℂ := MvPolynomial.renameEquiv ℂ swapFin2 P
      have : 0 < MvPolynomial.degreeOf (0 : Fin 2) Q := by
        have :=
          MvPolynomial.degreeOf_rename_of_injective (p := P) swapFin2.injective (1 : Fin 2)
        simpa [Q, MvPolynomial.renameEquiv_apply, swapFin2] using this ▸ hdeg1
      obtain ⟨R, hRfinite, hRproj⟩ := exists_zero_first_of_degreeOf_pos Q this
      let π : PlaneCurveAffine H → ℂ := fun p => p.val.1
      have : Continuous π := continuous_subtype_val.fst
      have : IsCompact (Set.range π) := by
        simpa only [Set.image_univ] using hcompact.image this
      have hunion : Set.range π ∪ R = Set.univ := by
        ext x
        constructor
        · simp
        · intro _
          by_cases hxR : x ∈ R
          · simp_all
          · rcases hRproj x hxR with ⟨y, hy⟩
            refine Or.inl ⟨⟨(x, y), ?_⟩, rfl⟩
            have hy' : MvPolynomial.eval ![x, y] P = 0 := by
              dsimp [Q] at hy
              rw [MvPolynomial.eval_rename] at hy
              have hvec :
                  ((Fin.cons y (fun _ : Fin 1 => x)) ∘ swapFin2 : Fin 2 → ℂ) = ![x, y] := by
                funext i
                fin_cases i <;> rfl
              simp_all
            simpa [P, affinePolynomialFin2_eval_eq H.F.val ![x, y]] using hy'
      have : IsCompact (Set.univ : Set ℂ) := by
        simpa [hunion] using this.union hRfinite.isCompact
      exact (inferInstance : NoncompactSpace ℂ).noncompact_univ this

attribute [instance] AX_PlaneCurveAffine_noncompact

end PlaneCurveAffine

/-! ### Projective compactification

A smooth plane curve of degree `d` generically meets the line at
infinity `{z = 0}` in **`d` distinct points** (by Bézout). So the
classical smooth projective compactification adds `d` points at
infinity (fewer if the curve is tangent to or contains the infinity
line, but still ≥ 1 for smooth curves).

The one-point compactification `OnePoint (PlaneCurveAffine H)` adds
just **one** point — wrong for any `d ≥ 2`. A unified parity-style
split as we used for `Hyperelliptic` doesn't work cleanly here because
the number of infinity points depends on the curve's intersection with
`{z = 0}`, not just parity.

We therefore **axiomatize** the projective compactification with
properly formulated instances, until the three-affine-chart atlas
construction (dehomogenizing with `x ≠ 0`, `y ≠ 0`, `z ≠ 0` and
gluing) is built explicitly.

Historical note: earlier versions (commits through `63ccce7`) defined
`PlaneCurve H := OnePoint (PlaneCurveAffine H)` as a real def. That
was topologically wrong for any `d ≥ 2`; Codex review 2026-04-23
correctly flagged it. This version is the honest axiom-stub.
-/

/-- The smooth projective plane curve `{F = 0} ⊂ ℙ²` as the projective
zero-locus of `F`.

The vanishing predicate is phrased by existence of a nonzero homogeneous
representative, so it is a predicate on projective points rather than on
Lean's chosen `Projectivization.rep`. For the homogeneous polynomial
`H.F`, this is the classical projective zero-locus. -/
def PlaneCurve (H : PlaneCurveData) : Type :=
  { p : Projectivization ℂ (Fin 3 → ℂ) //
    ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0,
      Projectivization.mk ℂ v hv = p ∧ H.F.val.eval v = 0 }

private abbrev ProjectivePlaneVector := Fin 3 → ℂ

private lemma homogeneous_eval_smul {p : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℂ) (v : ProjectivePlaneVector) :
    p.eval (fun i => c * v i) = c ^ d * p.eval v := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  calc
    (∑ x ∈ p.support, p.coeff x * ∏ i, (c * v i) ^ x i)
        = ∑ x ∈ p.support, p.coeff x * (c ^ d * ∏ i, v i ^ x i) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hdeg : d = ∑ i ∈ x.support, x i :=
            hp.degree_eq_sum_deg_support hx
          have hprod : ∏ i : Fin 3, (c * v i) ^ x i =
              c ^ d * ∏ i : Fin 3, v i ^ x i := by
            rw [hdeg]
            simp_rw [mul_pow]
            rw [Finset.prod_mul_distrib]
            congr 1
            rw [Finset.prod_pow_eq_pow_sum]
            have hsum : x.sum (fun _ n => n) = ∑ i : Fin 3, x i :=
              Finsupp.sum_fintype x (fun _ n => n) (by simp)
            change c ^ (∑ i : Fin 3, x i) = c ^ (∑ i ∈ x.support, x i)
            rw [← hsum]
            rfl
          rw [hprod]
    _ = c ^ d * ∑ x ∈ p.support, p.coeff x * ∏ i, v i ^ x i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring

private abbrev planeCurveUnitZero (H : PlaneCurveData) : Type :=
  {v : ProjectivePlaneVector // ‖v‖ = 1 ∧ H.F.val.eval v = 0}

private lemma planeCurveUnitZero_isCompact (H : PlaneCurveData) :
    IsCompact {v : ProjectivePlaneVector | ‖v‖ = 1 ∧ H.F.val.eval v = 0} := by
  have : IsCompact (Metric.sphere (0 : ProjectivePlaneVector) 1) :=
    isCompact_sphere 0 1
  have : IsClosed {v : ProjectivePlaneVector | H.F.val.eval v = 0} :=
    isClosed_eq (MvPolynomial.continuous_eval H.F.val) continuous_const
  have :
      {v : ProjectivePlaneVector | ‖v‖ = 1 ∧ H.F.val.eval v = 0} =
        Metric.sphere (0 : ProjectivePlaneVector) 1 ∩
          {v : ProjectivePlaneVector | H.F.val.eval v = 0} := by
    ext
    simp
  grind [IsCompact.inter_right]

private instance planeCurveUnitZero_compactSpace (H : PlaneCurveData) :
    CompactSpace (planeCurveUnitZero H) :=
  isCompact_iff_compactSpace.mp (planeCurveUnitZero_isCompact H)

private lemma nonzero_of_mem_planeCurveUnitZero {H : PlaneCurveData}
    (v : planeCurveUnitZero H) :
    (v.1 : ProjectivePlaneVector) ≠ 0 := by
  intro
  have : ‖(v.1)‖ = 0 := by simp [*]
  grind

private noncomputable def planeCurveUnitZeroToPlaneCurve (H : PlaneCurveData) :
    planeCurveUnitZero H → PlaneCurve H := fun v =>
  ⟨Projectivization.mk ℂ (v.1 : ProjectivePlaneVector)
      (nonzero_of_mem_planeCurveUnitZero v),
    ⟨(v.1 : ProjectivePlaneVector), nonzero_of_mem_planeCurveUnitZero v, rfl, v.2.2⟩⟩

private abbrev ProjectivePlaneNonzeroVectors := {v : Fin 3 → ℂ // v ≠ 0}

private def unitSmulProjectivePlaneNonzeroVectors (a : ℂˣ)
    (v : ProjectivePlaneNonzeroVectors) : ProjectivePlaneNonzeroVectors :=
  ⟨(a : ℂ) • (v : Fin 3 → ℂ), by
    intro
    have : (a : ℂ) ≠ 0 := by simp
    have : (v : Fin 3 → ℂ) = 0 := by simp_all
    grind⟩

private def unitSmulProjectivePlaneNonzeroVectorsHomeomorph (a : ℂˣ) :
    ProjectivePlaneNonzeroVectors ≃ₜ ProjectivePlaneNonzeroVectors where
  toFun := unitSmulProjectivePlaneNonzeroVectors a
  invFun := unitSmulProjectivePlaneNonzeroVectors a⁻¹
  left_inv v := by
    apply Subtype.ext
    change ((↑(a⁻¹) : ℂ) • ((a : ℂ) • (v : Fin 3 → ℂ))) = (v : Fin 3 → ℂ)
    simp
  right_inv v := by
    apply Subtype.ext
    change ((a : ℂ) • ((↑(a⁻¹) : ℂ) • (v : Fin 3 → ℂ))) = (v : Fin 3 → ℂ)
    simp
  continuous_toFun := (continuous_const.smul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.smul continuous_subtype_val).subtype_mk _

private lemma projectivization_preimage_image_eq (U : Set ProjectivePlaneNonzeroVectors) :
    (Projectivization.mk' ℂ) ⁻¹' ((Projectivization.mk' ℂ) '' U) =
      Set.iUnion (fun a : ℂˣ => unitSmulProjectivePlaneNonzeroVectors a '' U) := by
  ext x
  constructor
  · rintro ⟨y, hyU, hxy⟩
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk] at hxy
    rcases (Projectivization.mk_eq_mk_iff ℂ
        (y : Fin 3 → ℂ) (x : Fin 3 → ℂ) y.2 x.2).1 hxy with ⟨a, ha⟩
    rw [Set.mem_iUnion]
    refine ⟨a⁻¹, ?_⟩
    refine ⟨y, hyU, ?_⟩
    apply Subtype.ext
    change ((↑(a⁻¹) : ℂ) • (y : Fin 3 → ℂ)) = (x : Fin 3 → ℂ)
    rw [← ha]
    change ((↑(a⁻¹) : ℂ) • ((a : ℂ) • (x : Fin 3 → ℂ))) = (x : Fin 3 → ℂ)
    simp
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨a, y, hyU, rfl⟩
    refine ⟨y, hyU, ?_⟩
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
    grind [unitSmulProjectivePlaneNonzeroVectors, Projectivization.mk_eq_mk_iff']

private theorem projectivization_isOpenMap_mk' :
    IsOpenMap (@Quotient.mk' ProjectivePlaneNonzeroVectors
      (projectivizationSetoid ℂ (Fin 3 → ℂ))) := by
  intro U hU
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  change IsOpen ((Projectivization.mk' ℂ :
      ProjectivePlaneNonzeroVectors → Projectivization ℂ (Fin 3 → ℂ)) ⁻¹'
    ((Projectivization.mk' ℂ :
      ProjectivePlaneNonzeroVectors → Projectivization ℂ (Fin 3 → ℂ)) '' U))
  rw [projectivization_preimage_image_eq]
  exact isOpen_iUnion fun a =>
    (unitSmulProjectivePlaneNonzeroVectorsHomeomorph a).isOpenMap U hU

private theorem projectivization_isOpenQuotientMap_mk' :
    IsOpenQuotientMap (@Quotient.mk' ProjectivePlaneNonzeroVectors
      (projectivizationSetoid ℂ (Fin 3 → ℂ))) where
  surjective := Quotient.mk_surjective
  continuous := continuous_quotient_mk'
  isOpenMap := projectivization_isOpenMap_mk'

private lemma projectivization_mk'_eq_mk'_iff_minors
    (u v : ProjectivePlaneNonzeroVectors) :
    Projectivization.mk' ℂ u = Projectivization.mk' ℂ v ↔
      ∀ i j : Fin 3, (u : Fin 3 → ℂ) i * (v : Fin 3 → ℂ) j =
        (u : Fin 3 → ℂ) j * (v : Fin 3 → ℂ) i := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
  rw [Projectivization.mk_eq_mk_iff' ℂ (u : Fin 3 → ℂ) (v : Fin 3 → ℂ) u.2 v.2]
  constructor
  · rintro ⟨a, h⟩ i j
    rw [← h]
    change (a • (v : Fin 3 → ℂ)) i * (v : Fin 3 → ℂ) j =
      (a • (v : Fin 3 → ℂ)) j * (v : Fin 3 → ℂ) i
    simp [mul_comm, mul_left_comm, mul_assoc]
  · intro h
    have hv_nonzero : ∃ k : Fin 3, (v : Fin 3 → ℂ) k ≠ 0 := by
      by_contra hnone
      apply v.2
      ext k
      by_contra hk
      exact hnone ⟨k, hk⟩
    rcases hv_nonzero with ⟨k, hvk⟩
    let a : ℂ := (u : Fin 3 → ℂ) k / (v : Fin 3 → ℂ) k
    refine ⟨a, ?_⟩
    ext i
    change a * (v : Fin 3 → ℂ) i = (u : Fin 3 → ℂ) i
    grind

private def projectivizationMinor (i j : Fin 3)
    (p : ProjectivePlaneNonzeroVectors × ProjectivePlaneNonzeroVectors) : ℂ :=
  (p.1 : Fin 3 → ℂ) i * (p.2 : Fin 3 → ℂ) j -
    (p.1 : Fin 3 → ℂ) j * (p.2 : Fin 3 → ℂ) i

private theorem continuous_projectivizationMinor (i j : Fin 3) :
    Continuous (projectivizationMinor i j) :=
      ((((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))).sub
          (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
            ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))))

private theorem projectivization_rel_closed :
    IsClosed {q : ProjectivePlaneNonzeroVectors × ProjectivePlaneNonzeroVectors |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} := by
  have hset :
      {q : ProjectivePlaneNonzeroVectors × ProjectivePlaneNonzeroVectors |
        Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} =
        ⋂ i : Fin 3, ⋂ j : Fin 3,
          {q : ProjectivePlaneNonzeroVectors × ProjectivePlaneNonzeroVectors |
            projectivizationMinor i j q = 0} := by
    ext q
    constructor
    · intro h
      change Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2 at h
      rw [projectivization_mk'_eq_mk'_iff_minors q.1 q.2] at h
      simp [projectivizationMinor, sub_eq_zero, h]
    · intro h
      change Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2
      rw [projectivization_mk'_eq_mk'_iff_minors q.1 q.2]
      intro i j
      have hij : projectivizationMinor i j q = 0 := by
        simpa using (Set.mem_iInter.mp (Set.mem_iInter.mp h i) j)
      simpa [projectivizationMinor, sub_eq_zero] using hij
  rw [hset]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (continuous_projectivizationMinor i j) continuous_const

private theorem projectivization_t2Space :
    T2Space (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))) := by
  rw [t2Space_iff_of_isOpenQuotientMap projectivization_isOpenQuotientMap_mk']
  exact projectivization_rel_closed

instance PlaneCurve.instTopologicalSpace (H : PlaneCurveData) :
    TopologicalSpace (PlaneCurve H) := by
  letI : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace
      (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))))
  change TopologicalSpace
    { p : Projectivization ℂ (Fin 3 → ℂ) //
      ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0,
        Projectivization.mk ℂ v hv = p ∧ H.F.val.eval v = 0 }
  infer_instance

private lemma continuous_planeCurveUnitZeroToPlaneCurve (H : PlaneCurveData) :
    Continuous (planeCurveUnitZeroToPlaneCurve H) := by
  let : TopologicalSpace (Projectivization ℂ ProjectivePlaneVector) :=
    inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid _ _)))
  apply Continuous.subtype_mk
  exact continuous_quotient_mk'.comp (continuous_subtype_val.subtype_mk _)

instance PlaneCurve.instT2Space (H : PlaneCurveData) : T2Space (PlaneCurve H) := by
  let : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace
      (Quotient (projectivizationSetoid ℂ _)))
  let : T2Space (Projectivization ℂ (Fin 3 → ℂ)) := projectivization_t2Space
  change T2Space { p : Projectivization _ _ // ∃ v, ∃ hv,
        Projectivization.mk ℂ v hv = p ∧ H.F.val.eval v = 0 }
  infer_instance

instance PlaneCurve.instCompactSpace (H : PlaneCurveData) :
    CompactSpace (PlaneCurve H) := by
  let : TopologicalSpace (Projectivization ℂ ProjectivePlaneVector) :=
    inferInstanceAs (TopologicalSpace (Quotient _))
  rw [← isCompact_univ_iff]
  have : IsCompact ((planeCurveUnitZeroToPlaneCurve H) ''
      (Set.univ : Set (planeCurveUnitZero H))) :=
    isCompact_univ.image (continuous_planeCurveUnitZeroToPlaneCurve H)
  rw [show (planeCurveUnitZeroToPlaneCurve H) '' (Set.univ : Set (planeCurveUnitZero H)) =
      (Set.univ : Set (PlaneCurve H)) by
    ext p
    constructor
    · intro
      trivial
    · intro
      obtain ⟨v, hv, hmk, heval⟩ := p.2
      let c : ℂ := ((‖v‖)⁻¹ : ℝ)
      let w := (c * v ·)
      have : ‖v‖ ≠ 0 := mt norm_eq_zero.mp hv
      have hc_ne : c ≠ 0 := by
        dsimp [c]
        exact_mod_cast inv_ne_zero this
      have : ‖w‖ = 1 := by
        dsimp [w, c]
        change ‖((↑(‖v‖)⁻¹ : ℂ) • v : ProjectivePlaneVector)‖ = 1
        rw [norm_smul]
        have hnonneg : 0 ≤ (‖v‖)⁻¹ := inv_nonneg.mpr (norm_nonneg v)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact inv_mul_cancel₀ this
      have heval_w : H.F.val.eval w = 0 := by
        dsimp [w, c]
        rw [homogeneous_eval_smul H.F.homogeneous]
        simp [heval]
      refine ⟨⟨w, this, heval_w⟩, trivial, ?_⟩
      apply Subtype.ext
      change Projectivization.mk ℂ w
          (nonzero_of_mem_planeCurveUnitZero ⟨w, this, heval_w⟩) = p.1
      rw [← hmk]
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
      refine ⟨Units.mk0 c hc_ne, ?_⟩
      rfl] at this
  grind

noncomputable def PlaneCurveAffine.toPlaneCurve (H : PlaneCurveData)
    (p : PlaneCurveAffine H) : PlaneCurve H := by
  let v : Fin 3 → ℂ := ![p.val.1, p.val.2, 1]
  have hv : v ≠ 0 := by
    intro h
    have h2 : v 2 = 0 := congrFun h 2
    exact one_ne_zero h2
  refine ⟨Projectivization.mk ℂ v hv, v, hv, rfl, p.property⟩

theorem continuous_toPlaneCurve (H : PlaneCurveData) :
    Continuous (PlaneCurveAffine.toPlaneCurve H) := by
  letI : Setoid { v : Fin 3 → ℂ // v ≠ 0 } := projectivizationSetoid ℂ (Fin 3 → ℂ)
  letI : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ _)))
  apply Continuous.subtype_mk
  refine continuous_quotient_mk'.comp ?_
  apply Continuous.subtype_mk
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_subtype_val.fst
  · exact continuous_subtype_val.snd
  · exact continuous_const

axiom PlaneCurve.instChartedSpace (H : PlaneCurveData) :
    ChartedSpace ℂ (PlaneCurve H)
attribute [instance] PlaneCurve.instChartedSpace

axiom PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)
attribute [instance] PlaneCurve.instIsManifold

lemma PlaneCurve_nhdsWithin_compl_singleton_neBot (H : PlaneCurveData) (x : PlaneCurve H) :
    (nhdsWithin x {x}ᶜ).NeBot := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have h_map := e.map_nhdsWithin_preimage_eq hx {e x}ᶜ
  have h_eq : nhdsWithin x (e ⁻¹' {e x}ᶜ) = nhdsWithin x {x}ᶜ := by
    refine nhdsWithin_eq_nhdsWithin' (e.open_source.mem_nhds hx) ?_
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      intro h_eq
      apply hy1
      rw [h_eq]
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      intro h_eq
      apply hy1
      exact e.injOn hy2 hx h_eq
  rw [← h_eq]
  rw [← Filter.map_neBot_iff e]
  rw [h_map]
  exact NormedField.nhdsNE_neBot (e x)

/-- The subset of points at infinity on the projective curve. -/
def infinityPoints (H : PlaneCurveData) : Set (PlaneCurve H) :=
  { p | ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv = p.1 ∧ v 2 = 0 }

section

open MvPolynomial

noncomputable def infPoly (H : PlaneCurveData) : Polynomial ℂ :=
  MvPolynomial.aeval (fun i => if i = 0 then Polynomial.X
    else if i = 1 then 1 else 0) H.F.val

noncomputable def infMon (d i : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i, d - i, 0]

lemma exists_monomial_z0 (H : PlaneCurveData) :
    ∃ m ∈ H.F.val.support, m 2 = 0 := by
  by_contra h_all
  push Not at h_all
  have h_le : ∀ m ∈ H.F.val.support, Finsupp.single (2 : Fin 3) 1 ≤ m := by
    intro m hm
    rw [Finsupp.single_le_iff]
    have h_nz : m 2 ≠ 0 := h_all m hm
    omega
  have h_mod : H.F.val.modMonomial (Finsupp.single 2 1) = 0 := by
    ext m
    rw [coeff_zero]
    by_cases hm : m ∈ H.F.val.support
    · rw [coeff_modMonomial_of_le H.F.val (h_le m hm)]
    · rw [mem_support_iff] at hm
      push Not at hm
      by_cases h_le2 : Finsupp.single 2 1 ≤ m
      · rw [coeff_modMonomial_of_le H.F.val h_le2]
      · rw [coeff_modMonomial_of_not_le H.F.val h_le2, hm]
  have h_dvd : MvPolynomial.X 2 ∣ H.F.val :=
    MvPolynomial.X_dvd_iff_modMonomial_eq_zero.mpr h_mod
  exact H.h_not_at_infinity h_dvd

lemma prod_f_eq (m : Fin 3 →₀ ℕ) :
    m.prod (fun i k => (if i = 0 then Polynomial.X
      else if i = 1 then (1 : Polynomial ℂ) else 0) ^ k) =
    if m 2 = 0 then Polynomial.X ^ m 0 else 0 := by
  have h_prod : m.prod (fun i k => (if i = 0 then Polynomial.X
        else if i = 1 then (1 : Polynomial ℂ) else 0) ^ k) =
      ∏ i : Fin 3, (if i = 0 then Polynomial.X
        else if i = 1 then (1 : Polynomial ℂ) else 0) ^ m i := by
    rw [Finsupp.prod_fintype]
    · intro i
      simp
  rw [h_prod]
  rw [Fin.prod_univ_three]
  by_cases h : m 2 = 0 <;> simp [h]

lemma infPoly_eq_sum (H : PlaneCurveData) :
    infPoly H = H.F.val.support.sum (fun m =>
      if m 2 = 0 then Polynomial.monomial (m 0) (MvPolynomial.coeff m H.F.val) else 0) := by
  dsimp [infPoly]
  conv_lhs => rw [MvPolynomial.as_sum H.F.val]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  have h_prod := prod_f_eq m
  rw [h_prod]
  by_cases h2 : m 2 = 0
  · simp only [h2, Polynomial.algebraMap_eq, Nat.reduceAdd, Fin.isValue, if_true]
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  · simp only [h2, Polynomial.algebraMap_eq, Nat.reduceAdd, Fin.isValue, mul_zero, if_false]

lemma m_eq_infMon (d : ℕ) (m : Fin 3 →₀ ℕ) (h2 : m 2 = 0) (hdeg : (Finsupp.weight 1) m = d) :
    m = infMon d (m 0) := by
  have h_sum : (Finsupp.weight 1) m = m 0 + m 1 + m 2 := by
    change (Finsupp.weight (fun _ => (1 : ℕ))) m = m 0 + m 1 + m 2
    have h := Finsupp.weight_apply (fun _ => (1 : ℕ)) m
    rw [h]
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_three]
    · intro x
      simp
  rw [h_sum, h2, add_zero] at hdeg
  have h_m1 : m 1 = d - m 0 := by omega
  ext i
  fin_cases i <;> simp [h_m1, h2, infMon]

lemma coeff_infPoly (H : PlaneCurveData) (i : ℕ) :
    (infPoly H).coeff i = MvPolynomial.coeff (infMon H.d i) H.F.val := by
  rw [infPoly_eq_sum]
  rw [Polynomial.finsetSum_coeff]
  by_cases h_mem : infMon H.d i ∈ H.F.val.support
  · have h_eq : ∀ m ∈ H.F.val.support,
        ((if m 2 = 0 then Polynomial.monomial (m 0) (MvPolynomial.coeff m H.F.val) else 0) :
          Polynomial ℂ).coeff i =
            if m = infMon H.d i then MvPolynomial.coeff (infMon H.d i) H.F.val else 0 := by
      intro m hm
      by_cases hm_inf : m = infMon H.d i
      · subst hm_inf
        have h2 : (infMon H.d i) 2 = 0 := rfl
        have h0 : (infMon H.d i) 0 = i := rfl
        simp only [h2, h0, if_true, Polynomial.coeff_monomial]
      · rw [if_neg hm_inf]
        by_cases h2 : m 2 = 0
        · rw [if_pos h2]
          rw [Polynomial.coeff_monomial]
          split_ifs with h_eq2
          · have h_deg : (Finsupp.weight 1) m = H.d :=
              H.F.homogeneous (MvPolynomial.mem_support_iff.mp hm)
            have hm_inf2 : m = infMon H.d i := by
              have h_eq3 : m = infMon H.d (m 0) := m_eq_infMon H.d m h2 h_deg
              rw [h_eq2] at h_eq3
              exact h_eq3
            contradiction
          · rfl
        · rw [if_neg h2]
          rfl
    rw [Finset.sum_congr rfl h_eq]
    rw [Finset.sum_eq_single (infMon H.d i)]
    · simp
    · intro b hb hne
      simp [hne]
    · intro h_not
      exact (h_not h_mem).elim
  · -- If infMon H.d i is not in the support:
    have h_eq : ∀ m ∈ H.F.val.support,
        ((if m 2 = 0 then Polynomial.monomial (m 0) (MvPolynomial.coeff m H.F.val) else 0) :
          Polynomial ℂ).coeff i = 0 := by
      intro m hm
      by_cases h2 : m 2 = 0
      · rw [if_pos h2]
        rw [Polynomial.coeff_monomial]
        split_ifs with h_eq2
        · have h_deg : (Finsupp.weight 1) m = H.d :=
            H.F.homogeneous (MvPolynomial.mem_support_iff.mp hm)
          have hm_inf2 : m = infMon H.d i := by
            have h_eq3 : m = infMon H.d (m 0) := m_eq_infMon H.d m h2 h_deg
            rw [h_eq2] at h_eq3
            exact h_eq3
          rw [hm_inf2] at hm
          contradiction
        · rfl
      · rw [if_neg h2]
        rfl
    rw [Finset.sum_congr rfl h_eq]
    simp only [Nat.reduceAdd, Finset.sum_const_zero]
    have h_zero : MvPolynomial.coeff (infMon H.d i) H.F.val = 0 := by
      rwa [MvPolynomial.mem_support_iff, not_not] at h_mem
    exact h_zero.symm

lemma infPoly_ne_zero (H : PlaneCurveData) : infPoly H ≠ 0 := by
  rcases exists_monomial_z0 H with ⟨m, hm, hm2⟩
  have h_deg : (Finsupp.weight 1) m = H.d :=
    H.F.homogeneous (MvPolynomial.mem_support_iff.mp hm)
  have h_eq : m = infMon H.d (m 0) := m_eq_infMon H.d m hm2 h_deg
  have h_coeff : MvPolynomial.coeff (infMon H.d (m 0)) H.F.val ≠ 0 := by
    rw [← h_eq]
    exact MvPolynomial.mem_support_iff.mp hm
  have h_poly_coeff : (infPoly H).coeff (m 0) ≠ 0 := by
    rw [coeff_infPoly]
    exact h_coeff
  intro h_zero
  rw [h_zero] at h_poly_coeff
  simp at h_poly_coeff

lemma vec1_ne_zero (t : ℂ) : (![t, 1, 0] : Fin 3 → ℂ) ≠ 0 := by
  intro h
  have h1 : (![t, 1, 0] : Fin 3 → ℂ) 1 = 0 := congrFun h 1
  exact one_ne_zero h1

lemma vec2_ne_zero : (![1, 0, 0] : Fin 3 → ℂ) ≠ 0 := by
  intro h
  have h0 : (![1, 0, 0] : Fin 3 → ℂ) 0 = 0 := congrFun h 0
  exact one_ne_zero h0

noncomputable def infProj (x : ℂ ⊕ Unit) : Projectivization ℂ (Fin 3 → ℂ) :=
  match x with
  | Sum.inl t => Projectivization.mk ℂ ![t, 1, 0] (vec1_ne_zero t)
  | Sum.inr () => Projectivization.mk ℂ ![1, 0, 0] vec2_ne_zero

noncomputable def infFinset (H : PlaneCurveData) : Finset (ℂ ⊕ Unit) :=
  open Classical in
  ((infPoly H).roots.toFinset).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ : Finset Unit).map ⟨Sum.inr, Sum.inr_injective⟩

lemma eval_zero_of_proj_eq {H : PlaneCurveData} {v w : Fin 3 → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw) (hw_zero : H.F.val.eval w = 0) :
    H.F.val.eval v = 0 := by
  rw [Projectivization.mk_eq_mk_iff ℂ v w hv hw] at h
  rcases h with ⟨c, hc⟩
  rw [← hc]
  change H.F.val.eval (fun i => (c : ℂ) * w i) = 0
  rw [homogeneous_eval_smul H.F.homogeneous]
  rw [hw_zero, mul_zero]

lemma eval_aeval_eq (F : MvPolynomial (Fin 3) ℂ) (f : Fin 3 → Polynomial ℂ) (t : ℂ) :
    (MvPolynomial.aeval f F).eval t = MvPolynomial.eval (fun i => (f i).eval t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma eval_infPoly (H : PlaneCurveData) (t : ℂ) :
    (infPoly H).eval t = H.F.val.eval ![t, 1, 0] := by
  dsimp [infPoly]
  rw [eval_aeval_eq]
  apply congrArg (fun x => MvPolynomial.eval x H.F.val)
  ext i
  fin_cases i <;> simp

open Classical in
lemma image_infinityPoints_subset (H : PlaneCurveData) :
    Subtype.val '' (infinityPoints H) ⊆ ↑((infFinset H).image infProj) := by
  classical
  rintro p ⟨q, hq, rfl⟩
  rcases hq with ⟨v, hv, h_mk, hz⟩
  have hq_prop := q.property
  rcases hq_prop with ⟨w, hw, hw_mk, hw_eval⟩
  have heval : H.F.val.eval v = 0 := by
    apply eval_zero_of_proj_eq hv hw ?_ hw_eval
    rw [hw_mk, h_mk]
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h_v0
      apply hv
      ext i
      fin_cases i
      · exact h_v0
      · exact h1
      · exact hz
    have h_eq : Projectivization.mk ℂ v hv =
        Projectivization.mk ℂ ![1, 0, 0] vec2_ne_zero := by
      rw [Projectivization.mk_eq_mk_iff ℂ v ![1, 0, 0] hv vec2_ne_zero]
      refine ⟨Units.mk0 (v 0) h0, ?_⟩
      ext i
      fin_cases i
      · simp
      · simp [h1]
      · simp [hz]
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨Sum.inr (), ?_, ?_⟩
    · rw [infFinset]
      rw [Finset.mem_union]
      right
      rw [Finset.mem_map]
      refine ⟨(), Finset.mem_univ _, rfl⟩
    · rw [infProj]
      exact h_eq.symm.trans h_mk
  · let t := v 0 / v 1
    have h_eq : Projectivization.mk ℂ v hv =
        Projectivization.mk ℂ ![t, 1, 0] (vec1_ne_zero t) := by
      rw [Projectivization.mk_eq_mk_iff ℂ v ![t, 1, 0] hv (vec1_ne_zero t)]
      refine ⟨Units.mk0 (v 1) h1, ?_⟩
      ext i
      fin_cases i
      · simp only [t, Fin.isValue, Nat.reduceAdd, Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero,
          Units.smul_mk0, smul_eq_mul]
        rw [mul_comm, div_mul_cancel₀ _ h1]
      · simp
      · simp [hz]
    have heval_t : H.F.val.eval ![t, 1, 0] = 0 := by
      apply eval_zero_of_proj_eq (vec1_ne_zero t) hv ?_ heval
      rw [h_eq]
    have ht_root : t ∈ (infPoly H).roots := by
      rw [Polynomial.mem_roots (infPoly_ne_zero H)]
      rw [Polynomial.IsRoot]
      rw [eval_infPoly]
      exact heval_t
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨Sum.inl t, ?_, ?_⟩
    · rw [infFinset]
      rw [Finset.mem_union]
      left
      rw [Finset.mem_map]
      refine ⟨t, ?_, rfl⟩
      rw [Multiset.mem_toFinset]
      exact ht_root
    · rw [infProj]
      exact h_eq.symm.trans h_mk

open Classical in
theorem infinityPoints_finite (H : PlaneCurveData) :
    (infinityPoints H).Finite := by
  classical
  have h_img : (Subtype.val '' (infinityPoints H)).Finite := by
    apply Set.Finite.subset
      (Finset.finite_toSet ((infFinset H).image infProj))
    exact image_infinityPoints_subset H
  exact Set.Finite.of_finite_image h_img Subtype.val_injective.injOn

end

theorem range_toPlaneCurve_eq_compl_infinityPoints (H : PlaneCurveData) :
    Set.range (PlaneCurveAffine.toPlaneCurve H) = (infinityPoints H)ᶜ := by
  ext p
  simp only [Set.mem_range, Set.mem_compl_iff, infinityPoints, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, rfl⟩ ⟨v, hv, h_mk, h_z⟩
    have h_eq : Projectivization.mk ℂ v hv =
      Projectivization.mk ℂ ![q.val.1, q.val.2, 1] (by
        intro h
        have h2 : ![q.val.1, q.val.2, 1] 2 = 0 := congrFun h 2
        exact one_ne_zero h2) := by
      exact h_mk
    rw [Projectivization.mk_eq_mk_iff ℂ v ![q.val.1, q.val.2, 1] hv] at h_eq
    rcases h_eq with ⟨a, ha⟩
    have h2 : v 2 = (a : ℂ) := by
      have h_eval := congrFun ha 2
      change (a • ![q.val.1, q.val.2, 1]) 2 = v 2 at h_eval
      rw [← h_eval]
      change (a : ℂ) • (1 : ℂ) = (a : ℂ)
      rw [smul_eq_mul, mul_one]
    rw [h_z] at h2
    have ha_zero : (a : ℂ) = 0 := by
      simpa using h2.symm
    exact a.ne_zero ha_zero
  · intro hp
    letI : Setoid { v : Fin 3 → ℂ // v ≠ 0 } := projectivizationSetoid ℂ (Fin 3 → ℂ)
    obtain ⟨v, hv, h_mk, heval⟩ := p.2
    have h_v2 : v 2 ≠ 0 := by
      intro hz
      apply hp
      refine ⟨v, hv, h_mk, hz⟩
    let c := (v 2)⁻¹
    let w := c • v
    have hw2 : w 2 = 1 := by
      change c * v 2 = 1
      exact inv_mul_cancel₀ h_v2
    have heval_w : H.F.val.eval w = 0 := by
      change H.F.val.eval (fun i => c * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    have h_w_eq : w = ![w 0, w 1, 1] := by
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hw2
    have h_q_eval : H.F.val.eval ![w 0, w 1, (1 : ℂ)] = 0 := by
      rw [← h_w_eq]
      exact heval_w
    let q : PlaneCurveAffine H := ⟨(w 0, w 1), h_q_eval⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change Projectivization.mk ℂ ![w 0, w 1, 1] _ = p.val
    have hw_nonzero : w ≠ 0 := by
      intro h
      have h2 : w 2 = 0 := congrFun h 2
      rw [hw2] at h2
      exact one_ne_zero h2
    have h_mk_eq : Projectivization.mk ℂ ![w 0, w 1, 1] (h_w_eq ▸ hw_nonzero) =
        Projectivization.mk ℂ w hw_nonzero := by
      change Quotient.mk' (⟨![w 0, w 1, 1], h_w_eq ▸ hw_nonzero⟩ : {v : Fin 3 → ℂ // v ≠ 0}) =
        Quotient.mk' (⟨w, hw_nonzero⟩ : {v : Fin 3 → ℂ // v ≠ 0})
      congr 1
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hw2.symm
    rw [h_mk_eq]
    rw [← h_mk]
    rw [Projectivization.mk_eq_mk_iff ℂ w v hw_nonzero hv]
    refine ⟨Units.mk0 c (inv_ne_zero h_v2), rfl⟩

theorem dense_range_toPlaneCurve (H : PlaneCurveData) :
    Dense (Set.range (PlaneCurveAffine.toPlaneCurve H)) := by
  have h_ne : ∀ x : PlaneCurve H, (nhdsWithin x {x}ᶜ).NeBot :=
    PlaneCurve_nhdsWithin_compl_singleton_neBot H
  haveI : ∀ x : PlaneCurve H, (nhdsWithin x {x}ᶜ).NeBot := h_ne
  rw [range_toPlaneCurve_eq_compl_infinityPoints H]
  rw [Set.compl_eq_univ_diff]
  exact Dense.diff_finite dense_univ (infinityPoints_finite H)

instance PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurve H) := by
  have _hAff : ConnectedSpace (PlaneCurveAffine H) :=
    PlaneCurveAffine.AX_PlaneCurveAffine_connected H
  have hRange : IsConnected (Set.range (PlaneCurveAffine.toPlaneCurve H)) :=
    isConnected_range (continuous_toPlaneCurve H)
  have hDense : Dense (Set.range (PlaneCurveAffine.toPlaneCurve H)) :=
    dense_range_toPlaneCurve H
  have hUniv : IsConnected (Set.univ : Set (PlaneCurve H)) :=
    hDense.closure_eq ▸ hRange.closure
  exact connectedSpace_iff_univ.mpr hUniv


/-- `PlaneCurve H` is nonempty.
This is proved by lifting the (now-proven) affine-nonempty witness `(x, y)` from
`PlaneCurveAffine.AX_PlaneCurveAffine_nonempty` to the projective point `[x : y : 1]`
in `PlaneCurve H`.
The historical soundness concern about the affine patch being empty for `F = z` (issue #82)
is resolved at the data level: `PlaneCurveData` requires `h_not_at_infinity` (`z ∤ F`),
making the affine nonempty axiom/theorem sound. -/
instance PlaneCurve.instNonempty (H : PlaneCurveData) : Nonempty (PlaneCurve H) := by
  obtain ⟨⟨x, y⟩, hp⟩ := PlaneCurveAffine.AX_PlaneCurveAffine_nonempty H
  let v : Fin 3 → ℂ := ![x, y, 1]
  have hv : v ≠ 0 := by
    intro h
    have h2 : v 2 = 0 := congrFun h 2
    exact one_ne_zero h2
  exact ⟨⟨Projectivization.mk ℂ v hv, v, hv, rfl, hp⟩⟩

-- TODO (genus_eq): `Jacobians.RiemannSurface.genus (PlaneCurve H) = H.genus`
-- via the Plücker formula discharge.

-- TODO (Pluecker discharge): concrete `AX_PluckerFormula` via
-- Poincaré-residue forms `x^a y^b z^c · resF`.

-- TODO (Fermat curves): `{x^d + y^d + z^d = 0}` as concrete example.

end Jacobians.ProjectiveCurve
