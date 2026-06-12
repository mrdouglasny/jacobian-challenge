/-
# P9 — the g=1 boundary-word witness, stage 1: the two explicit integrals

Handover UPDATE 4 P9 (`docs/planning/P9_ELLIPTIC_WITNESS_PLAN.md`).  With
the constant/linear field choices `h := c`, `F := c·z`, the two boundary
words of `ArcBoundaryWordData` reduce to:

* `rectBoundaryIntegral (fun z => (c·z)·c) = 0` — Cauchy on the box for an
  entire function (`word_R1`'s right side);
* `boundaryForm (fun _ => c) (fun z => c·z) = normSq c · 2i` — the classic
  area integral `∮_{∂[0,1]²} conj z dz = 2i` (`word_R2`'s right side).

Stages 1–2 deliver the integral lemmas and loop layer; stage 3 (below)
assembles `ellipticArcBoundaryWordData : ArcBoundaryWordDataInterior` over
the oriented elliptic loops with the orientation-normalized constant
`c := √|Im (ω₂ · conj ω₁)|` — the first complete family witness for the
analytic half of `AX_PeriodCycleBasis`.
-/
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWord
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWordInterior
import Jacobians.RiemannSurface.ArcAlgebra
import Jacobians.ProjectiveCurve.Elliptic.Witnesses
import Jacobians.ProjectiveCurve.Elliptic.Periods

namespace Jacobians.RiemannSurface
namespace BoundaryWordElliptic

open Complex intervalIntegral
open Jacobians.ProjectiveCurve

/-- Cauchy on the box for the `word_R1` integrand: `∮ (c·z)·c dz = 0`. -/
theorem rectBoundary_linear_mul_const (c : ℂ) :
    Jacobians.rectBoundaryIntegral (fun z => (c * z) * c) = 0 := by
  refine Jacobians.rectBoundaryIntegral_eq_zero_of_differentiableOn ?_
  exact (differentiable_id.const_mul c |>.mul_const c).differentiableOn

/-- `∫₀¹ (t : ℂ) dt = 1/2`. -/
theorem integral_coe_id : (∫ t in (0:ℝ)..1, (t : ℂ)) = 1 / 2 := by
  have h : (∫ t in (0:ℝ)..1, (t : ℝ)) = 1 / 2 := by
    rw [integral_id]
    norm_num
  rw [show (∫ t in (0:ℝ)..1, (t : ℂ))
      = ((∫ t in (0:ℝ)..1, (t : ℝ) : ℝ) : ℂ) from
    intervalIntegral.integral_ofReal, h]
  norm_num

/-- The conjugate of an affine path integrates to the conjugate affine
midpoint value: `∫₀¹ conj (p + t·q) dt = conj p + conj q / 2`. -/
theorem integral_conj_affine (p q : ℂ) :
    (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (p + (t : ℂ) * q))
      = (starRingEnd ℂ) p + (starRingEnd ℂ) q / 2 := by
  have hfun : ∀ t : ℝ, (starRingEnd ℂ) (p + (t : ℂ) * q)
      = (starRingEnd ℂ) p + (t : ℂ) * (starRingEnd ℂ) q := by
    intro t
    rw [map_add, map_mul, Complex.conj_ofReal]
  rw [intervalIntegral.integral_congr fun t _ => hfun t]
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) * (starRingEnd ℂ) q)
      MeasureTheory.volume 0 1 :=
    (Complex.continuous_ofReal.mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add
    (f := fun _ : ℝ => (starRingEnd ℂ) p)
    (g := fun t : ℝ => (t : ℂ) * (starRingEnd ℂ) q)
    (continuous_const.intervalIntegrable _ _) hint,
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    integral_coe_id]
  simp
  ring

/-- **The area integral** for the `word_R2` integrand:
`boundaryForm (const c) (c·z) = normSq c · 2i`. -/
theorem boundaryForm_const_linear (c : ℂ) :
    Jacobians.boundaryForm (fun _ => c) (fun z => c * z)
      = (Complex.normSq c : ℂ) * (2 * Complex.I) := by
  have hker : ∀ w : ℂ,
      (starRingEnd ℂ) (c * w) * c
      = (Complex.normSq c : ℂ) * (starRingEnd ℂ) w := by
    intro w
    rw [map_mul]
    calc (starRingEnd ℂ) c * (starRingEnd ℂ) w * c
        = ((starRingEnd ℂ) c * c) * (starRingEnd ℂ) w := by ring
      _ = (Complex.normSq c : ℂ) * (starRingEnd ℂ) w := by
          rw [← Complex.normSq_eq_conj_mul_self]
  have hw : ∀ x y : ℝ, (Jacobians.wCLM (x, y) : ℂ)
      = (x : ℂ) + (y : ℂ) * Complex.I := by
    intro x y
    show Complex.equivRealProdCLM.symm (x, y) = _
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  unfold Jacobians.boundaryForm
  -- rewrite each of the four edges into the affine form and integrate
  have e₁ : (∫ x in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 0))) *
        (fun _ => c) (Jacobians.wCLM (x, 0)))
      = (Complex.normSq c : ℂ) * (1 / 2) := by
    have : ∀ x : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 0))) *
        (fun _ => c) (Jacobians.wCLM (x, 0))
        = (Complex.normSq c : ℂ) * (starRingEnd ℂ) ((0 : ℂ) + (x : ℂ) * 1) := by
      intro x
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun x _ => this x,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    norm_num
  have e₂ : (∫ y in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (1, y))) *
        (fun _ => c) (Jacobians.wCLM (1, y)))
      = (Complex.normSq c : ℂ) * (1 - Complex.I / 2) := by
    have : ∀ y : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (1, y))) *
        (fun _ => c) (Jacobians.wCLM (1, y))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((1 : ℂ) + (y : ℂ) * Complex.I) := by
      intro y
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun y _ => this y,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
    ring
  have e₃ : (∫ x in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 1))) *
        (fun _ => c) (Jacobians.wCLM (x, 1)))
      = (Complex.normSq c : ℂ) * (1 / 2 - Complex.I) := by
    have : ∀ x : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 1))) *
        (fun _ => c) (Jacobians.wCLM (x, 1))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((Complex.I : ℂ) + (x : ℂ) * 1) := by
      intro x
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun x _ => this x,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
    ring
  have e₄ : (∫ y in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (0, y))) *
        (fun _ => c) (Jacobians.wCLM (0, y)))
      = (Complex.normSq c : ℂ) * (-Complex.I / 2) := by
    have : ∀ y : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (0, y))) *
        (fun _ => c) (Jacobians.wCLM (0, y))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((0 : ℂ) + (y : ℂ) * Complex.I) := by
      intro y
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun y _ => this y,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
  rw [e₁, e₂, e₃, e₄]
  ring_nf

/-! ### Stage 2: the elliptic data — singleton form basis and oriented loops -/

section EllipticData

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

noncomputable instance uniqueFinGenus :
    Unique (Fin (genus (Elliptic ω₁ ω₂ h))) :=
  Equiv.unique (finCongr (genus_Elliptic_eq_one ω₁ ω₂ h))

/-- The singleton basis of holomorphic 1-forms on the torus, on the
invariant differential `ellipticDz`. -/
noncomputable def ellipticFormBasis :
    Module.Basis (Fin (genus (Elliptic ω₁ ω₂ h))) ℂ
      (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) :=
  basisOfLinearIndependentOfCardEqFinrank
    ((linearIndependent_unique_iff
      (v := fun _ : Fin (genus (Elliptic ω₁ ω₂ h)) =>
        ellipticDz ω₁ ω₂ h)).mpr (ellipticDz_ne_zero ω₁ ω₂ h))
    (by
      rw [Fintype.card_fin]
      rfl)

@[simp]
theorem ellipticFormBasis_apply (i : Fin (genus (Elliptic ω₁ ω₂ h))) :
    ellipticFormBasis ω₁ ω₂ h i = ellipticDz ω₁ ω₂ h := by
  have hcoe : ⇑(ellipticFormBasis ω₁ ω₂ h)
      = fun _ => ellipticDz ω₁ ω₂ h :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact congrFun hcoe i

/-- The B-cycle reversed, as an `AnalyticLoop` (for orientation
normalization). -/
noncomputable def bLoopRev : AnalyticLoop (Elliptic ω₁ ω₂ h) 0 where
  arc := (bLoop ω₁ ω₂ h).arc.reverse
  start_eq := by
    rw [AnalyticArc.reverse_extend_zero]
    exact (bLoop ω₁ ω₂ h).end_eq
  end_eq := by
    rw [AnalyticArc.reverse_extend_one]
    exact (bLoop ω₁ ω₂ h).start_eq

/-- The oriented elliptic loop family: `aLoop` in the A-slot; in the B-slot
`bLoop` or its reverse, so that the imaginary part of `ω₂'·conj ω₁` is
positive. -/
noncomputable def ellipticLoops :
    Fin (2 * genus (Elliptic ω₁ ω₂ h)) → AnalyticLoop (Elliptic ω₁ ω₂ h) 0 :=
  fun i =>
    if (i : ℕ) = 0 then aLoop ω₁ ω₂ h
    else if 0 < (ω₂ * (starRingEnd ℂ) ω₁).im then bLoop ω₁ ω₂ h
    else bLoopRev ω₁ ω₂ h

end EllipticData

/-! ### Stage 3: period entries, the orientation constant, and the datum -/

section Stage3

open Jacobians.Axioms Matrix
open scoped ComplexOrder

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

include h in
/-- ℝ-independent periods have `Im (ω₂ · conj ω₁) ≠ 0` (the lattice
determinant). -/
theorem im_mul_conj_ne_zero : (ω₂ * (starRingEnd ℂ) ω₁).im ≠ 0 := by
  intro h0
  have hpair := LinearIndependent.pair_iff.mp h
  have hexp := Complex.mul_im ω₂ ((starRingEnd ℂ) ω₁)
  rw [Complex.conj_re, Complex.conj_im, h0] at hexp
  -- hexp : 0 = ω₂.re * -ω₁.im + ω₂.im * ω₁.re
  have h1 : (ω₂.im : ℝ) • ω₁ + (-ω₁.im : ℝ) • ω₂ = 0 := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linear_combination -hexp
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      ring
  obtain ⟨h2im, h1im'⟩ := hpair _ _ h1
  have h1im : ω₁.im = 0 := by linarith [neg_eq_zero.mp h1im']
  have h2 : (ω₂.re : ℝ) • ω₁ + (-ω₁.re : ℝ) • ω₂ = 0 := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im,
        h1im, h2im]
      ring
  obtain ⟨h2re, h1re'⟩ := hpair _ _ h2
  have h1re : ω₁.re = 0 := neg_eq_zero.mp h1re'
  have hω₁ : ω₁ = 0 := Complex.ext (by simp [h1re]) (by simp [h1im])
  have := hpair 1 0 (by simp [hω₁])
  exact one_ne_zero this.1

/-- The oriented second period: `ω₂` or `−ω₂`, chosen so that
`Im (ω₂' · conj ω₁) = |Im (ω₂ · conj ω₁)| ≥ 0`. -/
noncomputable def orientedPeriod : ℂ :=
  if 0 < (ω₂ * (starRingEnd ℂ) ω₁).im then ω₂ else -ω₂

theorem orientedPeriod_im :
    (orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁).im
      = |(ω₂ * (starRingEnd ℂ) ω₁).im| := by
  unfold orientedPeriod
  split_ifs with hpos
  · exact (abs_of_pos hpos).symm
  · rw [not_lt] at hpos
    rw [neg_mul, Complex.neg_im, abs_of_nonpos hpos]

/-- The orientation constant `c := √|Im (ω₂ · conj ω₁)|`, normalizing the
boundary-word area integral to the lattice determinant. -/
noncomputable def orientationConstant : ℝ :=
  Real.sqrt |(ω₂ * (starRingEnd ℂ) ω₁).im|

theorem normSq_orientationConstant :
    Complex.normSq ((orientationConstant ω₁ ω₂ : ℝ) : ℂ)
      = |(ω₂ * (starRingEnd ℂ) ω₁).im| := by
  rw [Complex.normSq_ofReal, orientationConstant]
  exact Real.mul_self_sqrt (abs_nonneg _)

include h in
theorem orientationConstant_pos : 0 < orientationConstant ω₁ ω₂ :=
  Real.sqrt_pos.mpr (abs_pos.mpr (im_mul_conj_ne_zero ω₁ ω₂ h))

/-- The A-slot of `ellipticLoops` is `aLoop`. -/
theorem ellipticLoops_αEmbed (i : Fin (genus (Elliptic ω₁ ω₂ h))) :
    ellipticLoops ω₁ ω₂ h (αEmbed i) = aLoop ω₁ ω₂ h := by
  have hi : ((αEmbed i : Fin (2 * genus (Elliptic ω₁ ω₂ h))) : ℕ) = 0 := by
    change (i : ℕ) = 0
    have hg := genus_Elliptic_eq_one ω₁ ω₂ h
    have := i.isLt
    omega
  simp [ellipticLoops, hi]

/-- The B-slot of `ellipticLoops` is the orientation-normalized B-cycle. -/
theorem ellipticLoops_βEmbed (i : Fin (genus (Elliptic ω₁ ω₂ h))) :
    ellipticLoops ω₁ ω₂ h (βEmbed i)
      = if 0 < (ω₂ * (starRingEnd ℂ) ω₁).im then bLoop ω₁ ω₂ h
        else bLoopRev ω₁ ω₂ h := by
  have hi : ((βEmbed i : Fin (2 * genus (Elliptic ω₁ ω₂ h))) : ℕ) ≠ 0 := by
    change genus (Elliptic ω₁ ω₂ h) + (i : ℕ) ≠ 0
    have hg := genus_Elliptic_eq_one ω₁ ω₂ h
    omega
  simp only [ellipticLoops]
  rw [if_neg hi]

/-- **A-period entry**: every entry of the elliptic arc-A-period matrix is
`ω₁`. -/
theorem arcAPeriodMatrix_elliptic (i j : Fin (genus (Elliptic ω₁ ω₂ h))) :
    arcAPeriodMatrix (ellipticLoops ω₁ ω₂ h)
      (fun m => ellipticFormBasis ω₁ ω₂ h m) i j = ω₁ := by
  rw [arcAPeriodMatrix_apply, ellipticLoops_αEmbed]
  simp [ellipticFormBasis_apply, aLoop_period_eq]

/-- **B-period entry**: every entry of the elliptic arc-B-period matrix is
the oriented period `ω₂'`. -/
theorem arcBPeriodMatrix_elliptic (i j : Fin (genus (Elliptic ω₁ ω₂ h))) :
    arcBPeriodMatrix (ellipticLoops ω₁ ω₂ h)
      (fun m => ellipticFormBasis ω₁ ω₂ h m) i j
      = orientedPeriod ω₁ ω₂ := by
  rw [arcBPeriodMatrix_apply, ellipticLoops_βEmbed]
  unfold orientedPeriod
  split_ifs with hpos
  · simp [ellipticFormBasis_apply, bLoop_period_eq]
  · rw [show (bLoopRev ω₁ ω₂ h).arc = (bLoop ω₁ ω₂ h).arc.reverse from rfl]
    simp [ellipticFormBasis_apply, canonicalArcIntegral_reverse, bLoop_period_eq]

/-- The `word_R2` left side collapses to `−|Im (ω₂ · conj ω₁)| · 2i`. -/
theorem elliptic_word_R2_lhs :
    ω₁ * (starRingEnd ℂ) (orientedPeriod ω₁ ω₂)
        - orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁
      = -((|(ω₂ * (starRingEnd ℂ) ω₁).im| : ℝ) * (2 * Complex.I)) := by
  have hsub := Complex.sub_conj (orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁)
  have hconj : ω₁ * (starRingEnd ℂ) (orientedPeriod ω₁ ω₂)
      = (starRingEnd ℂ) (orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hconj, ← orientedPeriod_im ω₁ ω₂,
    show (starRingEnd ℂ) (orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁)
        - orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁
      = -(orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁
          - (starRingEnd ℂ) (orientedPeriod ω₁ ω₂ * (starRingEnd ℂ) ω₁)) from by
      ring, hsub]
  push_cast
  ring

/-- **The g = 1 boundary-word witness**: the interior-form comparison datum
for the elliptic curve, over the oriented loops and the `dz` basis, with
constant cut pullback `h := c` and linear primitive `F := c·z` for the
orientation constant `c = √|Im (ω₂ · conj ω₁)|`. All fields are explicit;
no axiom enters (in particular neither `AX_PeriodCycleBasis` nor
`AX_Elliptic_H1_symplectic`). -/
noncomputable def ellipticArcBoundaryWordData :
    ArcBoundaryWordDataInterior (ellipticLoops ω₁ ω₂ h)
      (ellipticFormBasis ω₁ ω₂ h) where
  h := fun _ _ => (orientationConstant ω₁ ω₂ : ℂ)
  F := fun _ z => (orientationConstant ω₁ ω₂ : ℂ) * z
  hhc := fun _ => continuousOn_const
  hFc := fun _ => (continuous_const.mul continuous_id).continuousOn
  hh := fun _ z _ => by
    simpa using hasDerivAt_const z ((orientationConstant ω₁ ω₂ : ℝ) : ℂ)
  hF := fun _ z _ => by
    simpa using (hasDerivAt_id z).const_mul ((orientationConstant ω₁ ω₂ : ℝ) : ℂ)
  word_R1 := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      arcAPeriodMatrix_elliptic ω₁ ω₂ h, arcBPeriodMatrix_elliptic ω₁ ω₂ h]
    rw [rectBoundary_linear_mul_const, sub_eq_zero]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  word_R2 := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, arcAPeriodMatrix_elliptic ω₁ ω₂ h,
      arcBPeriodMatrix_elliptic ω₁ ω₂ h, Fintype.sum_unique]
    rw [boundaryForm_const_linear, normSq_orientationConstant]
    exact elliptic_word_R2_lhs ω₁ ω₂
  nondeg := by
    intro v hv
    refine ⟨(1 / 2, 1 / 2),
      ⟨Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩,
        Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩⟩, ?_⟩
    rw [Fintype.sum_unique]
    have hvd : v default ≠ 0 := by
      intro h0
      apply hv
      funext j
      rw [Unique.eq_default j]
      simpa using h0
    exact mul_ne_zero hvd
      (Complex.ofReal_ne_zero.mpr (orientationConstant_pos ω₁ ω₂ h).ne')

/-- **R1 at g = 1, concrete and axiom-free**: the elliptic arc-period blocks
commute. -/
theorem elliptic_periodMatrix_symm :
    (arcAPeriodMatrix (ellipticLoops ω₁ ω₂ h)
        fun m => ellipticFormBasis ω₁ ω₂ h m)ᵀ
        * (arcBPeriodMatrix (ellipticLoops ω₁ ω₂ h)
            fun m => ellipticFormBasis ω₁ ω₂ h m)
      = (arcBPeriodMatrix (ellipticLoops ω₁ ω₂ h)
            fun m => ellipticFormBasis ω₁ ω₂ h m)ᵀ
        * (arcAPeriodMatrix (ellipticLoops ω₁ ω₂ h)
            fun m => ellipticFormBasis ω₁ ω₂ h m) :=
  (ellipticArcBoundaryWordData ω₁ ω₂ h).periodMatrix_symm

/-- **R2 at g = 1, concrete and axiom-free**: the elliptic arc-period Gram
matrix is positive definite. -/
theorem elliptic_periodGram_posDef :
    (arcPeriodGram (ellipticLoops ω₁ ω₂ h)
      fun m => ellipticFormBasis ω₁ ω₂ h m).PosDef :=
  (ellipticArcBoundaryWordData ω₁ ω₂ h).periodGram_posDef

/-- **Conditional g = 1 `PeriodCycleBasis`**: given the H₁ topology fields
for the oriented elliptic loops (the sole remaining content of
`AX_Elliptic_H1_symplectic`), the boundary-word datum completes a full
`PeriodCycleBasis` witness with both Hodge fields PROVEN. -/
noncomputable def ellipticPeriodCycleBasisOfH1
    (isBasis : Module.Basis (Fin (2 * genus (Elliptic ω₁ ω₂ h))) ℤ
      (H1 (Elliptic ω₁ ω₂ h) 0))
    (loops_to_basis : ∀ i, isBasis i
      = loopToHomology (ellipticLoops ω₁ ω₂ h i)) :
    PeriodCycleBasis (Elliptic ω₁ ω₂ h) 0 :=
  periodCycleBasisOfBoundaryWordInterior isBasis loops_to_basis
    (ellipticArcBoundaryWordData ω₁ ω₂ h)

end Stage3

end BoundaryWordElliptic
end Jacobians.RiemannSurface
