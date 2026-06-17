import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic
import Jacobians.GeneralResults.ChartTransition

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Polynomial

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- Custom induction principle for `HyperellipticOdd H h` to avoid unfolding it to
`OnePoint (HyperellipticAffine H)` during proofs. This ensures typeclass search
can find the `ChartedSpace` and `IsManifold` instances. -/
@[elab_as_elim]
protected theorem rec {C : HyperellipticOdd H h → Prop}
    (infty_val : C infty)
    (coe_val : ∀ (a : HyperellipticAffine H), C (a : HyperellipticOdd H h)) :
    ∀ (p : HyperellipticOdd H h), C p := by
  intro p
  change OnePoint (HyperellipticAffine H) at p
  induction p with
  | infty =>
    change C infty
    exact infty_val
  | coe a =>
    change C (coe a)
    exact coe_val a

/-- The unified coefficient family for `g(x) dx / y` on the odd curve `HyperellipticOdd H h`. -/
noncomputable def hyperellipticOddCoeff (g : Polynomial ℂ) (p : HyperellipticOdd H h) :
    ℂ → ℂ := fun z => by
  classical
  let p' : OnePoint (HyperellipticAffine H) := p
  exact p'.elim
    (if hz : z ∈ (infinityChart H h).target then
       if z = 0 then
         -2 * g.coeff (H.genus - 1) / H.f.leadingCoeff
       else
         let x := (infinityInverseMap H h z).val.1
         2 * g.eval x * x ^ (H.genus + 2) /
           (x * (Polynomial.derivative H.f).eval x - (2 * H.genus + 2) * H.f.eval x)
     else 0)
    (fun a => HyperellipticAffine.hyperellipticAffineCoeff g a z)

theorem hyperellipticOddCoeff_zero :
    hyperellipticOddCoeff (H := H) (h := h) 0 = 0 := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [mul_zero, zero_div]
    · simp only [Polynomial.eval_zero, mul_zero, zero_mul, zero_div]
    · rfl
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_zero]
    rfl

theorem hyperellipticOddCoeff_add (g g' : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (g + g') =
      hyperellipticOddCoeff g + hyperellipticOddCoeff g' := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.add_apply]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_add]
      ring
    · simp only [Polynomial.eval_add]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_add g g']
    rfl

theorem hyperellipticOddCoeff_smul (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (c • g) =
      c • hyperellipticOddCoeff g := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_smul, smul_eq_mul]
      ring
    · simp only [Polynomial.eval_smul, smul_eq_mul]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_smul c g]
    rfl

/-- The coefficient family is zero off each chart target. -/
theorem hyperellipticOddCoeff_isZeroOffChartTarget (g : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro p z hz
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    unfold hyperellipticOddCoeff
    have hExt : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target := by
      change Set.univ ∩ (chartAt (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target
      rw [Set.univ_inter]
      rfl
    rw [hExt] at hz
    dsimp [infty] at *
    split_ifs
    rfl
  | coe_val a =>
    unfold hyperellipticOddCoeff
    have hExt_lift : (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).target =
        (extChartAt 𝓘(ℂ, ℂ) a).target := by
      change Set.univ ∩ (chartAt (a : HyperellipticOdd H h)).target =
        Set.univ ∩ (ChartedSpace.chartAt a).target
      dsimp [coe, HyperellipticOdd.coe]
      rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hExt_lift] at hz
    dsimp [coe] at *
    exact HyperellipticAffine.hyperellipticAffineCoeff_isZeroOffChartTarget g a z hz

/-- The coefficient family is analytic on the affine charts. -/
theorem hyperellipticOddCoeff_analyticOn_affineLift
    (g : Polynomial ℂ) (a : HyperellipticAffine H) :
    AnalyticOn ℂ (hyperellipticOddCoeff (h := h) g (coe a))
      (affineLiftChart (h := h) a).target := by
  have hCoeff : hyperellipticOddCoeff (h := h) g (coe a) =
      HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
  rw [hCoeff]
  have hLift : (affineLiftChart (h := h) a).target = (extChartAt 𝓘(ℂ, ℂ) a).target := by
    change (affineLiftChart (h := h) a).target = Set.univ ∩ (ChartedSpace.chartAt a).target
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [Set.univ_inter]
  rw [hLift]
  exact HyperellipticAffine.hyperellipticAffineCoeff_isHolomorphicOneFormCoeff g a

/-- Same-summand cocycle equation holds on overlaps of affine charts. -/
theorem hyperellipticOddCoeff_cocycle_coe_coe (g : Polynomial ℂ) (p q : HyperellipticAffine H)
    {z : ℂ} (hz : z ∈ (affineLiftChart (h := h) p).target)
    (hsrc : (affineLiftChart (h := h) p).symm z ∈ (affineLiftChart (h := h) q).source) :
    hyperellipticOddCoeff (h := h) g (coe p) z =
      hyperellipticOddCoeff (h := h) g (coe q) ((affineLiftChart (h := h) q)
        ((affineLiftChart (h := h) p).symm z)) *
        (fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z 1) := by
  have hp : hyperellipticOddCoeff (h := h) g (coe p) =
      HyperellipticAffine.hyperellipticAffineCoeff g p := rfl
  have hq : hyperellipticOddCoeff (h := h) g (coe q) =
      HyperellipticAffine.hyperellipticAffineCoeff g q := rfl
  rw [hp, hq]
  have hExt_target : (extChartAt 𝓘(ℂ, ℂ) p).target = (affineLiftChart (h := h) p).target := by
    change Set.univ ∩ (ChartedSpace.chartAt p).target = (affineLiftChart (h := h) p).target
    rw [Set.univ_inter]
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
  have hz_aff : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target := by
    rw [hExt_target]; exact hz
  have hsrc_aff : (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q).source := by
    rw [extChartAt_source 𝓘(ℂ, ℂ) q]
    have hSymm : (extChartAt 𝓘(ℂ, ℂ) p).symm z =
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z := rfl
    rw [hSymm]
    have hsrc' := hsrc
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc'
    obtain ⟨w, hw, heq⟩ := hsrc'
    have heq' : w = (ChartedSpace.chartAt p : OpenPartialHomeomorph
      (HyperellipticAffine H) ℂ).symm z := by
      exact OnePoint.coe_injective heq
    rw [← heq']
    exact hw
  have hLift_apply : (affineLiftChart (h := h) q) ((affineLiftChart (h := h) p).symm z) =
      (ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ)
        ((ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z) := by
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      Function.comp_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hLift_apply]
  have hFderiv : fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z =
      fderiv ℂ ((ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) ∘
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm) z := by
    refine Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (s := (affineLiftChart (h := h) p).target) ?_ ?_)
    · exact (affineLiftChart (h := h) p).open_target.mem_nhds hz
    · intro w hw
      simp only [Function.comp_apply, affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hFderiv]
  exact HyperellipticAffine.hyperellipticAffineCoeff_satisfiesCotangentCocycle
    g p q z hz_aff hsrc_aff

lemma coeff_X_mul_derivative_eq (p : Polynomial ℂ) (i : ℕ) :
    (X * p.derivative).coeff i = (i : ℂ) * p.coeff i := by
  cases i
  · simp
  · simp [coeff_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]

lemma poly_rev_id (f : Polynomial ℂ) (N : ℕ) (hN : f.natDegree = N) :
    X * f.derivative - C (N + 1 : ℂ) * f =
      - reflect N (f.reverse + X * f.reverse.derivative) := by
  ext i
  rw [coeff_sub, coeff_C_mul, coeff_neg, coeff_reflect]
  rw [coeff_add, coeff_X_mul_derivative_eq, coeff_X_mul_derivative_eq]
  simp only [coeff_reverse, hN]
  dsimp [revAt]
  by_cases h1 : i ≤ N
  · have h2 : N - i ≤ N := by omega
    simp only [h1, h2, ite_true]
    have h_eq : N - (N - i) = i := by omega
    simp only [h_eq]
    rw [Nat.cast_sub h1]
    ring
  · simp only [h1, ite_false]
    have h_zero : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by linarith)
    simp [h_zero]

lemma natDegree_le_N (f : Polynomial ℂ) (N : ℕ) (hN : f.natDegree = N) :
    (f.reverse + X * f.reverse.derivative).natDegree ≤ N := by
  have h1 : f.reverse.natDegree ≤ N := by
    calc f.reverse.natDegree ≤ f.natDegree := reverse_natDegree_le f
      _ = N := hN
  have h2 : (X * f.reverse.derivative).natDegree ≤ N := by
    by_cases h0 : f.reverse.natDegree = 0
    · have hc : f.reverse = C (f.reverse.coeff 0) := eq_C_of_natDegree_eq_zero h0
      have hd : f.reverse.derivative = 0 := by
        rw [hc, derivative_C]
      simp [hd]
    · calc (X * f.reverse.derivative).natDegree ≤
          X.natDegree + f.reverse.derivative.natDegree :=
        natDegree_mul_le
        _ = 1 + f.reverse.derivative.natDegree := by rw [natDegree_X]
        _ ≤ 1 + (f.reverse.natDegree - 1) := by
          have hd := natDegree_derivative_le f.reverse
          omega
        _ ≤ N := by omega
  calc (f.reverse + X * f.reverse.derivative).natDegree ≤
        max f.reverse.natDegree (X * f.reverse.derivative).natDegree :=
      natDegree_add_le _ _
    _ ≤ N := max_le h1 h2

lemma eval_reflect_eq (p : Polynomial ℂ) (N : ℕ) (hp : p.natDegree ≤ N) (W : ℂ) (hW : W ≠ 0) :
    (reflect N p).eval (W⁻¹ ^ 2) = W⁻¹ ^ (2 * N) * p.eval (W ^ 2) := by
  letI : Invertible (W ^ 2) := invertibleOfNonzero (pow_ne_zero 2 hW)
  have h1 := eval₂_reflect_mul_pow (RingHom.id ℂ) (W ^ 2) N p hp
  simp only [eval₂_id] at h1
  have h2 : ⅟(W ^ 2) = W⁻¹ ^ 2 := by
    simp [invOf_eq_inv, ← inv_pow]
  rw [h2] at h1
  have h3 : (W ^ 2) ^ N = W ^ (2 * N) := by ring
  rw [h3] at h1
  have hz : W ^ (2 * N) ≠ 0 := pow_ne_zero _ hW
  have h4 := congr_arg (fun y => y * (W ^ (2 * N))⁻¹) h1
  dsimp at h4
  rw [mul_assoc, mul_inv_cancel₀ hz, mul_one] at h4
  rw [h4]
  simp [inv_pow]
  ring

lemma x_fderiv_sub_f_eq {H : HyperellipticData} (hOdd : Odd H.f.natDegree) (W : ℂ) (hW : W ≠ 0) :
    let x := W⁻¹ ^ 2
    x * H.f.derivative.eval x - (2 * H.genus + 2) * H.f.eval x =
      - W⁻¹ ^ (4 * H.genus + 2) *
        (H.f.reverse.eval (W ^ 2) + W ^ 2 * H.f.reverse.derivative.eval (W ^ 2)) := by
  intro x
  have h_deg : 2 * H.genus + 2 = H.f.natDegree + 1 := by
    obtain ⟨k, hk⟩ := hOdd
    have h1 : H.f.natDegree = 2 * k + 1 := hk
    have h2 : H.genus = k := by
      dsimp [HyperellipticData.genus]
      omega
    omega
  have h_degC : (2 * H.genus + 2 : ℂ) = (H.f.natDegree + 1 : ℂ) := by
    exact_mod_cast h_deg
  rw [h_degC]
  have H_id := poly_rev_id H.f H.f.natDegree rfl
  have H_eval := congr_arg (fun P : Polynomial ℂ => P.eval x) H_id
  dsimp at H_eval
  rw [eval_sub, eval_mul, eval_X, eval_mul, eval_C] at H_eval
  rw [H_eval]
  have H_reflect := eval_reflect_eq (H.f.reverse + X * H.f.reverse.derivative) H.f.natDegree
    (natDegree_le_N H.f H.f.natDegree rfl) W hW
  rw [eval_neg]
  rw [H_reflect]
  have h_pow : 2 * H.f.natDegree = 4 * H.genus + 2 := by
    obtain ⟨k, hk⟩ := hOdd
    have h1 : H.f.natDegree = 2 * k + 1 := hk
    have h2 : H.genus = k := by
      dsimp [HyperellipticData.genus]
      omega
    omega
  rw [h_pow]
  rw [eval_add, eval_mul, eval_X]
  ring

/-- **Implicit differentiation of `t(w)² = w² · f_rev(w²)`**.

Differentiating both sides gives
`2 t(w) t'(w) = 2w f_rev(w²) + 2w³ f_rev'(w²)`, i.e.
`t'(w) · t(w) = w · (f_rev(w²) + w² · f_rev'(w²))`.

Used to compute `deriv(t)(w)` in terms of the reverse polynomial
and its derivative, which feeds into the cocycle identity. -/
private lemma deriv_t_mul_t (w : ℂ) (hw : w ∈ InfinityInverse.U_S H) :
    deriv (InfinityInverse.t H) w * InfinityInverse.t H w =
      w * (H.f.reverse.eval (w ^ 2) +
        w ^ 2 * H.f.reverse.derivative.eval (w ^ 2)) := by
  have ht_ana := InfinityInverse.t_analyticAt_of_mem H hw
  have ht_hda := ht_ana.differentiableAt.hasDerivAt
  have hLHS : HasDerivAt (fun w => (InfinityInverse.t H w) ^ 2)
    (2 * InfinityInverse.t H w * deriv (InfinityInverse.t H) w) w :=
    (ht_hda.pow 2).congr_deriv (by ring)
  have hw2 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * w) w := by
    have := hasDerivAt_pow 2 w; simpa using this
  have hrev : HasDerivAt (fun w : ℂ => H.f.reverse.eval (w ^ 2))
    (H.f.reverse.derivative.eval (w ^ 2) * (2 * w)) w := by
    have := (H.f.reverse.hasDerivAt (w ^ 2)).comp w hw2
    convert this using 1
  have hRHS : HasDerivAt (fun w => w ^ 2 * H.f.reverse.eval (w ^ 2))
    (2 * w * (H.f.reverse.eval (w ^ 2) +
      w ^ 2 * H.f.reverse.derivative.eval (w ^ 2))) w := by
    have := hw2.mul hrev; convert this using 1; ring
  have h_eq : (fun w => (InfinityInverse.t H w) ^ 2) =
    (fun w => w ^ 2 * H.f.reverse.eval (w ^ 2)) := by
    ext w; exact InfinityInverse.t_sq H w
  have huniq := hLHS.unique (h_eq ▸ hRHS)
  -- huniq : 2*t(w)*t'(w) = 2*w*(...)
  -- Goal: t'(w)*t(w) = w*(...)
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have h1 : InfinityInverse.t H w *
      deriv (InfinityInverse.t H) w =
    w * (H.f.reverse.eval (w ^ 2) +
      w ^ 2 * H.f.reverse.derivative.eval (w ^ 2)) := by
    have : 2 * (InfinityInverse.t H w *
        deriv (InfinityInverse.t H) w) =
      2 * (w * (H.f.reverse.eval (w ^ 2) +
        w ^ 2 * H.f.reverse.derivative.eval (w ^ 2))) := by
      linear_combination huniq
    exact mul_left_cancel₀ h2ne this
  linear_combination h1

/-- **Key identity for the infinity-to-affine cocycle**.

At a point `z ≠ 0` in the infinity chart target, the derivative of the
chart transition `z ↦ w(z)⁻¹ ^ 2` (where `w = tLocalHomeomorph.symm z`)
satisfies:
```
fderiv(z ↦ w(z)⁻²)(z)(1) =
  2 * (w⁻²)^(g+2) * y / (w⁻² * f'(w⁻²) - (2g+2) * f(w⁻²))
```
where `y = squareLocalHomeomorph.symm(f.eval(w⁻²))` is the y-branch.

Mathematically this is the identity `dx/dt = 2x^(g+2) * y / (x*f'(x) - (2g+2)*f(x))`
at infinity, where `t` is the uniformizer `y/x^(g+1)` and `x = w⁻²`.

Proof requires:
1. `HasDerivAt` for `tLocalHomeomorph.symm` at `z` via the IFT
2. Chain rule for `z ↦ w(z)⁻¹ ^ 2 = w(z)⁻²`
3. The relationship `t'(w) = S(w²) + 2w²S'(w²)` from the
   definition `t(w) = w * S(w²)`
4. Connection between `S(w²)` and the square root branch `y`
-/
theorem infinity_transition_deriv_identity_raw
    (hOdd : Odd H.f.natDegree)
    {z : ℂ}
    (hzt : z ∈ (InfinityInverse.tLocalHomeomorph H).target)
    (hzne : z ≠ 0) :
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    HasDerivAt (fun z => ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2)
      (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) /
        (w⁻¹ ^ 2 * (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
          (2 * H.genus + 2) * H.f.eval (w⁻¹ ^ 2))) z := by
  let w := (InfinityInverse.tLocalHomeomorph H).symm z
  -- Step 1: w is differentiable at z (from ContDiffOn ω of tLH.symm)
  have hw_diff : DifferentiableAt ℂ
      (InfinityInverse.tLocalHomeomorph H).symm z := by
    exact ((tLocalHomeomorph_symm_contDiffOn H).differentiableOn
      (hn := by simp [WithTop.top_ne_zero])).differentiableAt
      ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
        hzt)
  -- Step 2: w ≠ 0 (since t(0) = 0 and z ≠ 0)
  have hw_ne : w ≠ 0 := by
    intro hc
    have h_lv :=
      (InfinityInverse.tLocalHomeomorph H).right_inv hzt
    rw [show (InfinityInverse.tLocalHomeomorph H).symm z = w
      from rfl, hc] at h_lv
    rw [InfinityInverse.tLocalHomeomorph_coe H] at h_lv
    simp [InfinityInverse.t, InfinityInverse.S] at h_lv
    exact hzne h_lv.symm
  -- Step 3: w ∈ tLH.source, t is analytic at w
  have hw_source :
      w ∈ (InfinityInverse.tLocalHomeomorph H).source :=
    (InfinityInverse.tLocalHomeomorph H).map_target hzt
  have hw_US : w ∈ InfinityInverse.U_S H := hw_source.2
  have ht_ana : AnalyticAt ℂ (InfinityInverse.t H) w :=
    InfinityInverse.t_analyticAt_of_mem H hw_US
  -- Step 4: t has a derivative at w, and it's nonzero
  have ht_hda : HasDerivAt (InfinityInverse.t H)
      (deriv (InfinityInverse.t H) w) w :=
    ht_ana.differentiableAt.hasDerivAt
  -- Lift to tLocalHomeomorph
  have ht_hda_lh : HasDerivAt
      (InfinityInverse.tLocalHomeomorph H)
      (deriv (InfinityInverse.t H) w) w := by
    rwa [← InfinityInverse.tLocalHomeomorph_coe H]
  -- deriv(t)(w) ≠ 0 (since tLH is a local homeomorph)
  have ht_deriv_ne :
      deriv (InfinityInverse.t H) w ≠ 0 := by
    intro h_zero
    -- t ∘ tLH.symm =ᶠ[nhds z] id near z
    have h_ev : ↑(InfinityInverse.tLocalHomeomorph H) ∘
        ↑(InfinityInverse.tLocalHomeomorph H).symm
        =ᶠ[nhds z] id := by
      rw [Filter.EventuallyEq]
      exact Filter.eventually_of_mem
        ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
          hzt) fun x hx => by
        simp [(InfinityInverse.tLocalHomeomorph H).right_inv hx]
    -- HasDerivAt t 0 w (since h_zero says deriv = 0)
    have ht_hda_zero : HasDerivAt
        ↑(InfinityInverse.tLocalHomeomorph H) 0 w := by
      rw [← h_zero]; exact ht_hda_lh
    -- Apply the key Mathlib lemma
    exact absurd hw_diff
      (not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
        ht_hda_zero h_ev)
  -- Step 5: HasDerivAt for tLH.symm via IFT
  have hw_hda_symm : HasDerivAt
      (↑(InfinityInverse.tLocalHomeomorph H).symm)
      (deriv (InfinityInverse.t H) w)⁻¹ z :=
    (InfinityInverse.tLocalHomeomorph H).hasDerivAt_symm
      hzt ht_deriv_ne ht_hda_lh
  -- Step 6: Chain rule for z ↦ (tLH.symm z)⁻¹ ^ 2
  -- deriv = deriv(u ↦ u⁻¹^2)(w) * (t'(w))⁻¹ = (-2w⁻³) / t'(w)
  have hinv_sq_deriv : HasDerivAt
      (fun u : ℂ => u⁻¹ ^ 2) (-2 * w ^ (-3 : ℤ)) w := by
    have h1 : HasDerivAt Inv.inv (-(w ^ 2)⁻¹) w :=
      hasDerivAt_inv hw_ne
    have h2 : HasDerivAt (· ^ 2) (2 * w⁻¹) (w⁻¹) := by
      simpa using hasDerivAt_pow 2 w⁻¹
    have h3 := h2.comp w h1
    convert h3 using 1
    field_simp
  have hcomp : HasDerivAt
      (fun z =>
        ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2)
      ((-2 * w ^ (-3 : ℤ)) *
        (deriv (InfinityInverse.t H) w)⁻¹) z := by
    convert hinv_sq_deriv.comp z hw_hda_symm using 1
  refine hcomp.congr_deriv ?_
  -- Step 7: Implicit differentiation of t(w)² = w² * f_rev(w²)
  -- Differentiating the LHS: 2 * t(w) * t'(w)
  have ht_sq_hda : HasDerivAt
      (fun u => (InfinityInverse.t H u) ^ 2)
      (2 * InfinityInverse.t H w *
        deriv (InfinityInverse.t H) w) w :=
    (ht_hda.pow 2).congr_deriv (by ring)
  -- Differentiating the RHS: d/dw[w² * P(w²)]
  -- Product rule: (2w)*P(w²) + w²*(P'(w²)*2w)
  have hrhs_hda : HasDerivAt
      (fun u => u ^ 2 * H.f.reverse.eval (u ^ 2))
      (2 * w * H.f.reverse.eval (w ^ 2) +
        w ^ 2 * ((Polynomial.derivative
          H.f.reverse).eval (w ^ 2) * (2 * w))) w := by
    have h1 : HasDerivAt (fun u : ℂ => u ^ 2)
        (2 * w) w := by
      convert hasDerivAt_pow 2 w using 1; ring
    have h2 : HasDerivAt
        (fun u => H.f.reverse.eval (u ^ 2))
        ((Polynomial.derivative H.f.reverse).eval
          (w ^ 2) * (2 * w)) w := by
      have hP := H.f.reverse.hasDerivAt (w ^ 2)
      have hw2 : HasDerivAt (fun u : ℂ => u ^ 2)
          (2 * w) w := by
        convert hasDerivAt_pow 2 w using 1; ring
      exact hP.comp w hw2
    exact h1.mul h2
  -- Since t² = w² * f_rev(w²), their derivatives agree
  -- t(w) * t'(w) = w * (f_rev(w²) + w² * f_rev'(w²))
  have hderivs_eq :
      2 * InfinityInverse.t H w *
        deriv (InfinityInverse.t H) w =
      2 * w * H.f.reverse.eval (w ^ 2) +
        w ^ 2 * ((Polynomial.derivative
          H.f.reverse).eval (w ^ 2) * (2 * w)) := by
    have h_eq : ∀ u, (InfinityInverse.t H u) ^ 2 =
        u ^ 2 * H.f.reverse.eval (u ^ 2) :=
      fun u => InfinityInverse.t_sq H u
    have hlhs : HasDerivAt
        (fun u => (InfinityInverse.t H u) ^ 2)
        (2 * InfinityInverse.t H w *
          deriv (InfinityInverse.t H) w) w := by
      convert ht_hda.pow 2 using 1; ring
    have hlhs' : HasDerivAt
        (fun u => u ^ 2 * H.f.reverse.eval (u ^ 2))
        (2 * InfinityInverse.t H w *
          deriv (InfinityInverse.t H) w) w := by
      convert hlhs using 1
      ext u; exact (h_eq u).symm
    exact hlhs'.unique hrhs_hda
  set x := w⁻¹ ^ 2 with hx_def
  -- Set up R = f_rev(w²) + w²*f_rev'(w²) using deriv_t_mul_t
  set R := H.f.reverse.eval (w ^ 2) +
    w ^ 2 * H.f.reverse.derivative.eval (w ^ 2) with hR_def
  have h_impl := deriv_t_mul_t w hw_US
  rw [InfinityInverse.tLocalHomeomorph_right_inv H hzt]
    at h_impl
  -- h_impl : t'(w) * z = w * R (after folding R)
  change deriv (InfinityInverse.t H) w * z = w * R at h_impl
  -- R ≠ 0 (from t'(w) ≠ 0 and z ≠ 0)
  have hR_ne : R ≠ 0 := by
    intro hR; rw [hR, mul_zero] at h_impl
    rcases mul_eq_zero.mp h_impl with hh | hh
    · exact ht_deriv_ne hh
    · exact hzne hh
  -- t'(w) = w * R / z
  have h_deriv_val :
      deriv (InfinityInverse.t H) w = w * R / z := by
    field_simp; linear_combination h_impl
  -- D = -w⁻¹^(4g+2) * R (from x_fderiv_sub_f_eq)
  have h_denom := x_fderiv_sub_f_eq hOdd w hw_ne
  -- Substitute and close by field_simp + ring
  rw [h_deriv_val, h_denom, hx_def,
    show w ^ (-3 : ℤ) = (w ^ 3)⁻¹ from zpow_neg w 3]
  field_simp
  -- Rewrite denominator back to R and cancel R/R
  conv_rhs =>
    rw [show eval (w ^ 2) H.f.reverse +
      w ^ 2 * eval (w ^ 2) (derivative H.f.reverse) = R
      from hR_def.symm]
  rw [show w ^ 4 * R * (1 / w ^ 2) ^ (2 * H.genus + 3) / R =
    w ^ 4 * (1 / w ^ 2) ^ (2 * H.genus + 3) from by
      rw [show w ^ 4 * R * (1 / w ^ 2) ^ (2 * H.genus + 3) =
        R * (w ^ 4 * (1 / w ^ 2) ^ (2 * H.genus + 3)) from by ring]
      exact mul_div_cancel_left₀ _ hR_ne]
  congr 1
  rw [show (1 / w ^ 2) ^ (2 * H.genus + 3) = 1 / (w ^ 2) ^ (2 * H.genus + 3) by
    simp [one_div, inv_pow]]
  rw [show (1 / w) ^ (4 * H.genus + 2) = 1 / w ^ (4 * H.genus + 2) by simp [one_div, inv_pow]]
  rw [← pow_mul]
  have h_pow_mul : 2 * (2 * H.genus + 3) = 4 * H.genus + 6 := by ring
  have h_pow_add : 4 * H.genus + 6 = 4 + (4 * H.genus + 2) := by omega
  have hw_pow_ne : w ^ (4 * H.genus + 2) ≠ 0 := pow_ne_zero _ hw_ne
  have hw2_pow_ne : w ^ (4 * H.genus + 6) ≠ 0 := pow_ne_zero _ hw_ne
  field_simp
  rw [h_pow_mul, h_pow_add, pow_add]
  ring

/-- **Key identity for the infinity-to-affine cocycle**.

At a point `z ≠ 0` in the infinity chart target, the derivative of the
chart transition `z ↦ w(z)⁻¹ ^ 2` (where `w = tLocalHomeomorph.symm z`)
satisfies:
```
fderiv(z ↦ w(z)⁻²)(z)(1) =
  2 * (w⁻²)^(g+2) * y / (w⁻² * f'(w⁻²) - (2g+2) * f(w⁻²))
```
where `y = squareLocalHomeomorph.symm(f.eval(w⁻²))` is the y-branch.

Mathematically this is the identity `dx/dt = 2x^(g+2) * y / (x*f'(x) - (2g+2)*f(x))`
at infinity, where `t` is the uniformizer `y/x^(g+1)` and `x = w⁻¹ ^ 2`.

Proof requires:
1. `HasDerivAt` for `tLocalHomeomorph.symm` at `z` via the IFT
2. Chain rule for `z ↦ w(z)⁻¹ ^ 2 = w(z)⁻²`
3. The relationship `t'(w) = S(w²) + 2w²S'(w²)` from the
   definition `t(w) = w * S(w²)`
4. Connection between `S(w²)` and the square root branch `y`
-/
theorem infinity_transition_deriv_identity
    (hOdd : Odd H.f.natDegree)
    (a : HyperellipticAffine H)
    (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
    {z : ℂ}
    (hzt : z ∈ (InfinityInverse.tLocalHomeomorph H).target)
    (hzne : z ≠ 0)
    (_hInTarget : ((InfinityInverse.tLocalHomeomorph H).symm
      z)⁻¹ ^ 2 ∈
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY) :
            OpenPartialHomeomorph
              (HyperellipticAffine H) ℂ).target)
    (hYSrc : z * (((InfinityInverse.tLocalHomeomorph H).symm
      z)⁻¹ ^ 2) ^ (H.genus + 1) ∈
        (a.squareLocalHomeomorph hpY).source) :
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    (fderiv ℂ
      (fun z => ((InfinityInverse.tLocalHomeomorph H).symm
        z)⁻¹ ^ 2) z) 1 =
    2 * (w⁻¹ ^ 2) ^ (H.genus + 2) *
      ((HyperellipticAffine.squareLocalHomeomorph
          (H := H) a hpY).symm
        (H.f.eval (w⁻¹ ^ 2))) /
      (w⁻¹ ^ 2 *
        (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
        (2 * H.genus + 2) *
          H.f.eval (w⁻¹ ^ 2)) := by
  intro w
  have h_raw := infinity_transition_deriv_identity_raw hOdd hzt hzne
  have hBranch : (a.squareLocalHomeomorph hpY).symm
      (H.f.eval (w⁻¹ ^ 2)) =
      z * (w⁻¹ ^ 2) ^ (H.genus + 1) := by
    have hy_sq := InfinityInverse.y_sq_eq_eval_x hOdd z hzt hzne
    have h_left_inv :=
      (a.squareLocalHomeomorph hpY).left_inv hYSrc
    have h_sq_app : (a.squareLocalHomeomorph hpY)
        (z * (w⁻¹ ^ 2) ^ (H.genus + 1)) =
        (z * (w⁻¹ ^ 2) ^ (H.genus + 1)) ^ 2 := by
      simp [HyperellipticAffine.squareLocalHomeomorph]
    rw [h_sq_app, hy_sq] at h_left_inv
    exact h_left_inv
  rw [fderiv_apply_one_eq_deriv, h_raw.deriv, hBranch]
  ring

lemma infinity_transition_denominator_ne_zero {H : HyperellipticData} (h : Odd H.f.natDegree)
    {z : ℂ} (hz : z ∈ (infinityChart H h).target) (h_zero : z ≠ 0) :
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    eval (w ^ 2) H.f.reverse + w ^ 2 * eval (w ^ 2) (derivative H.f.reverse) ≠ 0 := by
  intro w hR
  have hw_ne : w ≠ 0 := by
    intro hc
    have h_lv := (InfinityInverse.tLocalHomeomorph H).right_inv hz
    rw [show (InfinityInverse.tLocalHomeomorph H).symm z = w from rfl, hc] at h_lv
    rw [InfinityInverse.tLocalHomeomorph_coe H] at h_lv
    simp [InfinityInverse.t, InfinityInverse.S] at h_lv
    exact h_zero h_lv.symm
  have hw_source : w ∈ (InfinityInverse.tLocalHomeomorph H).source :=
    (InfinityInverse.tLocalHomeomorph H).map_target hz
  have hw_US : w ∈ InfinityInverse.U_S H := hw_source.2
  have ht_deriv_ne : deriv (InfinityInverse.t H) w ≠ 0 := by
    intro h_zero_deriv
    have h_ev : ↑(InfinityInverse.tLocalHomeomorph H) ∘
        ↑(InfinityInverse.tLocalHomeomorph H).symm
        =ᶠ[nhds z] id := by
      rw [Filter.EventuallyEq]
      exact Filter.eventually_of_mem
        ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds hz) fun x hx => by
          simp [(InfinityInverse.tLocalHomeomorph H).right_inv hx]
    have hw_diff : DifferentiableAt ℂ (InfinityInverse.tLocalHomeomorph H).symm z := by
      exact ((tLocalHomeomorph_symm_contDiffOn H).differentiableOn
        (hn := by simp [WithTop.top_ne_zero])).differentiableAt
        ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds hz)
    have ht_hda_lh :
        HasDerivAt (InfinityInverse.tLocalHomeomorph H) (deriv (InfinityInverse.t H) w) w := by
      have ht_ana : AnalyticAt ℂ (InfinityInverse.t H) w :=
        InfinityInverse.t_analyticAt_of_mem H hw_US
      have ht_hda := ht_ana.differentiableAt.hasDerivAt
      rwa [← InfinityInverse.tLocalHomeomorph_coe H] at ht_hda
    have ht_hda_zero : HasDerivAt ↑(InfinityInverse.tLocalHomeomorph H) 0 w := by
      rw [← h_zero_deriv]; exact ht_hda_lh
    exact absurd hw_diff
      (not_differentiableAt_of_local_left_inverse_hasDerivAt_zero ht_hda_zero h_ev)
  have h_impl := deriv_t_mul_t w hw_US
  change deriv (InfinityInverse.t H) w * InfinityInverse.t H w =
    w * (eval (w ^ 2) H.f.reverse + w ^ 2 * eval (w ^ 2) (derivative H.f.reverse)) at h_impl
  rw [hR, mul_zero] at h_impl
  have h_t_eq : InfinityInverse.t H w = z := by
    have h_right := (InfinityInverse.tLocalHomeomorph H).right_inv hz
    exact h_right
  rw [h_t_eq] at h_impl
  rcases mul_eq_zero.mp h_impl with hh | hh
  · exact ht_deriv_ne hh
  · exact h_zero hh

theorem hyperellipticOddCoeff_analyticOn_infinityChart
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    AnalyticOn ℂ (hyperellipticOddCoeff (h := h) g (infty : HyperellipticOdd H h))
       (infinityChart H h).target := by
  let g_rev := g.reflect (H.genus - 1)
  let G : ℂ → ℂ := fun w =>
    -2 * eval (w ^ 2) g_rev /
      (eval (w ^ 2) H.f.reverse + w ^ 2 * eval (w ^ 2) (derivative H.f.reverse))
  have h_w2 : AnalyticOn ℂ (fun w : ℂ => w ^ 2) Set.univ := by
    have h_w2_poly : (fun w : ℂ => w ^ 2) = (fun w : ℂ => eval w (X ^ 2 : ℂ[X])) := by
      ext w; simp
    rw [h_w2_poly]
    exact (AnalyticOn.eval_polynomial (X ^ 2 : ℂ[X])).mono (Set.subset_univ _)
  have h_g_sq : AnalyticOn ℂ (fun w : ℂ => eval (w ^ 2) g_rev) Set.univ :=
    (AnalyticOn.eval_polynomial g_rev).comp h_w2 (Set.mapsTo_univ _ _)
  have h_num : AnalyticOn ℂ (fun w : ℂ => -2 * eval (w ^ 2) g_rev) Set.univ :=
    analyticOn_const.mul h_g_sq
  have h_f_sq : AnalyticOn ℂ (fun w : ℂ => eval (w ^ 2) H.f.reverse) Set.univ :=
    (AnalyticOn.eval_polynomial H.f.reverse).comp h_w2 (Set.mapsTo_univ _ _)
  have h_f'_sq : AnalyticOn ℂ (fun w : ℂ => eval (w ^ 2) (derivative H.f.reverse)) Set.univ :=
    (AnalyticOn.eval_polynomial (derivative H.f.reverse)).comp h_w2 (Set.mapsTo_univ _ _)
  have h_den : AnalyticOn ℂ (fun w : ℂ => eval (w ^ 2) H.f.reverse +
      w ^ 2 * eval (w ^ 2) (derivative H.f.reverse)) Set.univ :=
    h_f_sq.add (h_w2.mul h_f'_sq)
  -- Show G is AnalyticAt 0
  have hG_ana : AnalyticAt ℂ G 0 := by
    have h_den_zero : eval ((0 : ℂ) ^ 2) H.f.reverse +
        (0 : ℂ) ^ 2 * eval ((0 : ℂ) ^ 2) (derivative H.f.reverse) ≠ 0 := by
      have h0 : (0 : ℂ) ^ 2 = 0 := by norm_num
      rw [h0, zero_mul, add_zero]
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      rw [Polynomial.coeff_zero_reverse]
      exact InfinityInverse.leadingCoeff_ne_zero H
    exact (h_num.analyticAt Filter.univ_mem).div
      (h_den.analyticAt Filter.univ_mem) h_den_zero
  -- Show G is analytic everywhere (we only need near 0, but this implies it on the target)
  -- Actually we just need G(w(z)) is AnalyticOn the target.
  have hG_comp : AnalyticOn ℂ (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm)
      (infinityChart H h).target := by
    have hSymm : AnalyticOn ℂ (InfinityInverse.tLocalHomeomorph H).symm
        (infinityChart H h).target := by
      have hCD := tLocalHomeomorph_symm_contDiffOn H
      rw [show (ω : WithTop ℕ∞) = ⊤ from rfl] at hCD
      exact (contDiffOn_omega_iff_analyticOn (E := ℂ) (F := ℂ)
        (InfinityInverse.tLocalHomeomorph H).open_target.uniqueDiffOn).mp hCD
    have h_num_comp : AnalyticOn ℂ (fun z => -2 *
        eval (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2) g_rev)
        (infinityChart H h).target :=
      h_num.comp hSymm (Set.mapsTo_univ _ _)
    have h_den_comp : AnalyticOn ℂ (fun z =>
        eval (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2) H.f.reverse +
        ((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2 *
        eval (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2) (derivative H.f.reverse))
        (infinityChart H h).target :=
      h_den.comp hSymm (Set.mapsTo_univ _ _)
    have h_den_nz : ∀ z ∈ (infinityChart H h).target,
        eval (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2) H.f.reverse +
          ((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2 *
            eval (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2)
              (derivative H.f.reverse) ≠ 0 := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        have hw_zero : (InfinityInverse.tLocalHomeomorph H).symm 0 = 0 := by
          have h0 := InfinityInverse.tLocalHomeomorph_apply_zero H
          have h0_src := InfinityInverse.tLocalHomeomorph_source H
          have h_left := (InfinityInverse.tLocalHomeomorph H).left_inv h0_src
          rwa [h0] at h_left
        rw [hw_zero]
        have h0_sq : (0 : ℂ) ^ 2 = 0 := by norm_num
        rw [h0_sq, zero_mul, add_zero]
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        rw [Polynomial.coeff_zero_reverse]
        exact InfinityInverse.leadingCoeff_ne_zero H
      · exact infinity_transition_denominator_ne_zero h hz hz0
    exact h_num_comp.div h_den_comp h_den_nz
  -- Now show the composition equals the coefficient
  have h_eq : ∀ z ∈ (infinityChart H h).target,
      hyperellipticOddCoeff (H := H) (h := h) g (infty : HyperellipticOdd H h) z =
        (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm) z := by
    intro z hz
    unfold hyperellipticOddCoeff
    simp only [dif_pos hz]
    split_ifs with h_zero
    · -- case z = 0
      subst h_zero
      have hw_zero : (InfinityInverse.tLocalHomeomorph H).symm 0 = 0 := by
        have h0 := InfinityInverse.tLocalHomeomorph_apply_zero H
        have h0_src := InfinityInverse.tLocalHomeomorph_source H
        have h_left := (InfinityInverse.tLocalHomeomorph H).left_inv h0_src
        rwa [h0] at h_left
      -- Simplify LHS
      change -2 * g.coeff (H.genus - 1) / ↑H.f.leadingCoeff =
        (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm) 0
      -- Simplify RHS
      have h_rhs : (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm) 0 = G 0 := by
        simp only [Function.comp_apply, hw_zero]
      rw [h_rhs]
      unfold G
      have h0_sq : (0 : ℂ) ^ 2 = 0 := by norm_num
      rw [h0_sq]
      simp only [zero_mul, add_zero]
      have h_g_rev : eval 0 g_rev = g.coeff (H.genus - 1) := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect]
        unfold revAt
        rfl
      have h_f_rev : eval 0 H.f.reverse = H.f.leadingCoeff := by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        exact Polynomial.coeff_zero_reverse H.f
      rw [h_g_rev, h_f_rev]
    · -- case z ≠ 0
      change
        2 * eval (infinityInverseMap H h z).val.1 g *
            (infinityInverseMap H h z).val.1 ^ (H.genus + 2) /
          ((infinityInverseMap H h z).val.1 *
              eval (infinityInverseMap H h z).val.1 (derivative H.f) -
            (2 * (H.genus : ℂ) + 2) * eval (infinityInverseMap H h z).val.1 H.f) =
        (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm) z
      have hw_diff : DifferentiableAt ℂ
          (InfinityInverse.tLocalHomeomorph H).symm z := by
        exact ((tLocalHomeomorph_symm_contDiffOn H).differentiableOn
          (hn := by simp [WithTop.top_ne_zero])).differentiableAt
          ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
            hz)
      set w := (InfinityInverse.tLocalHomeomorph H).symm z
      have hw_ne : w ≠ 0 := by
        intro hc
        have h_lv :=
          (InfinityInverse.tLocalHomeomorph H).right_inv hz
        rw [show (InfinityInverse.tLocalHomeomorph H).symm z = w
          from rfl, hc] at h_lv
        rw [InfinityInverse.tLocalHomeomorph_coe H] at h_lv
        simp [InfinityInverse.t, InfinityInverse.S] at h_lv
        exact h_zero h_lv.symm
      have hw_source :
          w ∈ (InfinityInverse.tLocalHomeomorph H).source :=
        (InfinityInverse.tLocalHomeomorph H).map_target hz
      have hw_US : w ∈ InfinityInverse.U_S H := hw_source.2
      have ht_ana : AnalyticAt ℂ (InfinityInverse.t H) w :=
        InfinityInverse.t_analyticAt_of_mem H hw_US
      have ht_hda : HasDerivAt (InfinityInverse.t H)
          (deriv (InfinityInverse.t H) w) w :=
        ht_ana.differentiableAt.hasDerivAt
      have ht_hda_lh : HasDerivAt
          (InfinityInverse.tLocalHomeomorph H)
          (deriv (InfinityInverse.t H) w) w := by
        rwa [← InfinityInverse.tLocalHomeomorph_coe H]
      have ht_deriv_ne :
          deriv (InfinityInverse.t H) w ≠ 0 := by
        intro h_zero_deriv
        have h_ev : ↑(InfinityInverse.tLocalHomeomorph H) ∘
            ↑(InfinityInverse.tLocalHomeomorph H).symm
            =ᶠ[nhds z] id := by
          rw [Filter.EventuallyEq]
          exact Filter.eventually_of_mem
            ((InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
              hz) fun x hx => by
            simp [(InfinityInverse.tLocalHomeomorph H).right_inv hx]
        have ht_hda_zero : HasDerivAt
            ↑(InfinityInverse.tLocalHomeomorph H) 0 w := by
          rw [← h_zero_deriv]; exact ht_hda_lh
        exact absurd hw_diff
          (not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
            ht_hda_zero h_ev)
      have hx_eq : (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2 := by
        change (InfinityInverse.infinityInverseMap H h z).val.1 = w⁻¹ ^ 2
        rw [infinityInverseMap_val_of_ne_zero z hz h_zero]
      simp only [hx_eq]
      have h_rhs : (G ∘ ↑(InfinityInverse.tLocalHomeomorph H).symm) z = G w := rfl
      rw [h_rhs]
      unfold G
      set R := eval (w ^ 2) H.f.reverse + w ^ 2 * eval (w ^ 2) (derivative H.f.reverse) with hR_def
      have h_denom := x_fderiv_sub_f_eq h w hw_ne
      rw [h_denom]
      have h_genus_eq : (H.f.natDegree - 1) / 2 = H.genus := by
        obtain ⟨k, hk⟩ := h
        have h2 : H.genus = k := by
          dsimp [HyperellipticData.genus]
          omega
        omega
      have h_g_deg : g.natDegree ≤ H.genus - 1 := by
        have h1 : g.natDegree < H.genus := by
          rwa [h_genus_eq] at hDeg
        omega
      have h_g_rev : eval (w ^ 2) g_rev = w ^ (2 * (H.genus - 1)) * eval (w⁻¹ ^ 2) g := by
        have h_g_rev0 := eval_reflect_eq g (H.genus - 1) h_g_deg w⁻¹ (inv_ne_zero hw_ne)
        rw [inv_inv] at h_g_rev0
        exact h_g_rev0
      have h_pow_id : w ^ (2 * (H.genus - 1)) * w⁻¹ ^ (4 * H.genus + 2) =
          (w⁻¹ ^ 2) ^ (H.genus + 2) := by
        have h_sum : 2 * (H.genus - 1) + 2 * (H.genus + 2) = 4 * H.genus + 2 := by
          omega
        have h_M : 4 * H.genus + 2 = 2 * (H.genus - 1) + 2 * (H.genus + 2) := h_sum.symm
        rw [h_M, pow_add, ← mul_assoc]
        have h_cancel : w ^ (2 * (H.genus - 1)) * w⁻¹ ^ (2 * (H.genus - 1)) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hw_ne, one_pow]
        rw [h_cancel, one_mul, pow_mul]
      rw [h_g_rev]
      rw [← h_pow_id]
      have hR_ne : R ≠ 0 := by
        intro hR
        have h_impl := deriv_t_mul_t w hw_US
        change deriv (InfinityInverse.t H) w * InfinityInverse.t H w = w * R at h_impl
        rw [hR, mul_zero] at h_impl
        have h_t_eq : InfinityInverse.t H w = z := by
          have h_right := (InfinityInverse.tLocalHomeomorph H).right_inv hz
          exact h_right
        rw [h_t_eq] at h_impl
        rcases mul_eq_zero.mp h_impl with hh | hh
        · exact ht_deriv_ne hh
        · exact h_zero hh
      have h_w_pow_ne : w⁻¹ ^ (4 * H.genus + 2) ≠ 0 := pow_ne_zero _ (inv_ne_zero hw_ne)
      change 2 * eval (w⁻¹ ^ 2) g *
            (w ^ (2 * (H.genus - 1)) * w⁻¹ ^ (4 * H.genus + 2)) /
          (-w⁻¹ ^ (4 * H.genus + 2) * R) =
        -2 * (w ^ (2 * (H.genus - 1)) * eval (w⁻¹ ^ 2) g) / R
      field_simp [hR_ne, h_w_pow_ne]
  exact hG_comp.congr h_eq

theorem hyperellipticOddCoeff_isHolomorphicOneFormCoeff
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    IsHolomorphicOneFormCoeff (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro p
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    have hExt_target : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target := by
      change Set.univ ∩ (chartAt (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target
      rw [Set.univ_inter]
      rfl
    rw [hExt_target]
    exact hyperellipticOddCoeff_analyticOn_infinityChart g hDeg
  | coe_val a =>
    have hExt_target : (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).target =
        (affineLiftChart (h := h) a).target := by
      change Set.univ ∩ (chartAt (a : HyperellipticOdd H h)).target =
        (affineLiftChart (h := h) a).target
      rw [Set.univ_inter]
      rfl
    rw [hExt_target]
    exact hyperellipticOddCoeff_analyticOn_affineLift g a

theorem hyperellipticOddCoeff_cocycle_infty_coe (g : Polynomial ℂ) (a : HyperellipticAffine H)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target)
    (hsrc : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).source) :
    hyperellipticOddCoeff (h := h) g infty z =
      hyperellipticOddCoeff (h := h) g (coe a) ((extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h))
        ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)) ∘
          (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm) z 1) := by
  -- Step 1: Reduce extChartAt to concrete charts
  -- extChartAt infty = infinityChart (by Set.univ_inter)
  -- extChartAt (coe a) = affineLiftChart a (by Set.univ_inter)
  -- hyperellipticOddCoeff g (coe a) = hyperellipticAffineCoeff g a (by rfl)
  -- Step 2: Case split on a ∈ smoothLocusY
  by_cases hpY : a ∈ HyperellipticAffine.smoothLocusY H
  · -- Case: a ∈ smoothLocusY (projX chart, transition z ↦ w(z)⁻²)
    -- Step 1: Rewrite affine coefficient
    -- hyperellipticOddCoeff g (coe a) = hyperellipticAffineCoeff g a
    have hCoeffEq : hyperellipticOddCoeff (h := h) g (coe a) =
        HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
    rw [hCoeffEq]
    -- Step 2: Identify affineLiftChart with projX lift
    have hchart :
        (ChartedSpace.chartAt a :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjX (H := H) a hpY := by
      change HyperellipticAffine.affineChartAt (H := H) a =
        HyperellipticAffine.affineChartProjX (H := H) a hpY
      simp [HyperellipticAffine.affineChartAt, hpY]
    -- Step 3: Compute the transition value
    -- The transition infinityChart.symm ≫ affineLiftChart a
    -- equals infinityChart.symm ≫ (affineChartProjX a hpY).lift coe
    -- and its value at z is (tLocalHomeomorph.symm z)⁻¹ ^ 2
    -- But first, show z is in the transition source
    have hzt : z ∈ (infinityChart H h).target := by
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).target =
          (infinityChart H h).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (infty : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      rwa [← this]
    -- Show z ≠ 0 (z = 0 corresponds to ∞ which is not in the
    -- affine chart source, contradicting hsrc)
    have hzne : z ≠ 0 := by
      intro hc
      rw [hc] at hsrc
      -- infinityChart.symm 0 = ∞, which is not in any affine source
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).symm 0 =
          (infinityChart H h).symm 0 := rfl
      rw [this] at hsrc
      have hinf : (infinityChart H h).symm 0 =
        (infty : HyperellipticOdd H h) := by
        simp [infinityChart, infinityBackward, infty]
      rw [hinf] at hsrc
      -- ∞ ∈ (extChartAt (coe a)).source is impossible
      rw [extChartAt_source] at hsrc
      have : (infty : HyperellipticOdd H h) ∈
          (affineLiftChart (h := h) a).source := hsrc
      rw [affineLiftChart_source] at this
      obtain ⟨q, _, heq⟩ := this
      exact OnePoint.infty_notMem_range_coe ⟨q, heq⟩
    -- Step 4: Compute the transition value and the derivative
    -- Key: extChartAt (coe a) ∘ extChartAt infty.symm
    -- = affineLiftChart a ∘ infinityChart.symm
    -- = (affineChartProjX a hpY).lift coe ∘ infinityChart.symm (by hchart)
    -- By infinityChart_trans_affineLiftProjX_apply:
    --   transition(z) = w(z)⁻²
    -- where w = tLocalHomeomorph.symm z
    --
    -- Set w := tLocalHomeomorph.symm z
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    -- Show z ∈ tLocalHomeomorph.target
    have hzt_tLH : z ∈ (InfinityInverse.tLocalHomeomorph H).target := hzt
    -- Identify affineLiftChart a with projXLift
    have hLiftEq : affineLiftChart (h := h) a =
        (HyperellipticAffine.affineChartProjX (H := H)
          a hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H)) := by
      unfold affineLiftChart; congr 1
    -- Show the transition source membership
    have hTransSrc : z ∈ ((infinityChart H h).toPartialEquiv.symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) a hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe
            (X := HyperellipticAffine H))).toPartialEquiv).source := by
      refine ⟨hzt, ?_⟩
      change (infinityChart H h).symm z ∈
        ((HyperellipticAffine.affineChartProjX (H := H) a hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe
            (X := HyperellipticAffine H))).source
      have hSrcEq : (extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)).source =
          (affineLiftChart (h := h) a).source := by
        rw [extChartAt_source]; rfl
      rw [← hLiftEq, ← hSrcEq]
      exact hsrc
    -- Step 4: Compute the extChartAt transition value
    have hExtApp : (extChartAt 𝓘(ℂ, ℂ)
        (coe a : HyperellipticOdd H h))
        ((extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm z) =
          w⁻¹ ^ 2 := by
      -- extChartAt over 𝓘(ℂ,ℂ) is definitionally the chart map
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      -- conv rewrites gave ↑(affineLiftChart a) (↑(infinityChart.symm) z)
      -- = ↑(projXLift) (↑(infinityChart.symm) z)
      -- = ↑(infinityChart.symm ≫ₕ projXLift) z (by trans_apply)
      -- = w⁻¹ ^ 2 (by infinityChart_trans_affineLiftProjX_apply)
      have h1 : (affineLiftChart (h := h) a :
          OpenPartialHomeomorph (HyperellipticOdd H h) ℂ) =
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H))) := hLiftEq
      rw [h1]
      exact infinityChart_trans_affineLiftProjX_apply
        a hpY hTransSrc
    rw [hExtApp]
    -- Now the goal has concrete transition value w⁻¹ ^ 2:
    -- hyperellipticOddCoeff g infty z =
    --   hyperellipticAffineCoeff g a (w⁻¹ ^ 2) *
    --     fderiv(extChartAt(coe a) ∘ extChartAt(infty).symm)(z)(1)
    -- Step 5: Unfold the LHS at z ≠ 0
    have hLHS : hyperellipticOddCoeff (h := h) g infty z =
        let x := (infinityInverseMap H h z).val.1
        2 * g.eval x * x ^ (H.genus + 2) /
          (x * (Polynomial.derivative H.f).eval x -
            (2 * H.genus + 2) * H.f.eval x) := by
      unfold hyperellipticOddCoeff
      dsimp [infty]
      simp only [hzt, hzne, if_pos, if_neg, not_false_eq_true]
    rw [hLHS]
    -- Identify x = w⁻¹ ^ 2 using infinityInverseMap_val_of_ne_zero
    have hInvMap := infinityInverseMap_val_of_ne_zero
      z hzt_tLH hzne (H := H) (h := h)
    -- x = (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2
    have hx_eq : (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2 := by
      -- infinityInverseMap = InfinityInverse.infinityInverseMap (wrapper)
      change (InfinityInverse.infinityInverseMap H h z).val.1 =
        w⁻¹ ^ 2
      rw [hInvMap]
    simp only [hx_eq]
    -- Now the goal has w⁻¹ ^ 2 on both LHS and RHS:
    -- 2 * g.eval(w⁻¹ ^ 2) * (w⁻¹ ^ 2)^(g+2) /
    --   (w⁻¹^2 * f'(w⁻¹^2) - (2g+2) * f(w⁻¹^2)) =
    --   hyperellipticAffineCoeff g a (w⁻¹ ^ 2) *
    --     fderiv(transition)(z)(1)
    -- Step 6: Unfold affine coefficient to affineProjXCoeff
    have hAffCoeff :
        HyperellipticAffine.hyperellipticAffineCoeff g a
          (w⁻¹ ^ 2) =
        HyperellipticAffine.affineProjXCoeff g a hpY
          (w⁻¹ ^ 2) := by
      simp [HyperellipticAffine.hyperellipticAffineCoeff, hpY]
    rw [hAffCoeff]
    -- Step 7: Show w⁻¹ ^ 2 ∈ affineChartProjX target
    -- The transition maps z to w⁻¹ ^ 2 which is in projXLift.target
    -- = affineChartProjX.target
    have hInTarget : w⁻¹ ^ 2 ∈
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY) :
            OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target := by
      -- The transition maps z to w⁻¹ ^ 2, and transition maps
      -- source to target
      have hmem : z ∈ ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
        hTransSrc
      have hmap := ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).map_source hmem
      rw [infinityChart_trans_affineLiftProjX_apply a hpY
        hmem] at hmap
      rw [OpenPartialHomeomorph.trans_target] at hmap
      exact hmap.1
    -- Step 8: Unfold affineProjXCoeff to explicit formula
    rw [HyperellipticAffine.affineProjXCoeff_eq_on_target
      g a hpY hInTarget]
    -- Step 9: Compute the fderiv
    -- Use Filter.EventuallyEq.fderiv_eq to replace the chart
    -- composition with z → w(z)⁻¹ ^ 2
    have hOverlapOpen :
        IsOpen ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
      ((infinityChart H h).symm.trans _).open_source
    have hEqNear : (↑(extChartAt 𝓘(ℂ, ℂ)
        (coe a : HyperellipticOdd H h)) ∘
        ↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm) =ᶠ[nhds z]
      (fun z => ((InfinityInverse.tLocalHomeomorph H).symm
        z)⁻¹ ^ 2) := by
      refine Filter.eventually_of_mem
        (hOverlapOpen.mem_nhds hTransSrc) ?_
      intro u hu
      -- For u in the overlap, the chart composition equals
      -- the transition formula
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      rw [hLiftEq]
      exact infinityChart_trans_affineLiftProjX_apply
        a hpY hu
    rw [Filter.EventuallyEq.fderiv_eq hEqNear]
    -- Now the fderiv is of z → w(z)⁻¹ ^ 2
    -- Derive y-coordinate source membership from chart overlap
    have hYSrc : z * (w⁻¹ ^ 2) ^ (H.genus + 1) ∈
        (a.squareLocalHomeomorph hpY).source := by
      -- From hTransSrc: infinityChart.symm(z) ∈ projXLift.source
      -- For z ≠ 0: infinityChart.symm(z) = coe(infinityInverseMap(z))
      have h_eq_coe : (infinityChart H h).symm z =
          (coe : HyperellipticAffine H → HyperellipticOdd H h)
            (InfinityInverse.infinityInverseMap H h z) := by
        change infinityBackward H h z = _
        unfold infinityBackward
        rw [if_neg hzne]
      -- infinityInverseMap(z) ∈ affineChartProjX.source
      have h_in_src : InfinityInverse.infinityInverseMap H h z ∈
          (HyperellipticAffine.affineChartProjX (H := H) a hpY).source := by
        have h_proj_src : (infinityChart H h).symm z ∈
            ((a.affineChartProjX hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H))).source := by
          exact hTransSrc.2
        rw [h_eq_coe] at h_proj_src
        simp only [OpenPartialHomeomorph.lift_openEmbedding_source] at h_proj_src
        obtain ⟨q, hq, heq⟩ := h_proj_src
        have : q = InfinityInverse.infinityInverseMap H h z :=
          OnePoint.coe_injective heq
        rwa [← this]
      -- affineChartProjX.source says q.val.2 ∈ sqLH.source
      -- and infinityInverseMap(z).val.2 = z * (w⁻¹^2)^(g+1)
      have h_val := infinityInverseMap_val_of_ne_zero z
        hzt_tLH hzne (H := H) (h := h)
      have h_snd : (InfinityInverse.infinityInverseMap
          H h z).val.2 =
          z * (w⁻¹ ^ 2) ^ (H.genus + 1) := by rw [h_val]
      rw [← h_snd]
      exact h_in_src
    -- Apply infinity_transition_deriv_identity to get the
    -- explicit derivative value
    rw [infinity_transition_deriv_identity h a hpY
      hzt_tLH hzne hInTarget hYSrc]
    -- Goal is now:
    -- 2 * g(w⁻²) * (w⁻²)^(g+2) / denom =
    --   g(w⁻²) / y * (2 * (w⁻²)^(g+2) * y / denom)
    -- where y = squareLocalHomeomorph.symm(f(w⁻²))
    -- This is a pure algebraic identity: cancel g(w⁻²)
    -- and y from both sides
    set x := w⁻¹ ^ 2
    set y := ((HyperellipticAffine.squareLocalHomeomorph
        (H := H) a hpY).symm
      (H.f.eval x))
    set D := x * (Polynomial.derivative H.f).eval x -
      (2 * ↑H.genus + 2) * H.f.eval x
    -- Goal: 2 * g(x) * x^(g+2) / D =
    --       g(x) / y * (2 * x^(g+2) * y / D)
    have hyNZ : y ≠ 0 :=
      HyperellipticAffine.squareLocalHomeomorph_symm_ne_zero
        a hpY hInTarget
    ring_nf
    rw [show eval x g * x ^ 2 * x ^ H.genus *
        D⁻¹ * y * y⁻¹ * 2 =
      eval x g * x ^ 2 * x ^ H.genus *
        D⁻¹ * (y * y⁻¹) * 2 from by ring]
    rw [mul_inv_cancel₀ hyNZ, mul_one]
  · -- Case: a ∉ smoothLocusY (projY chart)
    have hpX : a ∈ HyperellipticAffine.smoothLocusX H :=
      HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H
        (by simpa [HyperellipticAffine.smoothLocusY]
          using hpY)
    -- Step 1: Chart identification
    have hchart : ChartedSpace.chartAt a =
        HyperellipticAffine.affineChartProjY (H := H)
          a hpX :=
      HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY
        (H := H) a hpY
    -- Step 2: z ∈ infinityChart.target
    have hzt : z ∈ (infinityChart H h).target := by
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).target =
          (infinityChart H h).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (infty : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      rwa [← this]
    -- Step 3: z ≠ 0
    have hzne : z ≠ 0 := by
      intro hc; rw [hc] at hsrc
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).symm 0 =
          (infinityChart H h).symm 0 := rfl
      rw [this] at hsrc
      have hinf : (infinityChart H h).symm 0 =
        (infty : HyperellipticOdd H h) := by
        simp [infinityChart, infinityBackward, infty]
      rw [hinf] at hsrc
      rw [extChartAt_source] at hsrc
      have : (infty : HyperellipticOdd H h) ∈
          (affineLiftChart (h := h) a).source := hsrc
      rw [affineLiftChart_source] at this
      obtain ⟨q, _, heq⟩ := this
      exact OnePoint.infty_notMem_range_coe ⟨q, heq⟩
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    have hzt_tLH :
        z ∈ (InfinityInverse.tLocalHomeomorph H).target :=
      hzt
    -- Step 4: affineLiftChart = projYLift
    have hLiftEq : affineLiftChart (h := h) a =
        (HyperellipticAffine.affineChartProjY (H := H)
          a hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H)) := by
      unfold affineLiftChart; rw [hchart]; rfl
    -- Step 5: Transition source membership
    have hTransSrc :
        z ∈ ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H)
            a hpX).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source := by
      constructor
      · exact hzt
      · have : (extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).symm z ∈
            (affineLiftChart (h := h) a).source := by
          have := hsrc
          rwa [extChartAt_source] at this
        rw [hLiftEq] at this
        rw [Set.mem_preimage]
        convert this
    -- Step 6: Compute transition value
    -- For projY: transition is z ↦ z * (w⁻¹ ^ 2)^(g+1)
    have hExtApp :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h))
          ((extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).symm z) =
          z * (w⁻¹ ^ 2) ^ (H.genus + 1) := by
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      rw [hLiftEq]
      exact infinityChart_trans_affineLiftProjY_apply
        a hpX hTransSrc
    rw [hExtApp]
    -- The remaining algebraic identity for the projY case
    have hInvMap := infinityInverseMap_val_of_ne_zero z hzt_tLH hzne (H := H) (h := h)
    have hx_eq : (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2 := by
      change (InfinityInverse.infinityInverseMap H h z).val.1 = w⁻¹ ^ 2
      rw [hInvMap]
    have hLHS : hyperellipticOddCoeff (h := h) g infty z =
        let x := (infinityInverseMap H h z).val.1
        2 * g.eval x * x ^ (H.genus + 2) /
          (x * (Polynomial.derivative H.f).eval x -
            (2 * H.genus + 2) * H.f.eval x) := by
      unfold hyperellipticOddCoeff
      dsimp [infty]
      simp only [hzt, hzne, if_pos, if_neg, not_false_eq_true]
    rw [hLHS, hx_eq]
    have hCoeffEq : hyperellipticOddCoeff (h := h) g (coe a) =
        HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
    rw [hCoeffEq]
    have hAffCoeff :
        HyperellipticAffine.hyperellipticAffineCoeff g a
          (z * (w⁻¹ ^ 2) ^ (H.genus + 1)) =
        HyperellipticAffine.affineProjYCoeff g a hpX
          (z * (w⁻¹ ^ 2) ^ (H.genus + 1)) := by
      simp [HyperellipticAffine.hyperellipticAffineCoeff, hpY]
    rw [hAffCoeff]
    have hInTarget : z * (w⁻¹ ^ 2) ^ (H.genus + 1) ∈
        ((HyperellipticAffine.affineChartProjY (H := H)
          a hpX) :
            OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target := by
      have hmem : z ∈ ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H)
            a hpX).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
        hTransSrc
      have hmap := ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H)
            a hpX).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).map_source hmem
      rw [infinityChart_trans_affineLiftProjY_apply a hpX
          hmem] at hmap
      rw [OpenPartialHomeomorph.trans_target] at hmap
      exact hmap.1
    rw [HyperellipticAffine.affineProjYCoeff_eq_on_target
      g a hpX hInTarget]
    have hy_sq := InfinityInverse.y_sq_eq_eval_x h z hzt_tLH hzne
    have h_in_src : w⁻¹ ^ 2 ∈ (HyperellipticAffine.polynomialLocalHomeomorph a hpX).source := by
      have h_proj_src : (infinityChart H h).symm z ∈
          ((HyperellipticAffine.affineChartProjY (H := H) a hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H))).source := by
        exact hTransSrc.2
      have h_eq_coe : (infinityChart H h).symm z =
          (coe : HyperellipticAffine H → HyperellipticOdd H h)
            (InfinityInverse.infinityInverseMap H h z) := by
        change infinityBackward H h z = _
        unfold infinityBackward
        rw [if_neg hzne]
      rw [h_eq_coe] at h_proj_src
      simp only [OpenPartialHomeomorph.lift_openEmbedding_source] at h_proj_src
      obtain ⟨q, hq, heq⟩ := h_proj_src
      have hq_eq : q = InfinityInverse.infinityInverseMap H h z :=
        OnePoint.coe_injective heq
      rw [hq_eq] at hq
      change (infinityInverseMap H h z).val.1 ∈
        (HyperellipticAffine.polynomialLocalHomeomorph a hpX).source at hq
      rwa [hx_eq] at hq
    have h_left_inv := (HyperellipticAffine.polynomialLocalHomeomorph a hpX).left_inv h_in_src
    have h_poly_app : (HyperellipticAffine.polynomialLocalHomeomorph a hpX) (w⁻¹ ^ 2) =
        H.f.eval (w⁻¹ ^ 2) := by
      simp [HyperellipticAffine.polynomialLocalHomeomorph]
    rw [h_poly_app] at h_left_inv
    rw [hy_sq, h_left_inv]
    have hOverlapOpen :
        IsOpen ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H)
            a hpX).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
      ((infinityChart H h).symm.trans _).open_source
    have hEqNear : (↑(extChartAt 𝓘(ℂ, ℂ)
        (coe a : HyperellipticOdd H h)) ∘
        ↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm) =ᶠ[nhds z]
      (fun z => z * (((InfinityInverse.tLocalHomeomorph H).symm
        z)⁻¹ ^ 2) ^ (H.genus + 1)) := by
      refine Filter.eventually_of_mem
        (hOverlapOpen.mem_nhds hTransSrc) ?_
      intro u hu
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      rw [hLiftEq]
      exact infinityChart_trans_affineLiftProjY_apply
        a hpX hu
    rw [Filter.EventuallyEq.fderiv_eq hEqNear]
    have hx_deriv : HasDerivAt (fun z => ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2)
        (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) /
          (w⁻¹ ^ 2 * (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
            (2 * H.genus + 2) * H.f.eval (w⁻¹ ^ 2))) z := by
      exact infinity_transition_deriv_identity_raw h hzt_tLH hzne
    have h_pow_deriv :
        HasDerivAt
          (fun z' => (((InfinityInverse.tLocalHomeomorph H).symm z')⁻¹ ^ 2) ^ (H.genus + 1))
          ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
            (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) /
              (w⁻¹ ^ 2 * (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
                (2 * H.genus + 2) * H.f.eval (w⁻¹ ^ 2)))) z := by
      have h_u_pow : HasDerivAt (fun u : ℂ => u ^ (H.genus + 1))
          ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus) (w⁻¹ ^ 2) := by
        have h_eq_deriv : ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus) =
            ↑(H.genus + 1) * (w⁻¹ ^ 2) ^ (H.genus + 1 - 1) := by
          have h_eq : H.genus + 1 - 1 = H.genus := by omega
          rw [h_eq]
          push_cast
          rfl
        rw [h_eq_deriv]
        exact hasDerivAt_pow (H.genus + 1) (w⁻¹ ^ 2)
      exact h_u_pow.comp z hx_deriv
    have h_prod_deriv :
        HasDerivAt
          (fun z => z * (((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2) ^ (H.genus + 1))
          (1 * (w⁻¹ ^ 2) ^ (H.genus + 1) + z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
            (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) /
              (w⁻¹ ^ 2 * (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
                (2 * H.genus + 2) * H.f.eval (w⁻¹ ^ 2))))) z := by
      have h_id_deriv : HasDerivAt (fun z : ℂ => z) 1 z := hasDerivAt_id' z
      exact h_id_deriv.mul h_pow_deriv
    rw [fderiv_apply_one_eq_deriv, h_prod_deriv.deriv]
    set D := w⁻¹ ^ 2 * (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
      (2 * (H.genus : ℂ) + 2) * H.f.eval (w⁻¹ ^ 2) with hD_def
    have hD_ne : D ≠ 0 := by
      have hw_ne : w ≠ 0 := by
        intro hw0
        have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H hzt_tLH
        have h_w_eq : (InfinityInverse.tLocalHomeomorph H).symm z = w := rfl
        rw [h_w_eq, hw0] at h_tz
        have h_zero : InfinityInverse.t H 0 = 0 := by
          unfold InfinityInverse.t
          simp
        rw [h_zero] at h_tz
        exact hzne h_tz.symm
      have hR_ne : eval (w ^ 2) H.f.reverse + w ^ 2 * eval (w ^ 2) (derivative H.f.reverse) ≠ 0 :=
        infinity_transition_denominator_ne_zero h hzt_tLH hzne
      have h_w_pow_ne : w⁻¹ ^ (4 * H.genus + 2) ≠ 0 := pow_ne_zero _ (inv_ne_zero hw_ne)
      have h_w_pow_ne_neg : -w⁻¹ ^ (4 * H.genus + 2) ≠ 0 := by
        intro hc
        rw [neg_eq_zero] at hc
        exact h_w_pow_ne hc
      have h_denom := x_fderiv_sub_f_eq h w hw_ne
      rw [hD_def, h_denom]
      exact mul_ne_zero h_w_pow_ne_neg hR_ne
    have h_f_der_ne : (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) ≠ 0 :=
      HyperellipticAffine.polynomialLocalHomeomorph_no_critical_in_source
        a hpX h_in_src
    have h_z_x_pow : z ^ 2 * (w⁻¹ ^ 2) ^ (2 * H.genus + 2) = H.f.eval (w⁻¹ ^ 2) := by
      calc z ^ 2 * (w⁻¹ ^ 2) ^ (2 * H.genus + 2)
        _ = (z * (w⁻¹ ^ 2) ^ (H.genus + 1)) ^ 2 := by
          rw [mul_pow, ← pow_mul]
          ring
        _ = H.f.eval (w⁻¹ ^ 2) := hy_sq
    have h_alg : (w⁻¹ ^ 2) ^ (H.genus + 2) / D =
        1 / (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) *
          ((w⁻¹ ^ 2) ^ (H.genus + 1) +
            z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
              (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) / D))) := by
      have h_num : (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) * (w⁻¹ ^ 2) ^ (H.genus + 2) =
          D * (w⁻¹ ^ 2) ^ (H.genus + 1) +
            z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
              (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3))) := by
        rw [hD_def]
        have h_z2 : z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
            (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3))) =
            (2 * H.genus + 2) * (z ^ 2 * (w⁻¹ ^ 2) ^ (2 * H.genus + 2)) *
              (w⁻¹ ^ 2) ^ (H.genus + 1) := by
          calc z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus * (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3)))
            _ = (2 * H.genus + 2) *
                  (z ^ 2 * ((w⁻¹ ^ 2) ^ H.genus * (w⁻¹ ^ 2) ^ (2 * H.genus + 3))) := by ring
            _ = (2 * H.genus + 2) * (z ^ 2 * (w⁻¹ ^ 2) ^ (3 * H.genus + 3)) := by
              rw [← pow_add]
              congr 3
              omega
            _ = (2 * H.genus + 2) * (z ^ 2 * (w⁻¹ ^ 2) ^ (2 * H.genus + 2)) *
                  (w⁻¹ ^ 2) ^ (H.genus + 1) := by
              have h_eq_pow : (w⁻¹ ^ 2) ^ (3 * H.genus + 3) =
                  (w⁻¹ ^ 2) ^ (2 * H.genus + 2) * (w⁻¹ ^ 2) ^ (H.genus + 1) := by
                rw [show 3 * H.genus + 3 = (2 * H.genus + 2) + (H.genus + 1) by omega]
                rw [pow_add]
              rw [h_eq_pow]
              ring
        rw [h_z2, h_z_x_pow]
        ring
      have hx_div : w⁻¹ ^ 2 = 1 / w ^ 2 := by ring
      rw [hx_div] at hD_def h_f_der_ne h_num h_z_x_pow ⊢
      field_simp [hD_ne, h_f_der_ne]
      linear_combination h_num
    have h_final : 2 * g.eval (w⁻¹ ^ 2) * (w⁻¹ ^ 2) ^ (H.genus + 2) / D =
        2 * g.eval (w⁻¹ ^ 2) / (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) *
          (1 * (w⁻¹ ^ 2) ^ (H.genus + 1) + z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
            (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) / D))) := by
      calc 2 * g.eval (w⁻¹ ^ 2) * (w⁻¹ ^ 2) ^ (H.genus + 2) / D
        _ = 2 * g.eval (w⁻¹ ^ 2) * ((w⁻¹ ^ 2) ^ (H.genus + 2) / D) := by ring
        _ = 2 * g.eval (w⁻¹ ^ 2) * (1 / (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) *
              ((w⁻¹ ^ 2) ^ (H.genus + 1) + z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
                (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) / D)))) := by rw [h_alg]
        _ = 2 * g.eval (w⁻¹ ^ 2) / (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) *
              (1 * (w⁻¹ ^ 2) ^ (H.genus + 1) + z * ((H.genus + 1) * (w⁻¹ ^ 2) ^ H.genus *
                (2 * z * (w⁻¹ ^ 2) ^ (2 * H.genus + 3) / D))) := by ring
    dsimp only
    exact h_final

theorem hyperellipticOddCoeff_satisfiesCotangentCocycle
    (g : Polynomial ℂ) (_hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    SatisfiesCotangentCocycle (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro x y z hz hSrc
  induction x using HyperellipticOdd.rec with
  | infty_val =>
    induction y using HyperellipticOdd.rec with
    | infty_val =>
      -- (infty, infty): same chart, transition is identity
      have hRightInv : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h))
          ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z) = z :=
        (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).right_inv hz
      rw [hRightInv]
      have hEv : ∀ᶠ w in nhds z,
          ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)) ∘
            (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm) w = id w :=
        Filter.eventually_of_mem (extChartAt_target_mem_nhds' hz) fun w hw => by
          simp only [Function.comp_apply, id]
          exact (extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).right_inv hw
      rw [Filter.EventuallyEq.fderiv_eq hEv, fderiv_id,
          ContinuousLinearMap.id_apply, mul_one]
    | coe_val a =>
      exact hyperellipticOddCoeff_cocycle_infty_coe g a hz hSrc
  | coe_val p =>
    induction y using HyperellipticOdd.rec with
    | infty_val =>
      -- (coe p, infty): derived from (infty, coe p)
      -- via transition_fderiv_mul
      let φp := extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H h)
      let φi := extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)
      let w := φi (φp.symm z)
      have hwt : w ∈ φi.target := φi.map_source hSrc
      have hws : φi.symm w ∈ φp.source := by
        change φi.symm (φi (φp.symm z)) ∈ φp.source
        rw [φi.left_inv hSrc]
        exact φp.map_target hz
      -- apply (infty, coe p) at (φi, φp, w)
      have hfwd := hyperellipticOddCoeff_cocycle_infty_coe
        g p hwt hws
      -- simplify φp (φi.symm w) = z in hfwd
      have hw_simp : φp (φi.symm w) = z := by
        change φp (φi.symm (φi (φp.symm z))) = z
        rw [φi.left_inv hSrc, φp.right_inv hz]
      rw [hw_simp] at hfwd
      -- hfwd: coeff infty w = coeff (coe p) z * D_bwd
      -- htfm: D_fwd * D_bwd = 1
      have htfm :=
        Jacobians.GeneralResults.transition_fderiv_mul
          (coe p : HyperellipticOdd H h)
          (infty : HyperellipticOdd H h) hz hSrc
      -- The goal is: coeff (coe p) z = coeff infty w * D_fwd
      -- We have: coeff infty w = coeff (coe p) z * D_bwd
      -- And: D_fwd * D_bwd = 1
      rw [hfwd, mul_assoc, mul_comm
        (fderiv ℂ (φp ∘ φi.symm) w 1)
        (fderiv ℂ (φi ∘ φp.symm) z 1),
        htfm, mul_one]
    | coe_val q =>
      -- (coe p, coe q): reduce to cocycle_coe_coe
      have hTarget :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe p : HyperellipticOdd H h)).target =
            (affineLiftChart (h := h) p).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (coe p : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      have hSource :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe q : HyperellipticOdd H h)).source =
            (affineLiftChart (h := h) q).source := by
        rw [extChartAt_source 𝓘(ℂ, ℂ)]
        change (affineLiftChart (h := h) q).source =
          (affineLiftChart (h := h) q).source
        rfl
      have hz' : z ∈ (affineLiftChart (h := h) p).target :=
        hTarget ▸ hz
      have hSrc' : (affineLiftChart (h := h) p).symm z ∈
          (affineLiftChart (h := h) q).source := by
        rw [← hSource]
        exact hSrc
      exact hyperellipticOddCoeff_cocycle_coe_coe g p q hz' hSrc'

noncomputable def hyperellipticOddForm (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticOdd H Fact.out) :=
  if h : g.natDegree < (H.f.natDegree - 1) / 2 then
    ⟨hyperellipticOddCoeff (H := H) (h := Fact.out) g,
      hyperellipticOddCoeff_isHolomorphicOneFormCoeff g h,
      hyperellipticOddCoeff_satisfiesCotangentCocycle g h,
      hyperellipticOddCoeff_isZeroOffChartTarget g⟩
  else 0

open Jacobians.ProjectiveCurve.HyperellipticAffine

theorem hyperellipticOddForm_of_lt (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] {g : Polynomial ℂ}
    (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    hyperellipticOddForm H g =
      ⟨hyperellipticOddCoeff (H := H) (h := Fact.out) g,
        hyperellipticOddCoeff_isHolomorphicOneFormCoeff g hDeg,
        hyperellipticOddCoeff_satisfiesCotangentCocycle g hDeg,
       hyperellipticOddCoeff_isZeroOffChartTarget g⟩ := by
  unfold hyperellipticOddForm
  rw [dif_pos hDeg]

theorem hyperellipticOddForm_coeff_of_lt (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] {g : Polynomial ℂ}
    (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    (hyperellipticOddForm H g).coeff = hyperellipticOddCoeff (H := H) (h := Fact.out) g := by
  rw [hyperellipticOddForm_of_lt H hDeg]
  rfl

@[simp] theorem hyperellipticOddForm_zero (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] :
    hyperellipticOddForm H (0 : Polynomial ℂ) = 0 := by
  unfold hyperellipticOddForm
  split
  · apply Subtype.ext
    change hyperellipticOddCoeff (H := H) (h := Fact.out) 0 = 0
    exact hyperellipticOddCoeff_zero
  · rfl

theorem natDegree_lt_of_mem_degreeLT {n : ℕ} (hn : 0 < n) {g : Polynomial ℂ}
    (hg : g ∈ Polynomial.degreeLT ℂ n) : g.natDegree < n := by
  by_cases h0 : g = 0
  · simpa [h0] using hn
  · rw [Polynomial.mem_degreeLT] at hg
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hg

private theorem eq_zero_of_mem_degreeLT_zero {p : Polynomial ℂ}
    (hp : p ∈ Polynomial.degreeLT ℂ 0) : p = 0 := by
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
    Polynomial.degree_eq_bot] at hp
  exact hp

theorem hyperellipticOddForm_add_of_lt (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] {g g' : Polynomial ℂ}
    (h : g.natDegree < (H.f.natDegree - 1) / 2)
    (h' : g'.natDegree < (H.f.natDegree - 1) / 2)
    (h'' : (g + g').natDegree < (H.f.natDegree - 1) / 2) :
    hyperellipticOddForm H (g + g') =
      hyperellipticOddForm H g + hyperellipticOddForm H g' := by
  rw [hyperellipticOddForm_of_lt H h,
    hyperellipticOddForm_of_lt H h',
    hyperellipticOddForm_of_lt H h'']
  apply Subtype.ext
  change hyperellipticOddCoeff (H := H) (h := Fact.out) (g + g') = _
  exact hyperellipticOddCoeff_add g g'

theorem hyperellipticOddForm_smul_of_lt (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] (c : ℂ) {g : Polynomial ℂ}
    (h : g.natDegree < (H.f.natDegree - 1) / 2)
    (h' : (c • g).natDegree < (H.f.natDegree - 1) / 2) :
    hyperellipticOddForm H (c • g) = c • hyperellipticOddForm H g := by
  rw [hyperellipticOddForm_of_lt H h, hyperellipticOddForm_of_lt H h']
  apply Subtype.ext
  change hyperellipticOddCoeff (H := H) (h := Fact.out) (c • g) = _
  exact hyperellipticOddCoeff_smul c g

/-- The packaged ℂ-linear map version of `hyperellipticOddForm`, on the
low-degree subspace `Polynomial.degreeLT ℂ ((H.f.natDegree - 1) / 2)`. -/
noncomputable def hyperellipticOddFormLinearMap (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] :
    Polynomial.degreeLT ℂ ((H.f.natDegree - 1) / 2) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticOdd H Fact.out) where
  toFun gd := hyperellipticOddForm H gd.1
  map_add' gd gd' := by
    rcases Nat.eq_zero_or_pos ((H.f.natDegree - 1) / 2) with hn | hn
    · have e : ∀ p : Polynomial.degreeLT ℂ ((H.f.natDegree - 1) / 2), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [e, add_zero, hyperellipticOddForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 := natDegree_lt_of_mem_degreeLT hn gd'.2
      have h3 : (gd.1 + gd'.1).natDegree < (H.f.natDegree - 1) / 2 :=
        lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt h1 h2)
      exact hyperellipticOddForm_add_of_lt H h1 h2 h3
  map_smul' c gd := by
    rcases Nat.eq_zero_or_pos ((H.f.natDegree - 1) / 2) with hn | hn
    · have e : ∀ p : Polynomial.degreeLT ℂ ((H.f.natDegree - 1) / 2), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [RingHom.id_apply, e, smul_zero, hyperellipticOddForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 : (c • gd.1).natDegree < (H.f.natDegree - 1) / 2 :=
        lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) h1
      change hyperellipticOddForm H (c • gd.1) = c • hyperellipticOddForm H gd.1
      exact hyperellipticOddForm_smul_of_lt H c h1 h2

theorem hyperellipticOddForm_eq_of_agree_at_affine_smoothY
    [Fact (Odd H.f.natDegree)]
    {g g' : Polynomial ℂ}
    (hg : g.natDegree < (H.f.natDegree - 1) / 2) (hg' : g'.natDegree < (H.f.natDegree - 1) / 2)
    {a : HyperellipticAffine H}
    (hpY : a ∈ smoothLocusY H)
    (hCoeff : (hyperellipticOddForm H g).coeff (coe a) =
              (hyperellipticOddForm H g').coeff (coe a)) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ), g₀.natDegree < (H.f.natDegree - 1) / 2 →
      (hyperellipticOddForm H g₀).coeff (coe a) = hyperellipticAffineCoeff g₀ a := by
    intro g₀ hg₀
    rw [hyperellipticOddForm_coeff_of_lt H hg₀]
    ext z
    rfl
  rw [hReduce g hg, hReduce g' hg'] at hCoeff
  exact hyperellipticAffineCoeff_injective_at_smoothLocusY a hpY hCoeff

theorem hyperellipticOddForm_eq_of_agree_at_affine_smoothX
    [Fact (Odd H.f.natDegree)]
    {g g' : Polynomial ℂ}
    (hg : g.natDegree < (H.f.natDegree - 1) / 2) (hg' : g'.natDegree < (H.f.natDegree - 1) / 2)
    {a : HyperellipticAffine H}
    (hpX : a ∈ smoothLocusX H) (hpYn : a ∉ smoothLocusY H)
    (hCoeff : (hyperellipticOddForm H g).coeff (coe a) =
              (hyperellipticOddForm H g').coeff (coe a)) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ), g₀.natDegree < (H.f.natDegree - 1) / 2 →
      (hyperellipticOddForm H g₀).coeff (coe a) = hyperellipticAffineCoeff g₀ a := by
    intro g₀ hg₀
    rw [hyperellipticOddForm_coeff_of_lt H hg₀]
    ext z
    rfl
  rw [hReduce g hg, hReduce g' hg'] at hCoeff
  exact hyperellipticAffineCoeff_injective_at_smoothLocusX a hpX hpYn hCoeff

noncomputable def witnessZeroX (H : HyperellipticData) : HyperellipticAffine H :=
  ⟨(0, (exists_complex_sq_eq (H.f.eval 0)).choose), by
    simpa using (exists_complex_sq_eq (H.f.eval 0)).choose_spec⟩

@[simp] lemma witnessZeroX_val_fst (H : HyperellipticData) :
    (witnessZeroX H).val.1 = 0 := rfl

lemma witnessZeroX_val_snd_sq (H : HyperellipticData) :
    (witnessZeroX H).val.2 ^ 2 = H.f.eval 0 := by
  simpa using (witnessZeroX H).property

lemma witnessZeroX_mem_smoothLocusY_iff (H : HyperellipticData) :
    witnessZeroX H ∈ smoothLocusY H ↔ H.f.eval 0 ≠ 0 := by
  unfold smoothLocusY
  constructor
  · intro hY h0
    apply hY
    have hSq : (witnessZeroX H).val.2 ^ 2 = 0 := by
      rw [witnessZeroX_val_snd_sq]; exact h0
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hSq
  · intro h0 hY
    have hSq : (witnessZeroX H).val.2 ^ 2 = H.f.eval 0 := witnessZeroX_val_snd_sq H
    rw [hY, zero_pow (by norm_num : 2 ≠ 0)] at hSq
    exact h0 hSq.symm

lemma witnessZeroX_mem_smoothLocusX_of_zero_root (H : HyperellipticData)
    (h0 : H.f.eval 0 = 0) :
    witnessZeroX H ∈ smoothLocusX H := by
  unfold smoothLocusX
  change (Polynomial.derivative H.f).eval (witnessZeroX H).val.1 ≠ 0
  rw [witnessZeroX_val_fst]
  exact eval_derivative_ne_zero_of_eval_eq_zero H h0

theorem hyperellipticOddForm_injOn_lowDegree
    (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    Set.InjOn (hyperellipticOddForm H)
      { g : Polynomial ℂ | g.natDegree < (H.f.natDegree - 1) / 2 } := by
  intro g hg g' hg' hForm
  simp only [Set.mem_setOf_eq] at hg hg'
  have hCoeff : (hyperellipticOddForm H g).coeff (coe (witnessZeroX H)) =
      (hyperellipticOddForm H g').coeff (coe (witnessZeroX H)) := by
    rw [hForm]
  by_cases h0 : H.f.eval 0 = 0
  · have hpX := witnessZeroX_mem_smoothLocusX_of_zero_root H h0
    have hpYn : witnessZeroX H ∉ smoothLocusY H := by
      rw [witnessZeroX_mem_smoothLocusY_iff]
      exact fun h => h h0
    exact hyperellipticOddForm_eq_of_agree_at_affine_smoothX hg hg' hpX hpYn hCoeff
  · have hpY : witnessZeroX H ∈ smoothLocusY H := by
      rw [witnessZeroX_mem_smoothLocusY_iff]
      exact h0
    exact hyperellipticOddForm_eq_of_agree_at_affine_smoothY hg hg' hpY hCoeff

theorem hyperellipticOddFormLinearMap_injective (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] :
    Function.Injective (hyperellipticOddFormLinearMap H) := by
  intro gd gd' h
  apply Subtype.ext
  rcases Nat.eq_zero_or_pos ((H.f.natDegree - 1) / 2) with hn | hn
  · have e : ∀ p : Polynomial.degreeLT ℂ ((H.f.natDegree - 1) / 2), p.1 = 0 := by
      intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
    rw [e gd, e gd']
  · exact hyperellipticOddForm_injOn_lowDegree H
      (Set.mem_setOf.mpr (natDegree_lt_of_mem_degreeLT hn gd.2))
      (Set.mem_setOf.mpr (natDegree_lt_of_mem_degreeLT hn gd'.2)) h

theorem hyperellipticOddForm_linearIndependent (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] :
    LinearIndependent ℂ
      (fun k : Fin ((H.f.natDegree - 1) / 2) =>
        hyperellipticOddForm H (Polynomial.X ^ k.val)) := by
  set n := (H.f.natDegree - 1) / 2 with hn
  have hmem : ∀ k : Fin n, (Polynomial.X ^ k.val : Polynomial ℂ) ∈ Polynomial.degreeLT ℂ n := by
    intro k; rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]; exact_mod_cast k.isLt
  set v : Fin n → Polynomial.degreeLT ℂ n := fun k => ⟨Polynomial.X ^ k.val, hmem k⟩ with hv
  have hCoe : ⇑(Polynomial.basisMonomials ℂ) = fun m => (Polynomial.X : Polynomial ℂ) ^ m := by
    funext m; rw [Polynomial.coe_basisMonomials, ← Polynomial.monomial_one_right_eq_X_pow m]
  have hPowLI : LinearIndependent ℂ (fun m : ℕ => (Polynomial.X : Polynomial ℂ) ^ m) := by
    have := (Polynomial.basisMonomials ℂ).linearIndependent; rw [hCoe] at this; exact this
  have hFinLI : LinearIndependent ℂ (fun k : Fin n => (Polynomial.X : Polynomial ℂ) ^ k.val) :=
    hPowLI.comp (fun k : Fin n => k.val) Fin.val_injective
  have hvLI : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (Polynomial.degreeLT ℂ n).subtype hFinLI
  have hKer : LinearMap.ker (hyperellipticOddFormLinearMap H) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hyperellipticOddFormLinearMap_injective H)
  have hmap := hvLI.map' (hyperellipticOddFormLinearMap H) hKer
  exact hmap

end Jacobians.ProjectiveCurve.HyperellipticOdd
