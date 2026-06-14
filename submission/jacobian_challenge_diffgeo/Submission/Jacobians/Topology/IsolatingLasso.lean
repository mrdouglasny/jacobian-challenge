/-
# B1 sharp form — one lasso per puncture normally generates π₁(ℂ ∖ T)

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rung **G6** (the
normal-closure sharpening of the B1 headline, the form the route doc's
G4 decision pinned).

**Main results.**
* `isolatingLasso_conj` — any two spoked isolating circle lassos around
  the SAME puncture are conjugate in `π₁(ℂ ∖ T, x₀)`: both circles live in
  a common punctured ball (`puncturedBallHomeo` presents it as a
  once-punctured plane), where winding around the puncture pins each to
  the same power of the cell generator; spokes absorb the difference as a
  conjugator.
* `normalClosure_isolatingLassos_eq_top` — for ANY choice of one
  isolating lasso per puncture, the normal closure of these `T.card`
  classes is all of `π₁(ℂ ∖ T, x₀)`.  Combined with the δ-winding matrix
  (`exists_winding_dual_loops`) this is the identified-generator
  presentation-level statement the slit-sheet program consumes.

Mathlib-only mathematical content.
-/
import Submission.Jacobians.Topology.LassoGeneration

namespace Jacobians.Topology

open Set Complex

local notation "Qmk" => Path.Homotopic.Quotient.mk

/-- The displacement of the standard circle has constant norm. -/
private theorem norm_circle_displacement (z s : ℂ) (t : unitInterval) :
    ‖(z - s) * Complex.exp (twoPiI * (t : ℝ))‖ = ‖z - s‖ := by
  have hre : (twoPiI * ((t : ℝ) : ℂ)).re = 0 := by
    simp [twoPiI, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]

/-- The standard circle around `s`, corestricted to a cell of the
punctured plane. -/
private noncomputable def cellCircle {T : Finset ℂ} (s : ℂ)
    (z : {w : ℂ // w ∉ (T : Set ℂ)})
    (hcirc : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ (T : Set ℂ))
    {A : Set {w : ℂ // w ∉ (T : Set ℂ)}} (hzA : z ∈ A)
    (hA : ∀ t : unitInterval,
      (⟨s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)), hcirc t⟩ :
        {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A) :
    Path (⟨z, hzA⟩ : A) ⟨z, hzA⟩ where
  toFun t := ⟨⟨s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
    hcirc t⟩, hA t⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (Subtype.ext (by simp))
  target' := Subtype.ext (Subtype.ext
    (by simp [twoPiI, Complex.exp_two_pi_mul_I]))

/-- **Equal classes for in-cell spoked circles**: inside a cell of the
punctured plane presented as a once-punctured plane, any two spoked
standard circles around the same puncture represent the same class. -/
private theorem spokedClass_cellCircle_eq {T : Finset ℂ} {s : ℂ}
    (hsT : s ∈ T) {A : Set {w : ℂ // w ∉ (T : Set ℂ)}} (a : ℂ)
    (φA : (A : Set _) ≃ₜ {w : ℂ // w ≠ a}) (yA : (A : Set _))
    {z₁ z₂ : {w : ℂ // w ∉ (T : Set ℂ)}}
    (hcirc₁ : ∀ t : unitInterval,
      s + ((z₁ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ (T : Set ℂ))
    (hcirc₂ : ∀ t : unitInterval,
      s + ((z₂ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ (T : Set ℂ))
    (hz₁A : z₁ ∈ A) (hz₂A : z₂ ∈ A)
    (hA₁ : ∀ t : unitInterval,
      (⟨s + ((z₁ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
        hcirc₁ t⟩ : {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A)
    (hA₂ : ∀ t : unitInterval,
      (⟨s + ((z₂ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
        hcirc₂ t⟩ : {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A)
    (ρ₁ : Path yA ⟨z₁, hz₁A⟩) (ρ₂ : Path yA ⟨z₂, hz₂A⟩) :
    spokedClass ρ₁ (cellCircle s z₁ hcirc₁ hz₁A hA₁)
      = spokedClass ρ₂ (cellCircle s z₂ hcirc₂ hz₂A hA₂) := by
  classical
  -- the ℤ-coordinate and the winding homomorphism of the cell
  set E : FundamentalGroup (A : Set _) yA ≃* Multiplicative ℤ :=
    (pi1MulEquivOfHomeomorph φA yA).trans
      (pi1PuncturedPlaneIntAt a (φA yA)).symm with hEdef
  set ιs : C((A : Set _), {w : ℂ // w ≠ s}) :=
    ⟨fun u => ⟨((u : {w : ℂ // w ∉ (T : Set ℂ)}) : ℂ),
      fun h => (u : {w : ℂ // w ∉ (T : Set ℂ)}).2
        (h ▸ Finset.mem_coe.mpr hsT)⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    with hιsdef
  set wA : FundamentalGroup (A : Set _) yA →* Multiplicative ℤ :=
    (pi1PuncturedPlaneIntAt s (ιs yA)).symm.toMonoidHom.comp
      (FundamentalGroup.mapOfEq ιs rfl) with hwAdef
  set g₀ := (pi1MulEquivOfHomeomorph φA yA).symm (FundamentalGroup.fromPath
    (Qmk (circleAround a (φA yA)))) with hg₀def
  have hEg₀ : E g₀ = Multiplicative.ofAdd 1 := by
    show (pi1PuncturedPlaneIntAt a (φA yA)).symm
      ((pi1MulEquivOfHomeomorph φA yA)
        ((pi1MulEquivOfHomeomorph φA yA).symm _)) = _
    rw [MulEquiv.apply_symm_apply, ← pi1PuncturedPlaneIntAt_ofAdd_one,
      MulEquiv.symm_apply_apply]
  set ε : ℤ := Multiplicative.toAdd (wA g₀) with hεdef
  -- each in-cell spoked circle has E-coordinate `m` with `m * ε = 1`
  have key : ∀ (z : {w : ℂ // w ∉ (T : Set ℂ)})
      (hcirc : ∀ t : unitInterval,
        s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ (T : Set ℂ))
      (hzA : z ∈ A)
      (hA' : ∀ t : unitInterval,
        (⟨s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
          hcirc t⟩ : {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A)
      (ρ : Path yA ⟨z, hzA⟩),
      Multiplicative.toAdd (E (spokedClass ρ (cellCircle s z hcirc hzA hA')))
        * ε = 1 := by
    intro z hcirc hzA hA' ρ
    set sc := spokedClass ρ (cellCircle s z hcirc hzA hA') with hscdef
    set m : ℤ := Multiplicative.toAdd (E sc) with hmdef
    -- the cyclic decomposition
    have hsc_pow : sc = g₀ ^ m := by
      have h1 : sc = E.symm (Multiplicative.ofAdd m) := by
        rw [hmdef, ofAdd_toAdd, MulEquiv.symm_apply_apply]
      have h2 : Multiplicative.ofAdd m
          = (Multiplicative.ofAdd (1 : ℤ)) ^ m := by
        rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
      have h3 : E.symm (Multiplicative.ofAdd 1) = g₀ := by
        rw [← hEg₀, MulEquiv.symm_apply_apply]
      rw [h1, h2, map_zpow, h3]
    -- the winding of the spoked circle is `1`
    have hwsc : wA sc = Multiplicative.ofAdd 1 := by
      show (pi1PuncturedPlaneIntAt s (ιs yA)).symm
          (FundamentalGroup.mapOfEq ιs rfl
            (spokedClass ρ (cellCircle s z hcirc hzA hA'))) = _
      rw [mapOfEq_spokedClass]
      have hcmap : (cellCircle s z hcirc hzA hA').map ιs.continuous
          = circleAround s (ιs ⟨z, hzA⟩) := by
        ext t
        rfl
      rw [hcmap, spokedClass_eq_transport,
        ← pi1PuncturedPlaneIntAt_ofAdd_one s (ιs ⟨z, hzA⟩),
        fundamentalGroupMulEquivOfPath_pi1PuncturedPlaneIntAt,
        MulEquiv.symm_apply_apply]
    -- combine
    have hw : Multiplicative.ofAdd (1 : ℤ) = Multiplicative.ofAdd (m * ε) := by
      have h1 : wA sc = (wA g₀) ^ m := by
        rw [hsc_pow, map_zpow]
      rw [← hwsc, h1, hεdef]
      conv_lhs => rw [← ofAdd_toAdd (wA g₀)]
      rw [← ofAdd_zsmul, smul_eq_mul]
    exact (Multiplicative.ofAdd.injective hw).symm
  -- compare the two circles through the shared `ε`
  have h₁ := key z₁ hcirc₁ hz₁A hA₁ ρ₁
  have h₂ := key z₂ hcirc₂ hz₂A hA₂ ρ₂
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h₁
    exact one_ne_zero h₁.symm
  have hmm : Multiplicative.toAdd
        (E (spokedClass ρ₁ (cellCircle s z₁ hcirc₁ hz₁A hA₁)))
      = Multiplicative.toAdd
        (E (spokedClass ρ₂ (cellCircle s z₂ hcirc₂ hz₂A hA₂))) :=
    mul_right_cancel₀ hε0 (h₁.trans h₂.symm)
  have hEE : E (spokedClass ρ₁ (cellCircle s z₁ hcirc₁ hz₁A hA₁))
      = E (spokedClass ρ₂ (cellCircle s z₂ hcirc₂ hz₂A hA₂)) := by
    have := congrArg Multiplicative.ofAdd hmm
    rwa [ofAdd_toAdd, ofAdd_toAdd] at this
  exact E.injective hEE

/-- A spoked isolating circle lasso around the puncture `s`: the open ball
of twice the circle's radius meets `T` only at `s`. -/
def IsIsolatingLasso (T : Finset ℂ) (x₀ : {z : ℂ // z ∉ (T : Set ℂ)})
    (s : ℂ) (g : FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀) : Prop :=
  ∃ (z : {w : ℂ // w ∉ (T : Set ℂ)})
    (hcirc : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ (T : Set ℂ))
    (_ : Metric.ball s (2 * ‖(z : ℂ) - s‖) ∩ (T : Set ℂ) ⊆ {s})
    (p : Path x₀ z),
    g = FundamentalGroup.fromPath (Qmk
      (p.trans ((circleInPunctured s z hcirc).trans p.symm)))

/-- **Meridian conjugacy for isolating lassos**: any two spoked isolating
circle lassos around the same puncture are conjugate. -/
theorem isolatingLasso_conj {T : Finset ℂ}
    {x₀ : {z : ℂ // z ∉ (T : Set ℂ)}} {s : ℂ} (hsT : s ∈ T)
    {g₁ g₂ : FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀}
    (hg₁ : IsIsolatingLasso T x₀ s g₁) (hg₂ : IsIsolatingLasso T x₀ s g₂) :
    ∃ u, g₁ = u⁻¹ * g₂ * u := by
  classical
  obtain ⟨z₁, hcirc₁, hiso₁, p₁, rfl⟩ := hg₁
  obtain ⟨z₂, hcirc₂, hiso₂, p₂, rfl⟩ := hg₂
  -- radii and the common punctured ball
  have hz₁s : (z₁ : ℂ) ≠ s := fun h => z₁.2 (h ▸ Finset.mem_coe.mpr hsT)
  have hz₂s : (z₂ : ℂ) ≠ s := fun h => z₂.2 (h ▸ Finset.mem_coe.mpr hsT)
  have hρ₁ : (0 : ℝ) < ‖(z₁ : ℂ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hz₁s)
  have hρ₂ : (0 : ℝ) < ‖(z₂ : ℂ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hz₂s)
  set R : ℝ := max (2 * ‖(z₁ : ℂ) - s‖) (2 * ‖(z₂ : ℂ) - s‖) with hRdef
  have hR : (0 : ℝ) < R := lt_max_of_lt_left (by linarith)
  set W : Set ℂ := Metric.ball s R with hWdef
  have hWo : IsOpen W := Metric.isOpen_ball
  have hWT : W ∩ (T : Set ℂ) = {s} := by
    apply Subset.antisymm
    · rintro w ⟨hwW, hwT⟩
      have hd : dist w s < R := by rwa [Metric.mem_ball] at hwW
      rcases lt_max_iff.mp (hRdef ▸ hd) with h | h
      · exact hiso₁ ⟨Metric.mem_ball.mpr h, hwT⟩
      · exact hiso₂ ⟨Metric.mem_ball.mpr h, hwT⟩
    · rintro w rfl
      exact ⟨Metric.mem_ball_self hR, Finset.mem_coe.mpr hsT⟩
  -- the cell and its presentation
  set A : Set {z : ℂ // z ∉ (T : Set ℂ)} := {z | (z : ℂ) ∈ W} with hAdef
  set φA : (A : Set _) ≃ₜ {w : ℂ // w ≠ s} :=
    (cellFlatten T W s hsT hWT).trans (puncturedBallHomeo s R hR) with hφAdef
  -- the circles stay in the cell
  have hcircle_mem : ∀ (z : {w : ℂ // w ∉ (T : Set ℂ)}),
      ‖(z : ℂ) - s‖ * 2 ≤ R →
      ∀ t : unitInterval,
        s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∈ W := by
    intro z hzR t
    have hz0 : (0 : ℝ) ≤ ‖(z : ℂ) - s‖ := norm_nonneg _
    rw [hWdef, Metric.mem_ball, Complex.dist_eq,
      show s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) - s
        = ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) by ring,
      norm_circle_displacement]
    by_cases hz : ‖(z : ℂ) - s‖ = 0
    · rw [hz]
      exact hR
    · have : (0 : ℝ) < ‖(z : ℂ) - s‖ := lt_of_le_of_ne hz0 (Ne.symm hz)
      linarith
  have hz₁W : ∀ t : unitInterval,
      s + ((z₁ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∈ W :=
    hcircle_mem z₁ (by rw [hRdef]; rw [mul_comm]; exact le_max_left _ _)
  have hz₂W : ∀ t : unitInterval,
      s + ((z₂ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∈ W :=
    hcircle_mem z₂ (by rw [hRdef]; rw [mul_comm]; exact le_max_right _ _)
  have hz₁A : z₁ ∈ A := by
    have h0 := hz₁W 0
    simpa using h0
  have hz₂A : z₂ ∈ A := by
    have h0 := hz₂W 0
    simpa using h0
  have hA₁ : ∀ t : unitInterval,
      (⟨s + ((z₁ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
        hcirc₁ t⟩ : {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A := fun t => hz₁W t
  have hA₂ : ∀ t : unitInterval,
      (⟨s + ((z₂ : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)),
        hcirc₂ t⟩ : {w : ℂ // w ∉ (T : Set ℂ)}) ∈ A := fun t => hz₂W t
  -- in-cell comparison at basepoint `z₁`
  haveI hpcP : PathConnectedSpace {w : ℂ // w ≠ s} :=
    pathConnectedSpace_puncturedPlane s
  haveI hpcA : PathConnectedSpace (A : Set _) :=
    pathConnectedSpace_of_homeomorph φA.symm
  obtain ⟨ρ⟩ := PathConnectedSpace.joined
    (⟨z₁, hz₁A⟩ : (A : Set _)) ⟨z₂, hz₂A⟩
  have hEq := spokedClass_cellCircle_eq hsT s φA (⟨z₁, hz₁A⟩ : (A : Set _))
    hcirc₁ hcirc₂ hz₁A hz₂A hA₁ hA₂ (Path.refl _) ρ
  -- push into the punctured plane
  have hpushL : FundamentalGroup.mapOfEq (inclusionCM A) rfl
      (spokedClass (Path.refl (⟨z₁, hz₁A⟩ : (A : Set _)))
        (cellCircle s z₁ hcirc₁ hz₁A hA₁))
      = FundamentalGroup.fromPath (Qmk (circleInPunctured s z₁ hcirc₁)) := by
    rw [mapOfEq_spokedClass, ← spokedClass_refl (circleInPunctured s z₁ hcirc₁)]
    exact spokedClass_of_eq rfl _ _ _ _ (fun t => rfl) (fun t => rfl)
  have hpushR : FundamentalGroup.mapOfEq (inclusionCM A) rfl
      (spokedClass ρ (cellCircle s z₂ hcirc₂ hz₂A hA₂))
      = spokedClass (ρ.map (inclusionCM A).continuous)
          (circleInPunctured s z₂ hcirc₂) := by
    rw [mapOfEq_spokedClass]
    exact spokedClass_of_eq rfl _ _ _ _ (fun t => rfl) (fun t => rfl)
  have hpush : FundamentalGroup.fromPath (Qmk (circleInPunctured s z₁ hcirc₁))
      = spokedClass (ρ.map (inclusionCM A).continuous)
          (circleInPunctured s z₂ hcirc₂) :=
    hpushL.symm.trans
      ((congrArg (FundamentalGroup.mapOfEq (inclusionCM A) rfl) hEq).trans
        hpushR)
  -- hpush : ⟦circle₁⟧ = spokedClass (ρ.map ι) circle₂  at basepoint z₁
  -- conjugate through the spokes
  set ρX := ρ.map (inclusionCM A).continuous with hρXdef
  set q₁ : Path x₀ z₂ := p₁.trans ρX with hq₁def
  have hg₁eq : spokedClass p₁ (circleInPunctured s z₁ hcirc₁)
      = spokedClass q₁ (circleInPunctured s z₂ hcirc₂) := by
    rw [spokedClass_eq_transport, hpush, hq₁def, spokedClass_trans]
    exact (spokedClass_eq_transport p₁ _).symm
  -- rewrite the `q₁` spoke through `p₂` with a loop conjugator
  have hq : Qmk ((q₁.trans p₂.symm).trans p₂) = Qmk q₁ := by
    rw [mk_trans_assoc, Path.Homotopic.Quotient.mk_trans q₁ (p₂.symm.trans p₂)]
    have h2 : Qmk (p₂.symm.trans p₂) = Qmk (Path.refl z₂) :=
      Quotient.sound (Path.Homotopic.symm_trans p₂)
    rw [h2, ← Path.Homotopic.Quotient.mk_trans]
    exact Quotient.sound ⟨Path.Homotopy.transRefl q₁⟩
  refine ⟨FundamentalGroup.fromPath (Qmk (q₁.trans p₂.symm)), ?_⟩
  show spokedClass p₁ (circleInPunctured s z₁ hcirc₁) = _
  rw [hg₁eq, spokedClass_congr _ hq.symm, spokedClass_trans,
    spokedClass_loop_conj]

/-- **B1, sharp form: one isolating lasso per puncture normally generates
`π₁(ℂ ∖ T, x₀)`.** -/
theorem normalClosure_isolatingLassos_eq_top (T : Finset ℂ)
    (x₀ : {z : ℂ // z ∉ (T : Set ℂ)})
    (L : ℂ → FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀)
    (hL : ∀ s ∈ T, IsIsolatingLasso T x₀ s (L s)) :
    Subgroup.normalClosure (L '' (T : Set ℂ)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath g)
  have hg : g = FundamentalGroup.fromPath (Qmk γ) := hγ.symm
  rw [hg]
  refine fromPath_mem_of_circleLassos_mem T x₀ _ ?_ γ
  intro s hs z hcirc hiso p
  obtain ⟨u, hu⟩ := isolatingLasso_conj hs
    (⟨z, hcirc, hiso, p, rfl⟩ : IsIsolatingLasso T x₀ s _) (hL s hs)
  rw [hu]
  have hmem : L s ∈ Subgroup.normalClosure (L '' (T : Set ℂ)) :=
    Subgroup.subset_normalClosure ⟨s, Finset.mem_coe.mpr hs, rfl⟩
  have hnormal := Subgroup.normalClosure_normal
    (s := L '' (T : Set ℂ))
    (G := FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀)
  have hconj := hnormal.conj_mem _ hmem u⁻¹
  rwa [inv_inv] at hconj

end Jacobians.Topology
