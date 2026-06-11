/-
# Lasso loops around punctures with δ winding matrix

M3-partial of the SVK-lite ladder (`docs/planning/SVK_ROUTE.md`): for a finite
puncture set `S ⊆ ℂ` and any basepoint `x₀`, we construct for every `s ∈ S` an
explicit lasso loop (path to a small circle around `s`, around, and back) whose
winding numbers are `1` around `s` and `0` around every other puncture
(`exists_winding_dual_loops`). Together with `windingHom` this identifies the
puncture loops as ℤ-independent elements of `π₁(ℂ ∖ S, x₀)` (and of its
abelianization `H₁`) — the identified-generator lower-bound half of "π₁ of the
punctured plane is free on loops around the punctures", in the form the
`AX_PeriodCycleBasis` slit-sheet program consumes
(`docs/planning/CYCLEBASIS_ALTERNATIVES.md` direction 2b). The generation upper
bound and nonabelian freeness require Seifert–van Kampen and are tracked in
`docs/planning/SVK_BLOCKER.md`.

Main ingredients:
* `mk_eq_refl_of_mem_isSimplyConnected` — a loop inside a simply connected
  subset is nullhomotopic in the ambient space;
* `circleAround` + `pi1PuncturedPlaneIntAt_ofAdd_one` — the circle through any
  point `z` around `s` represents the generator of `π₁(ℂ ∖ {s}, z)`;
* `fundamentalGroupMulEquivOfPath_pi1PuncturedPlaneIntAt` — the ℤ-isomorphisms
  at different basepoints commute with basepoint transport (lift computation);
* `fromPath_conj_eq_one` — a lasso around a nullhomotopic circle is trivial.

Mathlib-only mathematical content. Sorry-free and axiom-free
(beyond the three standard axioms).
-/
import Mathlib
import Jacobians.Topology.WindingNumber

namespace Jacobians.Topology

open Complex CategoryTheory

/-! ## Loops inside simply connected subsets are nullhomotopic -/

/-- A loop whose image lies in a simply connected subset is nullhomotopic in the
ambient space. -/
theorem mk_eq_refl_of_mem_isSimplyConnected {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsSimplyConnected U) {x : X} (L : Path x x) (hL : ∀ t, L t ∈ U) :
    Path.Homotopic.Quotient.mk L = Path.Homotopic.Quotient.mk (Path.refl x) := by
  haveI : SimplyConnectedSpace U := hU.simplyConnectedSpace
  have hx : x ∈ U := by
    have h0 := hL 0
    rwa [show L 0 = x from L.source] at h0
  set pt : U := ⟨x, hx⟩ with hpt
  set L' : Path pt pt :=
    { toFun := fun t ↦ ⟨L t, hL t⟩
      continuous_toFun := by fun_prop
      source' := by
        apply Subtype.ext
        show (L 0 : X) = x
        exact L.source
      target' := by
        apply Subtype.ext
        show (L 1 : X) = x
        exact L.target } with hL'
  have h1 : Path.Homotopic.Quotient.mk L' = Path.Homotopic.Quotient.mk (Path.refl pt) :=
    Subsingleton.elim _ _
  have h2 := congrArg (fun q : Path.Homotopic.Quotient pt pt ↦
    q.map ⟨Subtype.val, continuous_subtype_val⟩) h1
  simp only [← Path.Homotopic.Quotient.mk_map] at h2
  have e1 : L'.map continuous_subtype_val = L := by
    ext t
    rfl
  have e2 : (Path.refl pt).map continuous_subtype_val = Path.refl x := by
    ext t
    rfl
  rwa [e1, e2] at h2

/-! ## The circle generator at an arbitrary point of the punctured plane -/

/-- The circle through `z` around the puncture `s`: `t ↦ s + (z - s)·exp(2πit)`. -/
noncomputable def circleAround (s : ℂ) (z : {w : ℂ // w ≠ s}) : Path z z where
  toFun t := ⟨s + (z.1 - s) * Complex.exp (twoPiI * (t : ℝ)),
    by simp [sub_ne_zero.mpr z.2, Complex.exp_ne_zero]⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp [twoPiI, Complex.exp_two_pi_mul_I])

@[simp] theorem circleAround_coe (s : ℂ) (z : {w : ℂ // w ≠ s}) (t : unitInterval) :
    (circleAround s z t : ℂ) = s + (z.1 - s) * Complex.exp (twoPiI * (t : ℝ)) := rfl

/-- The circle through `z` represents the generator of `π₁(ℂ ∖ {s}, z)`. -/
theorem pi1PuncturedPlaneIntAt_ofAdd_one (s : ℂ) (z : {w : ℂ // w ≠ s}) :
    pi1PuncturedPlaneIntAt s z (Multiplicative.ofAdd 1)
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleAround s z)) := by
  have hlog : Complex.exp (Complex.log (z.1 - s)) = z.1 - s :=
    Complex.exp_log (sub_ne_zero.mpr z.2)
  refine pi1PuncturedPlaneIntOn_eq_fromPath s (Complex.log (z.1 - s)) z
    (Subtype.ext (by simp [hlog])) 1 (circleAround s z)
    ⟨⟨fun t ↦ twoPiI * (t : ℝ) + Complex.log (z.1 - s), by fun_prop⟩,
      by simp, by simp⟩ fun t ↦ ?_
  apply Subtype.ext
  show (expAround s (twoPiI * (t : ℝ) + Complex.log (z.1 - s)) : ℂ)
    = s + (z.1 - s) * Complex.exp (twoPiI * (t : ℝ))
  rw [expAround_coe, Complex.exp_add, hlog]
  ring

/-! ## Basepoint transport -/

/-- Basepoint transport along `α` acts on loop classes by `γ ↦ α⁻¹ · γ · α`. -/
theorem fundamentalGroupMulEquivOfPath_fromPath {X : Type*} [TopologicalSpace X]
    {x y : X} (α : Path x y) (γ : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath α
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
      = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (α.symm.trans (γ.trans α))) := by
  show ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk α : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)).conj
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = _
  rw [Iso.conj_apply]
  rfl

/-- The covering `expAround s` is periodic with period `2πi`. -/
theorem expAround_add_twoPiI (s w : ℂ) : expAround s (twoPiI + w) = expAround s w := by
  apply Subtype.ext
  simp [Complex.exp_add, twoPiI, Complex.exp_two_pi_mul_I]

/-- **The ℤ-isomorphisms of `π₁(ℂ ∖ {s})` at different basepoints commute with
basepoint transport**: transporting the `n`-fold circle class along any path gives
the `n`-fold circle class at the new basepoint. Proved by an explicit three-segment
lift through `expAround s`. -/
theorem fundamentalGroupMulEquivOfPath_pi1PuncturedPlaneIntAt (s : ℂ)
    {z z' : {w : ℂ // w ≠ s}} (α : Path z z') (g : Multiplicative ℤ) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath α (pi1PuncturedPlaneIntAt s z g)
      = pi1PuncturedPlaneIntAt s z' g := by
  have key : FundamentalGroup.fundamentalGroupMulEquivOfPath α
      (pi1PuncturedPlaneIntAt s z (Multiplicative.ofAdd 1))
      = pi1PuncturedPlaneIntAt s z' (Multiplicative.ofAdd 1) := by
    rw [pi1PuncturedPlaneIntAt_ofAdd_one s z, fundamentalGroupMulEquivOfPath_fromPath]
    refine Eq.symm ?_
    set cov := (isAddQuotientCoveringMap_expAround s).isCoveringMap with hcov
    set e₀' := Complex.log (z'.1 - s) with he₀'
    have hze' : expAround s e₀' = z' :=
      Subtype.ext (by simp [he₀', Complex.exp_log (sub_ne_zero.mpr z'.2)])
    -- lift `α.symm` from `e₀'`
    set Γ₁ : C(unitInterval, ℂ) :=
      cov.liftPath (α.symm : C(unitInterval, {w : ℂ // w ≠ s})) e₀'
        (α.symm.source.trans hze'.symm) with hΓ₁
    have hΓ₁lifts : ∀ t, expAround s (Γ₁ t) = α.symm t := fun t ↦
      congr_fun (cov.liftPath_lifts ..) t
    have hΓ₁zero : Γ₁ 0 = e₀' := cov.liftPath_zero ..
    have hexpend : Complex.exp (Γ₁ 1) = z.1 - s := by
      have h1 : (expAround s (Γ₁ 1) : ℂ) = (z : ℂ) := by
        rw [hΓ₁lifts 1]
        exact congrArg Subtype.val α.symm.target
      rw [expAround_coe] at h1
      linear_combination h1
    -- the three lift segments
    set Γ₁p : Path e₀' (Γ₁ 1) := ⟨Γ₁, hΓ₁zero, rfl⟩ with hΓ₁p
    set Γ₂p : Path (Γ₁ 1) (twoPiI + Γ₁ 1) :=
      ⟨⟨fun t ↦ twoPiI * (t : ℝ) + Γ₁ 1, by fun_prop⟩, by simp, by simp⟩ with hΓ₂p
    set Γ₃p : Path (twoPiI + Γ₁ 1) (twoPiI + e₀') :=
      Γ₁p.symm.map (continuous_const.add continuous_id) with hΓ₃p
    have hmid : ∀ u : unitInterval, expAround s (Γ₂p u) = circleAround s z u := by
      intro u
      apply Subtype.ext
      rw [circleAround_coe]
      show (expAround s (twoPiI * (u : ℝ) + Γ₁ 1) : ℂ)
        = s + ((z : ℂ) - s) * Complex.exp (twoPiI * (u : ℝ))
      rw [expAround_coe, Complex.exp_add, hexpend]
      ring
    have hthird : ∀ u : unitInterval, expAround s (Γ₃p u) = α u := by
      intro u
      show expAround s (twoPiI + Γ₁ (unitInterval.symm u)) = α u
      rw [expAround_add_twoPiI, hΓ₁lifts]
      show α.symm (unitInterval.symm u) = α u
      simp [Path.symm_apply]
    refine pi1PuncturedPlaneIntOn_eq_fromPath s e₀' z' hze' 1 _
      ((Γ₁p.trans (Γ₂p.trans Γ₃p)).cast rfl (by rw [one_smul])) (fun t ↦ ?_)
    show expAround s ((Γ₁p.trans (Γ₂p.trans Γ₃p)) t)
      = (α.symm.trans ((circleAround s z).trans α)) t
    simp only [Path.trans_apply]
    split_ifs
    · exact hΓ₁lifts _
    · exact hmid _
    · exact hthird _
  have hcomp : ((FundamentalGroup.fundamentalGroupMulEquivOfPath α).toMonoidHom.comp
        (pi1PuncturedPlaneIntAt s z).toMonoidHom)
      = (pi1PuncturedPlaneIntAt s z').toMonoidHom :=
    MonoidHom.ext_mint key
  exact DFunLike.congr_fun hcomp g

/-! ## Lassos -/

/-- A lasso around a nullhomotopic circle is trivial: `P · C · P⁻¹ ≃ refl` when
`C ≃ refl`. -/
theorem fromPath_conj_eq_one {X : Type*} [TopologicalSpace X] {x c : X}
    (P : Path x c) (C : Path c c)
    (hC : Path.Homotopic.Quotient.mk C = Path.Homotopic.Quotient.mk (Path.refl c)) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (P.trans (C.trans P.symm))) = 1 := by
  have h1 : Path.Homotopic.Quotient.mk (P.trans (C.trans P.symm))
      = (Path.Homotopic.Quotient.mk P).trans ((Path.Homotopic.Quotient.mk C).trans
          (Path.Homotopic.Quotient.mk P.symm)) := by
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans]
  have h3 : Path.Homotopic.Quotient.mk ((Path.refl c).trans P.symm)
      = Path.Homotopic.Quotient.mk P.symm :=
    Quotient.sound ⟨Path.Homotopy.reflTrans P.symm⟩
  have h5 : Path.Homotopic.Quotient.mk (P.trans P.symm)
      = Path.Homotopic.Quotient.mk (Path.refl x) :=
    Quotient.sound ⟨(Path.Homotopy.reflTransSymm P).symm⟩
  show FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (P.trans (C.trans P.symm))) = 1
  rw [h1, hC, ← Path.Homotopic.Quotient.mk_trans, h3, ← Path.Homotopic.Quotient.mk_trans, h5]
  rfl

variable {S : Set ℂ}

/-- The circle through `z` around the puncture `s ∈ S`, as a loop in the multiply
punctured plane (under the hypothesis that it avoids all punctures). -/
noncomputable def circleInPunctured (s : ℂ) (z : {w : ℂ // w ∉ S})
    (hcirc : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ S) :
    Path z z where
  toFun t := ⟨s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)), hcirc t⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp [twoPiI, Complex.exp_two_pi_mul_I])

/-- **Diagonal winding of a lasso.** The lasso `P · circle · P⁻¹` around `s` has
winding number `1` around `s`. -/
theorem windingHom_lasso_self {s : ℂ} (hs : s ∈ S)
    {x₀ z : {w : ℂ // w ∉ S}} (P : Path x₀ z)
    (hcirc : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ S) :
    windingHom hs x₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.trans ((circleInPunctured s z hcirc).trans P.symm))))
      = Multiplicative.ofAdd 1 := by
  show (pi1PuncturedPlaneIntAt s (puncturedInclusion hs x₀)).symm
      (FundamentalGroup.mapOfEq (puncturedInclusion hs) rfl
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.trans ((circleInPunctured s z hcirc).trans P.symm)))))
    = Multiplicative.ofAdd 1
  rw [FundamentalGroup.mapOfEq_apply]
  have hcast : ((P.trans ((circleInPunctured s z hcirc).trans P.symm)).map
        (puncturedInclusion hs).continuous).cast (Eq.symm rfl) (Eq.symm rfl)
      = (P.map (puncturedInclusion hs).continuous).trans
          ((circleAround s (puncturedInclusion hs z)).trans
            (P.map (puncturedInclusion hs).continuous).symm) := by
    rw [Path.cast_rfl_rfl, Path.map_trans, Path.map_trans, Path.map_symm]
    have hmid : (circleInPunctured s z hcirc).map (puncturedInclusion hs).continuous
        = circleAround s (puncturedInclusion hs z) := by
      ext t
      rfl
    rw [hmid]
  rw [hcast]
  have hconj := fundamentalGroupMulEquivOfPath_fromPath
    (P.map (puncturedInclusion hs).continuous).symm
    (circleAround s (puncturedInclusion hs z))
  rw [Path.symm_symm] at hconj
  rw [← hconj, ← pi1PuncturedPlaneIntAt_ofAdd_one,
    fundamentalGroupMulEquivOfPath_pi1PuncturedPlaneIntAt]
  exact MulEquiv.symm_apply_apply _ _

/-- **Off-diagonal winding of a lasso.** If the circle of the lasso around `s` lies
in a convex set avoiding the puncture `s'`, the lasso has winding number `0`
around `s'` (the connecting path `P` is arbitrary). -/
theorem windingHom_lasso_ne {s s' : ℂ} (hs' : s' ∈ S)
    {x₀ z : {w : ℂ // w ∉ S}} (P : Path x₀ z)
    (hcirc : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∉ S)
    {K : Set ℂ} (hK : Convex ℝ K) (hs'K : s' ∉ K)
    (hcircK : ∀ t : unitInterval,
      s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)) ∈ K) :
    windingHom hs' x₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.trans ((circleInPunctured s z hcirc).trans P.symm)))) = 1 := by
  haveI : ContractibleSpace K := hK.contractibleSpace ⟨_, hcircK 0⟩
  have hzK : (z : ℂ) ∈ K := by
    have h0 := hcircK 0
    simpa using h0
  set ptK : K := ⟨(z : ℂ), hzK⟩ with hptK
  -- the circle, corestricted to `K`
  set circleK : Path ptK ptK :=
    { toFun := fun t ↦ ⟨s + ((z : ℂ) - s) * Complex.exp (twoPiI * (t : ℝ)), hcircK t⟩
      continuous_toFun := by fun_prop
      source' := Subtype.ext (by simp [hptK])
      target' := Subtype.ext (by simp [hptK, twoPiI, Complex.exp_two_pi_mul_I]) } with hcircleK
  set ιK : C(K, {w : ℂ // w ≠ s'}) :=
    ⟨fun w ↦ ⟨w.1, fun h ↦ hs'K (by rw [← h]; exact w.2)⟩,
      continuous_subtype_val.subtype_mk _⟩ with hιK
  -- the mapped circle is nullhomotopic in `ℂ ∖ {s'}`
  have hmidtriv : Path.Homotopic.Quotient.mk
        ((circleInPunctured s z hcirc).map (puncturedInclusion hs').continuous)
      = Path.Homotopic.Quotient.mk (Path.refl (puncturedInclusion hs' z)) := by
    have h1 : Path.Homotopic.Quotient.mk circleK
        = Path.Homotopic.Quotient.mk (Path.refl ptK) := Subsingleton.elim _ _
    have h2 := congrArg (fun q : Path.Homotopic.Quotient ptK ptK ↦ q.map ιK) h1
    simp only [← Path.Homotopic.Quotient.mk_map] at h2
    have e1 : circleK.map ιK.continuous
        = (circleInPunctured s z hcirc).map (puncturedInclusion hs').continuous := by
      ext t
      rfl
    have e2 : (Path.refl ptK).map ιK.continuous = Path.refl (puncturedInclusion hs' z) := by
      ext t
      rfl
    rwa [e1, e2] at h2
  show (pi1PuncturedPlaneIntAt s' (puncturedInclusion hs' x₀)).symm
      (FundamentalGroup.mapOfEq (puncturedInclusion hs') rfl
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.trans ((circleInPunctured s z hcirc).trans P.symm))))) = 1
  rw [FundamentalGroup.mapOfEq_apply]
  have hcast : ((P.trans ((circleInPunctured s z hcirc).trans P.symm)).map
        (puncturedInclusion hs').continuous).cast (Eq.symm rfl) (Eq.symm rfl)
      = (P.map (puncturedInclusion hs').continuous).trans
          (((circleInPunctured s z hcirc).map (puncturedInclusion hs').continuous).trans
            (P.map (puncturedInclusion hs').continuous).symm) := by
    rw [Path.cast_rfl_rfl, Path.map_trans, Path.map_trans, Path.map_symm]
  rw [hcast, fromPath_conj_eq_one _ _ hmidtriv]
  exact map_one _

end Jacobians.Topology
