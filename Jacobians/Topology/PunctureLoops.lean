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

end Jacobians.Topology
