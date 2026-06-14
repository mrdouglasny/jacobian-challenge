/-
# Winding-number homomorphisms on the multiply punctured plane

M2-lite of the SVK-lite ladder (`docs/planning/SVK_ROUTE.md`): for a set of
punctures `S ⊆ ℂ` and `s ∈ S`, composing the π₁-functoriality of the inclusion
`ℂ ∖ S ↪ ℂ ∖ {s}` with the M1 isomorphism `π₁(ℂ ∖ {s}) ≃* Multiplicative ℤ`
gives the winding-number homomorphism

  `windingHom : π₁(ℂ ∖ S, x₀) →* Multiplicative ℤ`.

Computation rules:
* `windingHom_fromPath` — a loop lifting through `expAround s` to a path with
  endpoint displacement `n • 2πi` has winding number `n` around `s`;
* `windingHom_eq_one_of_convex` — a loop whose image lies in a convex set
  avoiding `s` has winding number `0` around `s` (the off-diagonal rule: a
  small circle around another puncture `s'` winds `0` times around `s`).

Together these identify the puncture loops as ℤ-independent classes in
`π₁(ℂ ∖ S)` — the lower-bound half of "π₁ of the punctured plane is free on
the puncture loops", in the form the `AX_PeriodCycleBasis` slit-sheet program
consumes (`docs/planning/CYCLEBASIS_ALTERNATIVES.md` direction 2b).

Mathlib-only mathematical content. Sorry-free and axiom-free
(beyond the three standard axioms).
-/
import Mathlib
import Submission.Jacobians.Topology.PuncturedPlanePi1

namespace Jacobians.Topology

open Complex

variable {S : Set ℂ}

/-- The multiply punctured plane includes into the singly punctured plane at each
puncture. -/
def puncturedInclusion {s : ℂ} (hs : s ∈ S) : C({z : ℂ // z ∉ S}, {z : ℂ // z ≠ s}) :=
  ⟨fun z ↦ ⟨z.1, fun h ↦ z.2 (by rw [h]; exact hs)⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem puncturedInclusion_coe {s : ℂ} (hs : s ∈ S) (z : {z : ℂ // z ∉ S}) :
    (puncturedInclusion hs z : ℂ) = z := rfl

/-- **The winding-number homomorphism** around the puncture `s ∈ S`, on the
fundamental group of `ℂ ∖ S`. -/
noncomputable def windingHom {s : ℂ} (hs : s ∈ S) (x₀ : {z : ℂ // z ∉ S}) :
    FundamentalGroup {z : ℂ // z ∉ S} x₀ →* Multiplicative ℤ :=
  (pi1PuncturedPlaneIntAt s (puncturedInclusion hs x₀)).symm.toMonoidHom.comp
    (FundamentalGroup.mapOfEq (puncturedInclusion hs) rfl)

/-- **Winding computation by lifting.** If the loop `L` at `x₀` in `ℂ ∖ S` lifts
pointwise through `expAround s` to a path in `ℂ` with endpoint displacement
`n • 2πi`, then its winding number around `s` is `n`. -/
theorem windingHom_fromPath {s : ℂ} (hs : s ∈ S) (x₀ : {z : ℂ // z ∉ S})
    (L : Path x₀ x₀) (n : ℤ) (e₀ : ℂ)
    (he₀ : expAround s e₀ = puncturedInclusion hs x₀)
    (Γ : Path e₀ (n • twoPiI + e₀))
    (hΓ : ∀ t, (expAround s (Γ t) : ℂ) = L t) :
    windingHom hs x₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))
      = Multiplicative.ofAdd n := by
  show (pi1PuncturedPlaneIntAt s (puncturedInclusion hs x₀)).symm
      (FundamentalGroup.mapOfEq (puncturedInclusion hs) rfl
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)))
    = Multiplicative.ofAdd n
  rw [FundamentalGroup.mapOfEq_apply, MulEquiv.symm_apply_eq,
    pi1PuncturedPlaneIntAt_eq_intOn s e₀ _ he₀]
  refine (pi1PuncturedPlaneIntOn_eq_fromPath s e₀ _ he₀ n _ Γ fun t ↦ ?_).symm
  exact Subtype.ext (hΓ t)

/-- **Off-diagonal vanishing.** A loop whose image lies in a convex set avoiding the
puncture `s` has winding number `0` around `s`. In particular a small circle around
a different puncture `s'` does not wind around `s`. -/
theorem windingHom_eq_one_of_convex {s : ℂ} (hs : s ∈ S) (x₀ : {z : ℂ // z ∉ S})
    (L : Path x₀ x₀) {K : Set ℂ} (hK : Convex ℝ K) (hsK : s ∉ K)
    (hLK : ∀ t, (L t : ℂ) ∈ K) :
    windingHom hs x₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = 1 := by
  haveI : ContractibleSpace K := hK.contractibleSpace ⟨L 0, hLK 0⟩
  have hx₀K : (x₀ : ℂ) ∈ K := by
    have := hLK 0
    rwa [show L 0 = x₀ from L.source] at this
  set pt : K := ⟨(x₀ : ℂ), hx₀K⟩ with hpt
  -- corestrict `L` to `K`
  set L' : Path pt pt :=
    { toFun := fun t ↦ ⟨L t, hLK t⟩
      continuous_toFun := by fun_prop
      source' := by
        apply Subtype.ext
        show (L 0 : ℂ) = (x₀ : ℂ)
        exact congrArg Subtype.val L.source
      target' := by
        apply Subtype.ext
        show (L 1 : ℂ) = (x₀ : ℂ)
        exact congrArg Subtype.val L.target } with hL'
  -- the inclusion `K → ℂ ∖ {s}`
  set ιK : C(K, {z : ℂ // z ≠ s}) :=
    ⟨fun w ↦ ⟨w.1, fun h ↦ hsK (by rw [← h]; exact w.2)⟩,
      continuous_subtype_val.subtype_mk _⟩ with hιK
  haveI : Subsingleton (FundamentalGroup K pt) :=
    inferInstanceAs (Subsingleton (Path.Homotopic.Quotient pt pt))
  show (pi1PuncturedPlaneIntAt s (puncturedInclusion hs x₀)).symm
      (FundamentalGroup.mapOfEq (puncturedInclusion hs) rfl
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))) = 1
  rw [FundamentalGroup.mapOfEq_apply]
  have hfactor : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((L.map (puncturedInclusion hs).continuous).cast rfl rfl))
      = FundamentalGroup.mapOfEq ιK (rfl : ιK pt = puncturedInclusion hs x₀)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L')) := by
    rw [FundamentalGroup.mapOfEq_apply]
    refine congrArg (fun q : Path (puncturedInclusion hs x₀) (puncturedInclusion hs x₀) ↦
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) ?_
    ext t
    rfl
  rw [hfactor, Subsingleton.elim
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L')) 1, map_one]
  exact map_one _

end Jacobians.Topology
