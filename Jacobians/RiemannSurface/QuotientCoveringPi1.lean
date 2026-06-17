/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
# Fundamental group of a quotient by a discrete subgroup: `π₁(V ⧸ Λ) ≅ Λ`

For a topological abelian group `V` and a discrete subgroup `Λ ≤ V`, the
projection `p : V → V ⧸ Λ` is a covering map (Mathlib,
`AddSubgroup.isAddQuotientCoveringMap_of_comm`). This file computes the
fundamental group of the quotient at the basepoint `0`:

* `pathLiftEnd Λ γ₀` — the endpoint in `V` of the unique lift through `p`
  (starting at `0 ∈ V`) of a loop `γ₀` at `0 ∈ V ⧸ Λ`; it lies in `Λ`
  (`pathLiftEnd_mem`).
* `loopLiftEnd Λ` — the same on homotopy classes, well defined by the
  homotopy lifting property (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
* `pi1ToLattice Λ : FundamentalGroup (V ⧸ Λ) 0 →* Multiplicative Λ` — the
  endpoint map is a group homomorphism (lifting a concatenation concatenates
  the lifts, translated by the first endpoint).
* `pi1ToLattice_injective` — for `V` simply connected: a loop whose lift is a
  loop is nullhomotopic (project a nullhomotopy of the lift).
* `pi1ToLattice_surjective` — for `V` a real topological vector space: the
  straight-line path `t ↦ t • c` projects to a loop with endpoint `c`.
* `pi1EquivLattice : FundamentalGroup (V ⧸ Λ) 0 ≃* Multiplicative Λ`.
* `h1EquivLattice : H1 (V ⧸ Λ) 0 ≃+ Λ` — the induced Hurewicz/abelianization
  form, with the computation rule `h1EquivLattice_loopClass`.

The intended consumers are the complex tori of this development:
`Elliptic ω₁ ω₂ h = ℂ ⧸ (ℤω₁ + ℤω₂)` (g = 1, see `EllipticH1.lean`) and the
Jacobian `ℂ^g ⧸ Λ` (future work).

## References

* A. Hatcher, *Algebraic Topology*, §1.3 (Proposition 1.31, Theorem 1.7's
  argument generalized from `S¹ = ℝ/ℤ`).
-/
import Jacobians.RiemannSurface.Homology

namespace Jacobians.RiemannSurface

set_option linter.unusedSectionVars false

open Function

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  (Λ : AddSubgroup V) [DiscreteTopology Λ]

/-- The quotient projection `V → V ⧸ Λ` by a discrete subgroup of a topological
abelian group is a covering map. -/
theorem isCoveringMap_quotientAddGroup_mk' :
    IsCoveringMap ((QuotientAddGroup.mk' Λ) : V → V ⧸ Λ) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm Λ DiscreteTopology.isDiscrete).isCoveringMap

variable {Λ}

/-- A loop at `0 : V ⧸ Λ` starts at the image of `0 : V`. -/
theorem loop_zero_eq_mk' (γ₀ : Path (0 : V ⧸ Λ) 0) :
    γ₀ 0 = QuotientAddGroup.mk' Λ (0 : V) :=
  γ₀.source.trans (map_zero _).symm

variable (Λ)

/-- The endpoint in `V` of the lift (starting at `0 : V`) of a loop at
`0 : V ⧸ Λ`. -/
noncomputable def pathLiftEnd (γ₀ : Path (0 : V ⧸ Λ) 0) : V :=
  (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ (0 : V) (loop_zero_eq_mk' γ₀) 1

/-- Lift-endpoint computation rule: any continuous pointwise lift of `γ₀`
starting at `0` computes `pathLiftEnd`. -/
theorem pathLiftEnd_eq (γ₀ : Path (0 : V ⧸ Λ) 0) (Γ : unitInterval → V)
    (hΓ : Continuous Γ) (hΓ0 : Γ 0 = 0)
    (hlift : ∀ t, QuotientAddGroup.mk' Λ (Γ t) = γ₀ t) :
    pathLiftEnd Λ γ₀ = Γ 1 := by
  have hΓeq : Γ = (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ (0 : V)
      (loop_zero_eq_mk' γ₀) :=
    ((isCoveringMap_quotientAddGroup_mk' Λ).eq_liftPath_iff _).mpr
      ⟨hΓ, funext hlift, hΓ0⟩
  exact (congr_fun hΓeq 1).symm

/-- The lift endpoint of a loop lies in `Λ`. -/
theorem pathLiftEnd_mem (γ₀ : Path (0 : V ⧸ Λ) 0) : pathLiftEnd Λ γ₀ ∈ Λ := by
  have h1 : QuotientAddGroup.mk' Λ (pathLiftEnd Λ γ₀) = γ₀ 1 :=
    congr_fun ((isCoveringMap_quotientAddGroup_mk' Λ).liftPath_lifts γ₀ (0 : V)
      (loop_zero_eq_mk' γ₀)) 1
  rw [γ₀.target] at h1
  rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h1

/-- The constant loop lifts to the constant path: endpoint `0`. -/
theorem pathLiftEnd_refl : pathLiftEnd Λ (Path.refl (0 : V ⧸ Λ)) = 0 :=
  pathLiftEnd_eq Λ _ (fun _ => 0) continuous_const rfl fun _ => (map_zero _)

/-- Translating the starting point of a lift by a lattice element translates
the whole lift. -/
theorem liftPath_add_mem (γ₀ : C(unitInterval, V ⧸ Λ)) (e b c : V) (hc : c ∈ Λ)
    (hb : b = e + c) (h0 : γ₀ 0 = QuotientAddGroup.mk' Λ e)
    (h0' : γ₀ 0 = QuotientAddGroup.mk' Λ b) (t : unitInterval) :
    (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ b h0' t
      = (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ e h0 t + c := by
  subst hb
  have key : (fun s => (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ e h0 s + c)
      = (isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ (e + c) h0' := by
    refine ((isCoveringMap_quotientAddGroup_mk' Λ).eq_liftPath_iff _).mpr
      ⟨((isCoveringMap_quotientAddGroup_mk' Λ).liftPath γ₀ e h0).continuous.add
        continuous_const, funext fun s => ?_, by
          rw [(isCoveringMap_quotientAddGroup_mk' Λ).liftPath_zero]⟩
    have hlift := congr_fun ((isCoveringMap_quotientAddGroup_mk' Λ).liftPath_lifts
      γ₀ e h0) s
    have hc0 : QuotientAddGroup.mk' Λ c = 0 := by
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hc
    simp only [Function.comp_apply] at hlift ⊢
    rw [map_add, hc0, add_zero, hlift]
  exact (congr_fun key t).symm

/-- **Concatenation adds lift endpoints.** -/
theorem pathLiftEnd_trans (γ₀ δ₀ : Path (0 : V ⧸ Λ) 0) :
    pathLiftEnd Λ (γ₀.trans δ₀) = pathLiftEnd Λ γ₀ + pathLiftEnd Λ δ₀ := by
  classical
  set cov := isCoveringMap_quotientAddGroup_mk' Λ with hcov
  have hpe : (0 : V ⧸ Λ) = QuotientAddGroup.mk' Λ (0 : V) := (map_zero _).symm
  -- the endpoint of the first lift
  set a : V := cov.liftPath γ₀ (0 : V) (γ₀.source.trans hpe) 1 with ha
  have hamem : a ∈ Λ := pathLiftEnd_mem Λ γ₀
  have hδmk : (δ₀ : C(unitInterval, V ⧸ Λ)) 0 = QuotientAddGroup.mk' Λ a := by
    have hl := congr_fun (cov.liftPath_lifts γ₀ (0 : V) (γ₀.source.trans hpe)) 1
    simp only [Function.comp_apply] at hl
    rw [ha, hl]
    exact δ₀.source.trans γ₀.target.symm
  -- evaluate the concatenated lift at `1`: it ends where the translated
  -- second lift ends
  have h1 : pathLiftEnd Λ (γ₀.trans δ₀) = cov.liftPath δ₀ a hδmk 1 :=
    (DFunLike.congr_fun (cov.liftPath_trans hpe γ₀ δ₀) 1).trans (Path.target _)
  -- translate the second lift back to base point `0`
  have h2 : cov.liftPath δ₀ a hδmk 1
      = cov.liftPath δ₀ (0 : V) (loop_zero_eq_mk' δ₀) 1 + a :=
    liftPath_add_mem Λ (δ₀ : C(unitInterval, V ⧸ Λ)) 0 a a hamem (zero_add a).symm
      (loop_zero_eq_mk' δ₀) hδmk 1
  rw [h1, h2, add_comm]
  rfl

/-- The lift endpoint on homotopy classes of loops, valued in `Λ`. Well
defined by the homotopy lifting property. -/
noncomputable def loopLiftEnd (γ : Path.Homotopic.Quotient (0 : V ⧸ Λ) 0) : Λ :=
  γ.lift (fun γ₀ => (⟨pathLiftEnd Λ γ₀, pathLiftEnd_mem Λ γ₀⟩ : Λ))
    fun γ₀ γ₁ hh => Subtype.ext
      ((isCoveringMap_quotientAddGroup_mk' Λ).liftPath_apply_one_eq_of_homotopicRel hh
        (0 : V) (loop_zero_eq_mk' γ₀) (loop_zero_eq_mk' γ₁))

@[simp] theorem loopLiftEnd_mk (γ₀ : Path (0 : V ⧸ Λ) 0) :
    loopLiftEnd Λ (Path.Homotopic.Quotient.mk γ₀)
      = ⟨pathLiftEnd Λ γ₀, pathLiftEnd_mem Λ γ₀⟩ :=
  rfl

/-- Concatenation of classes adds lift endpoints. -/
theorem loopLiftEnd_trans (γ δ : Path.Homotopic.Quotient (0 : V ⧸ Λ) 0) :
    loopLiftEnd Λ (γ.trans δ) = loopLiftEnd Λ γ + loopLiftEnd Λ δ := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ₀ =>
  induction δ using Path.Homotopic.Quotient.ind with | mk δ₀ =>
  rw [← Path.Homotopic.Quotient.mk_trans, loopLiftEnd_mk, loopLiftEnd_mk, loopLiftEnd_mk]
  exact Subtype.ext (pathLiftEnd_trans Λ γ₀ δ₀)

/-- **The endpoint homomorphism** `π₁(V ⧸ Λ, 0) →* Λ` (multiplicative form):
the class of a loop maps to the endpoint of its lift through the covering
`V → V ⧸ Λ`. -/
noncomputable def pi1ToLattice :
    FundamentalGroup (V ⧸ Λ) (0 : V ⧸ Λ) →* Multiplicative Λ where
  toFun g := Multiplicative.ofAdd (loopLiftEnd Λ (FundamentalGroup.toPath g))
  map_one' := by
    have h1 : FundamentalGroup.toPath (1 : FundamentalGroup (V ⧸ Λ) (0 : V ⧸ Λ))
        = Path.Homotopic.Quotient.mk (Path.refl (0 : V ⧸ Λ)) := rfl
    rw [h1, loopLiftEnd_mk]
    simp only [pathLiftEnd_refl]
    rfl
  map_mul' a b := by
    have hmul : FundamentalGroup.toPath (a * b)
        = (FundamentalGroup.toPath b).trans (FundamentalGroup.toPath a) := rfl
    simp only [hmul, loopLiftEnd_trans]
    rw [add_comm]
    rfl

@[simp] theorem pi1ToLattice_fromPath (γ₀ : Path (0 : V ⧸ Λ) 0) :
    pi1ToLattice Λ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))
      = Multiplicative.ofAdd (⟨pathLiftEnd Λ γ₀, pathLiftEnd_mem Λ γ₀⟩ : Λ) :=
  rfl

section Injective

variable [SimplyConnectedSpace V]

/-- A loop in `V ⧸ Λ` whose lift through the covering returns to `0` is
nullhomotopic: project a nullhomotopy of the lift (which exists because `V`
is simply connected). -/
theorem loopClass_eq_refl_of_pathLiftEnd_eq_zero (γ₀ : Path (0 : V ⧸ Λ) 0)
    (h0 : pathLiftEnd Λ γ₀ = 0) :
    Path.Homotopic.Quotient.mk γ₀
      = Path.Homotopic.Quotient.mk (Path.refl (0 : V ⧸ Λ)) := by
  set cov := isCoveringMap_quotientAddGroup_mk' Λ with hcov
  set Γ := cov.liftPath γ₀ (0 : V) (loop_zero_eq_mk' γ₀) with hΓ
  have hlift : (QuotientAddGroup.mk' Λ) ∘ Γ = γ₀ :=
    cov.liftPath_lifts γ₀ (0 : V) (loop_zero_eq_mk' γ₀)
  -- the lift is itself a loop at `0 : V`
  let Γp : Path (0 : V) 0 :=
    ⟨Γ, cov.liftPath_zero γ₀ (0 : V) (loop_zero_eq_mk' γ₀), h0⟩
  have hup : Γp.Homotopic (Path.refl (0 : V)) :=
    SimplyConnectedSpace.paths_homotopic Γp (Path.refl (0 : V))
  -- project down through the covering map
  set f : C(V, V ⧸ Λ) := ⟨QuotientAddGroup.mk' Λ, continuous_quotient_mk'⟩ with hf
  have hdown := hup.map f
  -- the projected lift IS `γ₀`, and the projected constant IS the constant
  -- (`mk' Λ 0` and `0 : V ⧸ Λ` are definitionally equal)
  have e1 : γ₀ = Γp.map f.continuous := by
    ext t
    exact (congr_fun hlift t).symm
  have e2 : Path.refl (0 : V ⧸ Λ) = (Path.refl (0 : V)).map f.continuous := by
    ext t
    exact (map_zero (QuotientAddGroup.mk' Λ)).symm
  rw [← e1, ← e2] at hdown
  exact Path.Homotopic.Quotient.eq.mpr hdown

/-- The endpoint homomorphism is injective when `V` is simply connected. -/
theorem pi1ToLattice_injective : Injective (pi1ToLattice Λ) := by
  rw [injective_iff_map_eq_one]
  have key : ∀ q : Path.Homotopic.Quotient (0 : V ⧸ Λ) 0,
      pi1ToLattice Λ (FundamentalGroup.fromPath q) = 1
        → FundamentalGroup.fromPath q = 1 := by
    intro q hq
    induction q using Path.Homotopic.Quotient.ind with | mk γ₀ =>
    rw [pi1ToLattice_fromPath] at hq
    have h0 : pathLiftEnd Λ γ₀ = 0 :=
      congr_arg Subtype.val (Multiplicative.ofAdd.injective hq)
    have hcl := loopClass_eq_refl_of_pathLiftEnd_eq_zero Λ γ₀ h0
    change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀) = 1
    rw [hcl]
    rfl
  intro g hg
  exact key (FundamentalGroup.toPath g) hg

end Injective

section Surjective

variable [Module ℝ V] [ContinuousSMul ℝ V]

/-- The straight-line loop in `V ⧸ Λ` associated to a lattice element: the
projection of `t ↦ t • c`. -/
noncomputable def latticeLoop (c : Λ) : Path (0 : V ⧸ Λ) 0 where
  toFun t := QuotientAddGroup.mk' Λ ((t : ℝ) • (c : V))
  continuous_toFun := by
    exact continuous_quotient_mk'.comp
      ((continuous_subtype_val.comp continuous_id).smul continuous_const)
  source' := by
    simp only [Set.Icc.coe_zero, zero_smul, map_zero]
  target' := by
    simp only [Set.Icc.coe_one, one_smul, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    exact c.2

/-- The straight-line loop lifts to the straight line: endpoint `c`. -/
theorem pathLiftEnd_latticeLoop (c : Λ) :
    pathLiftEnd Λ (latticeLoop Λ c) = (c : V) := by
  rw [pathLiftEnd_eq Λ (latticeLoop Λ c) (fun t => (t : ℝ) • (c : V))
    (((continuous_subtype_val.comp continuous_id).smul continuous_const))
    (by simp) (fun t => rfl)]
  simp

/-- The endpoint homomorphism is surjective when `V` is a real topological
vector space (so straight-line paths exist). -/
theorem pi1ToLattice_surjective : Surjective (pi1ToLattice Λ) := by
  intro c
  refine ⟨FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (latticeLoop Λ (Multiplicative.toAdd c))), ?_⟩
  rw [pi1ToLattice_fromPath]
  apply congr_arg Multiplicative.ofAdd
  exact Subtype.ext (pathLiftEnd_latticeLoop Λ (Multiplicative.toAdd c))

end Surjective

section Equiv

variable [SimplyConnectedSpace V] [Module ℝ V] [ContinuousSMul ℝ V]

/-- **`π₁(V ⧸ Λ, 0) ≅ Λ`** for a discrete subgroup `Λ` of a simply connected
real topological vector group `V`. -/
noncomputable def pi1EquivLattice :
    FundamentalGroup (V ⧸ Λ) (0 : V ⧸ Λ) ≃* Multiplicative Λ :=
  MulEquiv.ofBijective (pi1ToLattice Λ)
    ⟨pi1ToLattice_injective Λ, pi1ToLattice_surjective Λ⟩

/-- The endpoint homomorphism descended to first homology
`H₁(V ⧸ Λ) = π₁(V ⧸ Λ)ᵃᵇ`. -/
noncomputable def h1ToLattice : H1 (V ⧸ Λ) (0 : V ⧸ Λ) →+ Λ where
  toFun x := Multiplicative.toAdd (Abelianization.lift (pi1ToLattice Λ) x.toMul)
  map_zero' := by
    simp
  map_add' x y := by
    simp [map_mul]

/-- `h1ToLattice` on the Hurewicz image of a loop class is the lift
endpoint. -/
@[simp] theorem h1ToLattice_loopClass (γ₀ : Path (0 : V ⧸ Λ) 0) :
    h1ToLattice Λ (Additive.ofMul (Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))))
      = ⟨pathLiftEnd Λ γ₀, pathLiftEnd_mem Λ γ₀⟩ := by
  change Multiplicative.toAdd (Abelianization.lift (pi1ToLattice Λ)
    (Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀)))) = _
  rw [Abelianization.lift_apply_of, pi1ToLattice_fromPath]
  rfl

/-- The descended homomorphism is injective (`π₁` is already abelian here,
being isomorphic to `Λ`). -/
theorem h1ToLattice_injective : Injective (h1ToLattice Λ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientGroup.induction_on with | _ g =>
  -- `x = Additive.ofMul (Abelianization.of g)`
  have hg : Abelianization.lift (pi1ToLattice Λ) (Abelianization.of g) = 1 := by
    have : Multiplicative.toAdd (Abelianization.lift (pi1ToLattice Λ)
        (Abelianization.of g)) = 0 := hx
    exact Multiplicative.toAdd.injective this
  rw [Abelianization.lift_apply_of] at hg
  have : g = 1 := pi1ToLattice_injective Λ (by rw [hg, map_one])
  rw [this]
  rfl

/-- The descended homomorphism is surjective. -/
theorem h1ToLattice_surjective : Surjective (h1ToLattice Λ) := by
  intro c
  obtain ⟨g, hg⟩ := pi1ToLattice_surjective Λ (Multiplicative.ofAdd c)
  refine ⟨Additive.ofMul (Abelianization.of g), ?_⟩
  change Multiplicative.toAdd (Abelianization.lift (pi1ToLattice Λ)
    (Abelianization.of g)) = c
  rw [Abelianization.lift_apply_of, hg]
  rfl

/-- **`H₁(V ⧸ Λ, ℤ) ≅ Λ`**: the Hurewicz first homology of the quotient of a
simply connected real topological vector group by a discrete subgroup is the
subgroup itself, via lift endpoints. -/
noncomputable def h1EquivLattice : H1 (V ⧸ Λ) (0 : V ⧸ Λ) ≃+ Λ :=
  AddEquiv.ofBijective (h1ToLattice Λ)
    ⟨h1ToLattice_injective Λ, h1ToLattice_surjective Λ⟩

/-- Computation rule for `h1EquivLattice` on Hurewicz loop classes. -/
@[simp] theorem h1EquivLattice_loopClass (γ₀ : Path (0 : V ⧸ Λ) 0) :
    h1EquivLattice Λ (Additive.ofMul (Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ₀))))
      = ⟨pathLiftEnd Λ γ₀, pathLiftEnd_mem Λ γ₀⟩ :=
  h1ToLattice_loopClass Λ γ₀

end Equiv

end Jacobians.RiemannSurface
