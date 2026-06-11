/-
# π₁ of the punctured sphere (M4): transport from the punctured plane

The Riemann sphere model used by the Dolbeault-port pipeline is
`OnePoint ℂ` (`KirovDolbeault/ToSphereGeneral.lean`). Removing `∞` together
with a finite set `T` of finite points leaves a space homeomorphic to the
multiply punctured plane `ℂ ∖ T` (`puncturedSphereHomeo`), so all π₁ results
of this directory transport:

* `pi1MulEquivOfHomeomorph` — fundamental groups are invariant under
  homeomorphism (generic, Mathlib-shaped);
* `pi1PuncturedSphere` — `π₁(ℂℙ¹ ∖ ({∞} ∪ T), φ x₀) ≃* π₁(ℂ ∖ T, x₀)`;
* `pi1SphereTwoPoints` — the sphere minus two points (`∞` and one finite
  point) has `π₁ ≃* Multiplicative ℤ`.

Winding homomorphisms and the δ-winding lasso family of `PunctureLoops.lean`
transport along `(pi1PuncturedSphere T x₀).symm` on the consumer side.

Mathlib-only mathematical content. Sorry-free and axiom-free
(beyond the three standard axioms).
-/
import Mathlib
import Jacobians.Topology.PunctureLoops

namespace Jacobians.Topology

open Complex OnePoint

/-! ## π₁ is a homeomorphism invariant -/

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem pi1_hominv_aux (φ : X ≃ₜ Y) (x : X)
    (q : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (⟨⇑φ.symm, φ.symm.continuous⟩ : C(Y, X)) (φ.symm_apply_apply x)
      (FundamentalGroup.mapOfEq (⟨⇑φ, φ.continuous⟩ : C(X, Y)) (rfl : φ x = φ x) q) = q := by
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath q)
  have hq : q = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := hp.symm
  rw [hq, FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  refine congrArg (fun r : Path x x ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk r)) ?_
  ext t
  exact φ.symm_apply_apply (p t)

/-- **Fundamental groups are invariant under homeomorphism.** -/
noncomputable def pi1MulEquivOfHomeomorph (φ : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (φ x) where
  toFun := FundamentalGroup.mapOfEq (⟨⇑φ, φ.continuous⟩ : C(X, Y)) rfl
  invFun := FundamentalGroup.mapOfEq (⟨⇑φ.symm, φ.symm.continuous⟩ : C(Y, X)) (φ.symm_apply_apply x)
  left_inv q := pi1_hominv_aux φ x q
  right_inv q := by
    have h1 := pi1_hominv_aux φ.symm (φ x) q
    -- transport: `φ.symm.symm = φ` and the basepoint identification
    obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath q)
    have hq : q = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := hp.symm
    rw [hq, FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    refine congrArg (fun r : Path (φ x) (φ x) ↦
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk r)) ?_
    ext t
    exact φ.apply_symm_apply (p t)
  map_mul' := map_mul _

end Homeomorph

/-! ## The punctured sphere is the punctured plane -/

/-- The plane minus a finite set is homeomorphic to the `OnePoint` sphere minus
`∞` and the (coerced) finite set. -/
noncomputable def puncturedSphereHomeo (T : Finset ℂ) :
    {z : ℂ // z ∉ (T : Set ℂ)}
      ≃ₜ {w : OnePoint ℂ // w ∉ insert (∞ : OnePoint ℂ) ((↑) '' (T : Set ℂ))} := by
  have hmem : ∀ z : {z : ℂ // z ∉ (T : Set ℂ)},
      ((z : ℂ) : OnePoint ℂ) ∉ insert (∞ : OnePoint ℂ) ((↑) '' (T : Set ℂ)) := by
    rintro z (h | ⟨w, hwT, hw⟩)
    · exact OnePoint.coe_ne_infty _ h
    · exact z.2 (OnePoint.coe_injective hw ▸ hwT)
  refine Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fun z ↦ ⟨((z : ℂ) : OnePoint ℂ), hmem z⟩) ⟨?_, ?_⟩) ?_ ?_
  · intro z z' hzz'
    exact Subtype.ext (OnePoint.coe_injective (congrArg Subtype.val hzz'))
  · rintro ⟨w, hw⟩
    have hwne : w ≠ ∞ := fun h ↦ hw (h ▸ Set.mem_insert _ _)
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hwne
    refine ⟨⟨y, fun hyT ↦ hw ?_⟩, Subtype.ext hy⟩
    exact Set.mem_insert_iff.mpr (Or.inr ⟨y, hyT, hy⟩)
  · exact (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _
  · -- open map: composite of two open embeddings, corestricted
    have hopen : IsOpenMap (fun z : {z : ℂ // z ∉ (T : Set ℂ)} ↦ ((z : ℂ) : OnePoint ℂ)) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap.comp
        ((T.finite_toSet.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal.isOpenMap)
    exact hopen.codRestrict hmem

/-- **M4: π₁ of the punctured sphere is π₁ of the punctured plane.** All winding
and lasso results transport along this isomorphism. -/
noncomputable def pi1PuncturedSphere (T : Finset ℂ) (x₀ : {z : ℂ // z ∉ (T : Set ℂ)}) :
    FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀
      ≃* FundamentalGroup
          {w : OnePoint ℂ // w ∉ insert (∞ : OnePoint ℂ) ((↑) '' (T : Set ℂ))}
          (puncturedSphereHomeo T x₀) :=
  pi1MulEquivOfHomeomorph (puncturedSphereHomeo T) x₀

/-- **The sphere minus two points has fundamental group ℤ.** -/
noncomputable def pi1SphereTwoPoints (a : ℂ) (x₀ : {z : ℂ // z ∉ (({a} : Finset ℂ) : Set ℂ)}) :
    Multiplicative ℤ
      ≃* FundamentalGroup
          {w : OnePoint ℂ // w ∉ insert (∞ : OnePoint ℂ) ((↑) '' (({a} : Finset ℂ) : Set ℂ))}
          (puncturedSphereHomeo {a} x₀) := by
  have hx : (x₀ : ℂ) ≠ a := by simpa using x₀.2
  have hsets : {z : ℂ | z ≠ a} = {z : ℂ | z ∉ (({a} : Finset ℂ) : Set ℂ)} := by
    ext z
    simp
  refine MulEquiv.trans (MulEquiv.trans (pi1PuncturedPlaneIntAt a ⟨(x₀ : ℂ), hx⟩) ?_)
    (pi1PuncturedSphere {a} x₀)
  exact pi1MulEquivOfHomeomorph (Homeomorph.setCongr hsets) ⟨(x₀ : ℂ), hx⟩

end Jacobians.Topology
