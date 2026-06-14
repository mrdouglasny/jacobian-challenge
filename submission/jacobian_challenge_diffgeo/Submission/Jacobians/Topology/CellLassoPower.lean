/-
# G2 — loops in a once-punctured cell are lasso powers

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rung **G2**.

**Main result** (`fromPath_eq_cellLasso_zpow`): if `A ⊆ X` is a subset
homeomorphic to a once-punctured plane and the loop `δ` at `x₀ ∈ A` stays
inside `A`, then in `π₁(X, x₀)` the class of `δ` is an integer power of the
**cell lasso** — the image under the inclusion of the `φ`-pullback of the
explicit circle `circleAround` (the M1 generator).

This is the cell-computation input of the generation induction (G3): after
G1 splits a loop in `ℂ ∖ T` into single-cell factors, G2 rewrites each
factor lying in a once-punctured cell as a lasso power.  Assembly of
existing pieces: the M1 isomorphism `pi1PuncturedPlaneIntAt` with its
generator pin `pi1PuncturedPlaneIntAt_ofAdd_one`, homeomorphism invariance
`pi1MulEquivOfHomeomorph`, and `FundamentalGroup.mapOfEq` functoriality.
Mathlib-only imports.
-/
import Submission.Jacobians.Topology.PunctureLoops
import Submission.Jacobians.Topology.PuncturedSpherePi1

namespace Jacobians.Topology

open Set

local notation "Qmk" => Path.Homotopic.Quotient.mk

variable {X : Type*} [TopologicalSpace X]

/-- Corestriction of a path whose range lies in `A` to the subtype `↥A`. -/
def pathCorestrict {x y : X} {A : Set X} (p : Path x y) (hp : ∀ t, p t ∈ A)
    (hx : x ∈ A) (hy : y ∈ A) : Path (⟨x, hx⟩ : A) (⟨y, hy⟩ : A) where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- The subtype inclusion as a continuous map. -/
def inclusionCM (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Under the inclusion-induced homomorphism, the class of a corestricted
loop maps back to the class of the original loop. -/
theorem mapOfEq_inclusionCM_pathCorestrict {x₀ : X} {A : Set X} (hx₀ : x₀ ∈ A)
    (δ : Path x₀ x₀) (hδ : ∀ t, δ t ∈ A) :
    FundamentalGroup.mapOfEq (inclusionCM A) rfl
      (FundamentalGroup.fromPath (Qmk (pathCorestrict δ hδ hx₀ hx₀)))
      = FundamentalGroup.fromPath (Qmk δ) := by
  rw [FundamentalGroup.mapOfEq_apply]
  refine congrArg (fun r : Path x₀ x₀ => FundamentalGroup.fromPath (Qmk r)) ?_
  ext t
  rfl

/-- **The cell lasso**: for a cell `A ⊆ X` presented as a once-punctured
plane by `φ`, the class in `π₁(X, x₀)` of the `φ`-pullback of the explicit
circle around the puncture. -/
noncomputable def cellLasso {A : Set X} {a : ℂ}
    (φ : A ≃ₜ {w : ℂ // w ≠ a}) {x₀ : X} (hx₀ : x₀ ∈ A) :
    FundamentalGroup X x₀ :=
  FundamentalGroup.mapOfEq (inclusionCM A) rfl
    ((pi1MulEquivOfHomeomorph φ (⟨x₀, hx₀⟩ : A)).symm
      (FundamentalGroup.fromPath (Qmk (circleAround a (φ ⟨x₀, hx₀⟩)))))

/-- **G2 (cell computation).**  A loop staying inside a once-punctured cell
is, in `π₁` of the ambient space, an integer power of the cell lasso. -/
theorem fromPath_eq_cellLasso_zpow {A : Set X} {a : ℂ}
    (φ : A ≃ₜ {w : ℂ // w ≠ a}) {x₀ : X} (hx₀ : x₀ ∈ A)
    (δ : Path x₀ x₀) (hδ : ∀ t, δ t ∈ A) :
    ∃ n : ℤ, FundamentalGroup.fromPath (Qmk δ) = (cellLasso φ hx₀) ^ n := by
  classical
  set x₀' : A := (⟨x₀, hx₀⟩ : A) with hx₀'
  set e := pi1MulEquivOfHomeomorph φ x₀' with he
  set iso := pi1PuncturedPlaneIntAt a (φ x₀') with hiso
  set g : FundamentalGroup A x₀' :=
    FundamentalGroup.fromPath (Qmk (pathCorestrict δ hδ hx₀ hx₀)) with hg
  set n : ℤ := Multiplicative.toAdd (iso.symm (e g)) with hn
  refine ⟨n, ?_⟩
  -- in the punctured plane: `e g` is the `n`-th power of the M1 generator
  have hofAdd : Multiplicative.ofAdd n = Multiplicative.ofAdd (1 : ℤ) ^ n := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
  have h1 : e g = (iso (Multiplicative.ofAdd (1 : ℤ))) ^ n := by
    have : e g = iso (Multiplicative.ofAdd n) := by
      rw [hn, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [this, hofAdd, map_zpow]
  -- pull back through `e` and identify the generator with the circle
  have h2 : g = (e.symm (FundamentalGroup.fromPath
      (Qmk (circleAround a (φ x₀'))))) ^ n := by
    have := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at this
    rw [this, map_zpow, pi1PuncturedPlaneIntAt_ofAdd_one]
  -- push forward along the inclusion
  have h3 := congrArg (FundamentalGroup.mapOfEq (inclusionCM A)
    (rfl : (inclusionCM A) x₀' = x₀)) h2
  rw [map_zpow] at h3
  rw [← mapOfEq_inclusionCM_pathCorestrict hx₀ δ hδ]
  exact h3

/-- **The `n = 1` anchor of the generation induction** (route doc G3/G4
notes): the fundamental group of the once-punctured plane is generated —
plain closure, not just normal closure — by the explicit circle class. -/
theorem closure_circleAround_eq_top (a : ℂ) (z : {w : ℂ // w ≠ a}) :
    Subgroup.closure {FundamentalGroup.fromPath (Qmk (circleAround a z))}
      = (⊤ : Subgroup (FundamentalGroup {w : ℂ // w ≠ a} z)) := by
  rw [Subgroup.eq_top_iff']
  intro g
  set iso := pi1PuncturedPlaneIntAt a z with hiso
  have hg : g = (FundamentalGroup.fromPath (Qmk (circleAround a z)))
      ^ (Multiplicative.toAdd (iso.symm g)) := by
    rw [← pi1PuncturedPlaneIntAt_ofAdd_one, ← map_zpow]
    rw [show (Multiplicative.ofAdd (1 : ℤ)) ^ (Multiplicative.toAdd (iso.symm g))
        = Multiplicative.ofAdd (Multiplicative.toAdd (iso.symm g)) by
      rw [← ofAdd_zsmul, smul_eq_mul, mul_one]]
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rw [hg]
  refine Subgroup.zpow_mem _ ?_ _
  exact Subgroup.subset_closure (Set.mem_singleton _)

end Jacobians.Topology
