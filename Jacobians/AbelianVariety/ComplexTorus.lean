import Jacobians.AbelianVariety.Lattice

namespace Jacobians.AbelianVariety

open scoped Manifold Topology
open scoped ContDiff
open Set

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The complex torus `V ⧸ L.toAddSubgroup` where `L` is a full-rank ℤ-lattice in a
finite-dimensional ℂ-vector space `V`. -/
def ComplexTorus : Type _ := V ⧸ L.toAddSubgroup

namespace ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

instance instAddCommGroup : AddCommGroup (ComplexTorus V L) :=
  inferInstanceAs (AddCommGroup (V ⧸ L.toAddSubgroup))

instance instTopologicalSpace : TopologicalSpace (ComplexTorus V L) :=
  inferInstanceAs (TopologicalSpace (V ⧸ L.toAddSubgroup))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ComplexTorus V L) :=
  inferInstanceAs (IsTopologicalAddGroup (V ⧸ L.toAddSubgroup))

instance instT2Space : T2Space (ComplexTorus V L) := by
  letI : IsClosed (L.toAddSubgroup : Set V) :=
    AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  letI : T1Space (V ⧸ L.toAddSubgroup) :=
    inferInstance
  simpa [ComplexTorus] using (inferInstance : T2Space (V ⧸ L.toAddSubgroup))

instance instCompactSpace : CompactSpace (ComplexTorus V L) := by
  rw [← isCompact_univ_iff]
  simpa [ComplexTorus, Set.range_quotient_mk'] using
    (IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' L.toAddSubgroup)
      continuous_quotient_mk' (by
        intro z w hw
        exact Quotient.sound' <| by
          rw [QuotientAddGroup.leftRel_apply]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw))

/- TODO: Construct `ChartedSpace V (ComplexTorus V L)` from the covering map
`QuotientAddGroup.mk' L.toAddSubgroup : V → ComplexTorus V L`.

The likely route is:
1. Use `[DiscreteTopology L]` to obtain an open neighborhood `U` of `0` in `V` with
   `U ∩ (L : Set V) = {0}`.
2. For each lift `v : V`, show the quotient map restricts to an open embedding on `v + U`.
3. Use these local inverses to define charts centered at arbitrary points of `ComplexTorus V L`.
4. Prove chart transitions are translations by lattice vectors, hence smooth/holomorphic.

With that atlas in place, the `IsManifold 𝓘(ℂ, V) ω` and `LieAddGroup 𝓘(ℂ, V) ω` instances should
follow from the standard smoothness of affine translations on `V`. -/

end ComplexTorus

end Jacobians.AbelianVariety
