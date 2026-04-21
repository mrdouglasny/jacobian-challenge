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

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsZLattice ℝ L] in
private theorem lattice_isDiscrete :
    IsDiscrete (L.toAddSubgroup : Set V) := by
  rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsZLattice ℝ L] in
private noncomputable def quotientMapIsLocalHomeomorph :
    IsLocalHomeomorph (QuotientAddGroup.mk' L.toAddSubgroup : V → ComplexTorus V L) := by
  let hq : IsAddQuotientCoveringMap (QuotientAddGroup.mk' L.toAddSubgroup) L.toAddSubgroup :=
    AddSubgroup.isAddQuotientCoveringMap_of_comm L.toAddSubgroup lattice_isDiscrete
  exact hq.isCoveringMap.isLocalHomeomorph

private noncomputable def liftPoint (p : ComplexTorus V L) : V :=
  Classical.choose (QuotientAddGroup.mk'_surjective L.toAddSubgroup p)

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in
private lemma liftPoint_spec (p : ComplexTorus V L) :
    QuotientAddGroup.mk' L.toAddSubgroup (liftPoint (L := L) p) = p :=
  Classical.choose_spec (QuotientAddGroup.mk'_surjective L.toAddSubgroup p)

private noncomputable def quotientBranch (p : ComplexTorus V L) :
    OpenPartialHomeomorph V (ComplexTorus V L) :=
  Classical.choose (quotientMapIsLocalHomeomorph (L := L) (liftPoint (L := L) p))

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsZLattice ℝ L] in
private lemma mem_quotientBranch_source (p : ComplexTorus V L) :
    liftPoint (L := L) p ∈ (quotientBranch (L := L) p).source :=
  (Classical.choose_spec (quotientMapIsLocalHomeomorph (L := L) (liftPoint (L := L) p))).1

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsZLattice ℝ L] in
private lemma quotientBranch_eq (p : ComplexTorus V L) :
    ((quotientBranch (L := L) p : OpenPartialHomeomorph V (ComplexTorus V L)) : V →
      ComplexTorus V L) = QuotientAddGroup.mk' L.toAddSubgroup :=
  (Classical.choose_spec (quotientMapIsLocalHomeomorph (L := L) (liftPoint (L := L) p))).2.symm

noncomputable instance : ChartedSpace V (ComplexTorus V L) where
  atlas := Set.range fun p => (quotientBranch (L := L) p).symm
  chartAt p := (quotientBranch (L := L) p).symm
  mem_chart_source p := by
    have hp : quotientBranch (L := L) p (liftPoint (L := L) p) = p := by
      rw [quotientBranch_eq (L := L) p]
      exact liftPoint_spec (L := L) p
    simpa [hp] using
      (quotientBranch (L := L) p).map_source (mem_quotientBranch_source (L := L) p)
  chart_mem_atlas p := ⟨p, rfl⟩

noncomputable instance : IsManifold 𝓘(ℂ, V) ω (ComplexTorus V L) := by
  -- TODO: To use `isManifold_of_contDiffOn`, we still need an explicit overlap formula for the
  -- charts built from `quotientMapIsLocalHomeomorph`: on each nonempty overlap, prove
  -- `(chartAt V p).symm ≫ₕ chartAt V q` agrees with translation by a specific lattice vector.
  -- The present blocker is that `IsLocalHomeomorph` only gives existential local branches, and we
  -- have not yet proved the lemma identifying two chosen branches on an overlap by a translation.
  sorry

noncomputable instance : LieAddGroup 𝓘(ℂ, V) ω (ComplexTorus V L) := by
  -- TODO: After the `IsManifold` instance is upgraded from the existential atlas above to charts
  -- with explicit translation transition maps, addition and negation should be shown smooth by
  -- rewriting them locally to the corresponding affine maps on `V`. Right now this is blocked on
  -- the missing overlap/translation lemma used in the preceding `IsManifold` TODO.
  sorry

end ComplexTorus

end Jacobians.AbelianVariety
