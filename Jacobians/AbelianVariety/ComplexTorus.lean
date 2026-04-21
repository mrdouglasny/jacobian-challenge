import Jacobians.AbelianVariety.Lattice

namespace Jacobians.AbelianVariety

open scoped Manifold Topology
open scoped ContDiff
open scoped Pointwise
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

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsZLattice ℝ L] in
private theorem exists_chartRadius :
    ∃ r > 0, ∀ {x y : V},
      x ∈ Metric.ball (0 : V) r →
      y ∈ Metric.ball (0 : V) r →
      x - y ∈ (L.toAddSubgroup : Set V) →
      x = y := by
  have hzeroOpen : IsOpen ({(0 : L)} : Set L) := by
    simp [(discreteTopology_iff_isOpen_singleton_zero (G := L)).mp
      (inferInstance : DiscreteTopology L)]
  rcases (isOpen_induced_iff.mp hzeroOpen) with ⟨W, hWopen, hWpre⟩
  have h0W : (0 : V) ∈ W := by
    have : (0 : L) ∈ ((↑) : L → V) ⁻¹' W := by
      simp [hWpre]
    simpa using this
  rcases Metric.mem_nhds_iff.mp (hWopen.mem_nhds h0W) with ⟨ε, hεpos, hεsub⟩
  refine ⟨ε / 2, half_pos hεpos, ?_⟩
  intro x y hx hy hxy
  have hxyW : x - y ∈ W := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hx' : ‖x‖ < ε / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hy' : ‖y‖ < ε / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hnorm : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    linarith
  have hzero : (⟨x - y, hxy⟩ : L) = 0 := by
    have : (⟨x - y, hxy⟩ : L) ∈ ({(0 : L)} : Set L) := by
      have hpre : (⟨x - y, hxy⟩ : L) ∈ ((↑) : L → V) ⁻¹' W := by
        simpa using hxyW
      simpa [hWpre] using hpre
    simpa using this
  exact sub_eq_zero.mp <| Subtype.ext_iff.mp hzero

private noncomputable def chartRadius : ℝ :=
  Classical.choose (exists_chartRadius (L := L))

private lemma chartRadius_pos : 0 < chartRadius (L := L) :=
  (Classical.choose_spec (exists_chartRadius (L := L))).1

private lemma chartRadius_inj {x y : V}
    (hx : x ∈ Metric.ball (0 : V) (chartRadius (L := L)))
    (hy : y ∈ Metric.ball (0 : V) (chartRadius (L := L)))
    (hxy : x - y ∈ (L.toAddSubgroup : Set V)) :
    x = y :=
  (Classical.choose_spec (exists_chartRadius (L := L))).2 hx hy hxy

private noncomputable def liftPoint (p : ComplexTorus V L) : V :=
  Classical.choose (QuotientAddGroup.mk'_surjective L.toAddSubgroup p)

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in
private lemma liftPoint_spec (p : ComplexTorus V L) :
    QuotientAddGroup.mk' L.toAddSubgroup (liftPoint (L := L) p) = p :=
  Classical.choose_spec (QuotientAddGroup.mk'_surjective L.toAddSubgroup p)

private noncomputable def chartTarget (p : ComplexTorus V L) : Set V :=
  (fun u : V => liftPoint (L := L) p + u) '' Metric.ball (0 : V) (chartRadius (L := L))

private lemma isOpen_chartTarget (p : ComplexTorus V L) : IsOpen (chartTarget (L := L) p) := by
  dsimp [chartTarget]
  exact (Homeomorph.addLeft (liftPoint (L := L) p)).isOpenMap
    (Metric.ball (0 : V) (chartRadius (L := L))) Metric.isOpen_ball

private lemma liftPoint_mem_chartTarget (p : ComplexTorus V L) :
    liftPoint (L := L) p ∈ chartTarget (L := L) p := by
  refine ⟨0, ?_, by simp [chartTarget]⟩
  simp [Metric.mem_ball, chartRadius_pos]

private lemma quotient_mk_injOn_chartTarget (p : ComplexTorus V L) :
    Set.InjOn (QuotientAddGroup.mk' L.toAddSubgroup) (chartTarget (L := L) p) := by
  intro x hx y hy hxy
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  have hvu : v - u ∈ (L.toAddSubgroup : Set V) := by
    have hvu' :
        -(liftPoint (L := L) p + u) + (liftPoint (L := L) p + v) ∈
          (L.toAddSubgroup : Set V) :=
      QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hxy)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hvu'
  have huv : u - v ∈ (L.toAddSubgroup : Set V) := by
    simpa [sub_eq_add_neg] using AddSubgroup.neg_mem L.toAddSubgroup hvu
  have hEq : u = v := chartRadius_inj (L := L) hu hv <| by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using huv
  simpa [hEq]

private noncomputable def quotientBranch (p : ComplexTorus V L) :
    OpenPartialHomeomorph V (ComplexTorus V L) :=
  OpenPartialHomeomorph.ofContinuousOpen
    (((quotient_mk_injOn_chartTarget (L := L) p).toPartialEquiv
      (QuotientAddGroup.mk' L.toAddSubgroup) (chartTarget (L := L) p)))
    continuous_quotient_mk'.continuousOn
    (by simpa using (QuotientAddGroup.isOpenMap_coe (N := L.toAddSubgroup)))
    (isOpen_chartTarget (L := L) p)

private lemma quotientBranch_apply (p : ComplexTorus V L) (x : V) :
    quotientBranch (L := L) p x = QuotientAddGroup.mk' L.toAddSubgroup x :=
  rfl

private lemma chart_apply_mk (p : ComplexTorus V L) {x : V}
    (hx : x ∈ chartTarget (L := L) p) :
    (quotientBranch (L := L) p).symm (QuotientAddGroup.mk' L.toAddSubgroup x) = x := by
  simpa [quotientBranch] using ((quotientBranch (L := L) p).symm.right_inv hx)

noncomputable instance : ChartedSpace V (ComplexTorus V L) where
  atlas := Set.range fun p => (quotientBranch (L := L) p).symm
  chartAt p := (quotientBranch (L := L) p).symm
  mem_chart_source p := by
    change p ∈ (QuotientAddGroup.mk' L.toAddSubgroup) '' chartTarget (L := L) p
    exact ⟨liftPoint (L := L) p, liftPoint_mem_chartTarget (L := L) p, liftPoint_spec (L := L) p⟩
  chart_mem_atlas p := ⟨p, rfl⟩

private lemma extChartAt_symm_eq_quotient_mk (p : ComplexTorus V L) {z : V}
    (hz : z ∈ chartTarget (L := L) p) :
    (extChartAt 𝓘(ℂ, V) p).symm z = QuotientAddGroup.mk' L.toAddSubgroup z := by
  have hx : QuotientAddGroup.mk' L.toAddSubgroup z ∈ (chartAt V p).source := by
    simpa [quotientBranch_apply] using (quotientBranch (L := L) p).map_source hz
  have hz' : z ∈ (chartAt V p).target := by
    simpa using hz
  exact ((chartAt V p).eq_symm_apply hx hz').2 (chart_apply_mk (L := L) p hz)

noncomputable instance : IsManifold 𝓘(ℂ, V) ω (ComplexTorus V L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  simpa [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv,
    PartialEquiv.trans_source, PartialEquiv.symm_source] using
    (show ContDiffOn ℂ ω
        ((quotientBranch (L := L) q).symm ∘ quotientBranch (L := L) p)
        ((quotientBranch (L := L) p).source ∩
          (quotientBranch (L := L) p) ⁻¹' ((quotientBranch (L := L) q).symm.source)) from by
      apply contDiffOn_of_locally_contDiffOn
      intro w hw
      let z : ComplexTorus V L := quotientBranch (L := L) p w
      let x : V := (quotientBranch (L := L) q).symm z
      let c : V := x - w
      refine ⟨chartTarget (L := L) p ∩
          (fun t : V => t + c) ⁻¹' chartTarget (L := L) q, ?_, ?_, ?_⟩
      · exact (isOpen_chartTarget (L := L) p).inter
          ((isOpen_chartTarget (L := L) q).preimage (Homeomorph.addRight c).continuous)
      · have hx : x ∈ chartTarget (L := L) q := by
          exact ((quotientBranch (L := L) q).symm.map_source hw.2)
        constructor
        · exact hw.1
        · simpa [c, x, z]
      · refine
          (show ContDiffOn ℂ ω (fun t : V => t + c)
              (((quotientBranch (L := L) p).source ∩
                (quotientBranch (L := L) p) ⁻¹' ((quotientBranch (L := L) q).symm.source)) ∩
                (chartTarget (L := L) p ∩
                  (fun t : V => t + c) ⁻¹' chartTarget (L := L) q)) from
            ((contDiff_id.add
              (contDiff_const : ContDiff ℂ ω (fun _ : V => c))).contDiffOn)
          ).congr ?_
        intro t ht
        have htc : t + c ∈ chartTarget (L := L) q := ht.2.2
        have hqx :
            QuotientAddGroup.mk' L.toAddSubgroup x = QuotientAddGroup.mk' L.toAddSubgroup w := by
          simpa [x, z, quotientBranch_apply (L := L) p w] using
            ((quotientBranch (L := L) q).symm.left_inv hw.2)
        have hc_mem : c ∈ (L.toAddSubgroup : Set V) := by
          have : -w + x ∈ (L.toAddSubgroup : Set V) :=
            QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hqx.symm)
          simpa [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
        have hqt :
            QuotientAddGroup.mk' L.toAddSubgroup (t + c) =
              QuotientAddGroup.mk' L.toAddSubgroup t := by
          have hnegc : -c ∈ (L.toAddSubgroup : Set V) :=
            AddSubgroup.neg_mem L.toAddSubgroup hc_mem
          apply Quotient.sound'
          rw [QuotientAddGroup.leftRel_apply]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnegc
        calc
          ((quotientBranch (L := L) q).symm ∘ quotientBranch (L := L) p) t
              = (quotientBranch (L := L) q).symm
                  (QuotientAddGroup.mk' L.toAddSubgroup (t + c)) := by
                    simp [Function.comp, quotientBranch_apply, hqt]
          _ = t + c := chart_apply_mk (L := L) q htc)

private lemma liftPoint_add_const_mem (p q : ComplexTorus V L) :
    liftPoint (L := L) (p + q) - (liftPoint (L := L) p + liftPoint (L := L) q) ∈
      (L.toAddSubgroup : Set V) := by
  have hq :
      QuotientAddGroup.mk' L.toAddSubgroup (liftPoint (L := L) (p + q)) =
        QuotientAddGroup.mk' L.toAddSubgroup (liftPoint (L := L) p + liftPoint (L := L) q) := by
    rw [liftPoint_spec (L := L), map_add, liftPoint_spec (L := L), liftPoint_spec (L := L)]
    rfl
  have :
      -(liftPoint (L := L) p + liftPoint (L := L) q) + liftPoint (L := L) (p + q) ∈
        (L.toAddSubgroup : Set V) :=
    QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hq.symm)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

private lemma liftPoint_neg_const_mem (p : ComplexTorus V L) :
    liftPoint (L := L) (-p) + liftPoint (L := L) p ∈ (L.toAddSubgroup : Set V) := by
  have hq :
      QuotientAddGroup.mk' L.toAddSubgroup (liftPoint (L := L) (-p)) =
        QuotientAddGroup.mk' L.toAddSubgroup (-liftPoint (L := L) p) := by
    rw [liftPoint_spec (L := L), map_neg, liftPoint_spec (L := L)]
    rfl
  have :
      -(-liftPoint (L := L) p) + liftPoint (L := L) (-p) ∈ (L.toAddSubgroup : Set V) :=
    QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hq.symm)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this


-- TODO (LieAddGroup): Codex had the addition/negation charts set up but the
-- simp/simpa rewrites for product-chart `extChartAt` and negation-chart `symm`
-- didn't fully reduce to the expected affine formulas. Needs dedicated
-- rewrite lemmas for the current atlas:
--   `extChartAt_symm_eq_quotient_mk` on chart targets
--   product version: `((chartAt V p).prod (chartAt V q)).symm`
-- Route: prove these first, then contMDiff_add / contMDiff_neg fall out.
noncomputable instance : LieAddGroup 𝓘(ℂ, V) ω (ComplexTorus V L) := by
  sorry

end ComplexTorus

end Jacobians.AbelianVariety
