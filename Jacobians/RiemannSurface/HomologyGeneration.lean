/-
# Homology generation by analytic loops (H-lane)

Reduces the named hypothesis `PeriodGeneratingLoops` (B-4 residual of the
Forster §21.4 ladder, `PeriodDiscreteness.lean`) to two purely topological
facts about `H1 X x₀`, with **no** `AX_PeriodCycleBasis` in any closure.

* **Loop algebra.** `AnalyticLoop.refl`/`trans`/`reverse` (the arc-level
  operations of `ArcAlgebra.lean` packaged at a fixed basepoint), and the
  Hurewicz-side homomorphism lemmas `loopToHomology_refl`/`_trans`/`_reverse`.
* **The loop-class subgroup.** `loopHomologyClasses x₀`: the classes of
  analytic loops form an `AddSubgroup` of `H1 X x₀`, so
  `span ℤ (range loopToHomology)` has carrier exactly
  `range loopToHomology` (`coe_loopHomologySpan`). Consequence: **any**
  ℤ-module generating set extracted from the span consists of analytic-loop
  classes — no smoothing/approximation of continuous representatives needed.
* **Noetherian extraction.** If `H1 X x₀` is a finitely generated ℤ-module,
  some finite family of analytic loops homology-generates every analytic
  loop's class (`exists_finite_generating_loops`).
* **The `2g` count.** If moreover `H1 X x₀` is free with
  `finrank ℤ (H1 X x₀) ≤ 2 * genus X`, the family can be taken indexed by
  `Fin (2 * genus X)` (`exists_generating_loops`): a submodule of a free
  f.g. module over the PID ℤ is free of rank ≤ finrank, its basis vectors
  are loop classes, and constant loops pad the count. Only `≤` is needed:
  the `≥` direction is the axiom-free B-3 ℝ-spanning.
* **Wiring.** `PeriodGeneratingLoops` and hence discreteness/ZLattice/basis
  of the Forster-model period lattice follow
  (`exists_periodGeneratingLoops`, `discreteTopology_loopPeriodLattice`).

The residual hypotheses are *named topology*, free of loops, integration,
and R1/R2:
  (T-FG)  `Module.Finite ℤ (H1 X x₀)` — π₁ of a compact manifold is
          finitely generated (not in Mathlib at pin);
  (T-RANK) `Module.Free ℤ (H1 X x₀)` and
          `finrank ℤ (H1 X x₀) ≤ 2 * genus X` — the first Betti number is
          at most twice the analytic genus (classification of surfaces or
          Hodge/Dolbeault comparison).

Why `n` generators do not suffice for discreteness: a f.g. subgroup of
`ℝ^N` with more than `N` generators can be dense (`ℤ + ℤ√2 ⊆ ℝ`), so the
B-4 engine genuinely needs the `2g` count — that is exactly where T-RANK
enters. See `docs/planning/H_LANE_PROGRESS.log`.
-/
import Jacobians.Layer3.PeriodLatticeDiscrete

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Axioms (loopToHomology loopToPath)

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Loop algebra at a fixed basepoint -/

namespace AnalyticLoop

variable {x₀ : X}

/-- The constant analytic loop at `x₀` (generalizes the `ProjectiveLine`
witness `constLoop`; analyticity is trivial for a constant map). -/
def refl (x₀ : X) : AnalyticLoop X x₀ where
  arc :=
    { extend := fun _ => x₀
      continuous' := continuous_const
      partition := {0, 1}
      partition_subset := by
        intro r hr
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl <;> simp
      zero_mem := by simp
      one_mem := by simp
      is_analytic_strong := by
        intro a _ b _ hab _
        refine ⟨{a, b}, by simp, by simp, ?_, ?_⟩
        · intro r hr
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl
          · exact ⟨le_rfl, le_of_lt hab⟩
          · exact ⟨le_of_lt hab, le_rfl⟩
        · intro s _ t _ _ _
          refine ⟨x₀, Set.univ, fun _ : ℝ => (extChartAt 𝓘(ℂ) x₀) x₀, ?_, ?_, ?_, ?_, ?_⟩
          · exact isOpen_univ
          · intro r _
            exact Set.mem_univ r
          · intro r _
            exact analyticAt_const
          · intro r _
            exact mem_extChartAt_source x₀
          · intro r _
            rfl }
  start_eq := rfl
  end_eq := rfl

/-- Concatenation of analytic loops at a common basepoint. -/
def trans (γ δ : AnalyticLoop X x₀) : AnalyticLoop X x₀ where
  arc := γ.arc.trans δ.arc (γ.end_eq.trans δ.start_eq.symm)
  start_eq := by rw [AnalyticArc.trans_extend_zero]; exact γ.start_eq
  end_eq := by rw [AnalyticArc.trans_extend_one]; exact δ.end_eq

/-- Reversal of an analytic loop. -/
def reverse (γ : AnalyticLoop X x₀) : AnalyticLoop X x₀ where
  arc := γ.arc.reverse
  start_eq := by rw [AnalyticArc.reverse_extend_zero]; exact γ.end_eq
  end_eq := by rw [AnalyticArc.reverse_extend_one]; exact γ.start_eq

end AnalyticLoop

/-! ## The underlying topological paths of the loop algebra -/

variable {x₀ : X}

theorem loopToPath_refl : loopToPath (AnalyticLoop.refl x₀) = Path.refl x₀ := by
  ext t
  rfl

theorem loopToPath_trans (γ δ : AnalyticLoop X x₀) :
    loopToPath (γ.trans δ) = (loopToPath γ).trans (loopToPath δ) := by
  ext t
  rw [Path.trans_apply]
  by_cases h : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos h]
    show (if (t : ℝ) ≤ (1 / 2 : ℝ) then γ.arc.extend (2 * (t : ℝ))
        else δ.arc.extend (2 * (t : ℝ) - 1)) = γ.arc.extend _
    rw [if_pos h]
  · rw [dif_neg h]
    show (if (t : ℝ) ≤ (1 / 2 : ℝ) then γ.arc.extend (2 * (t : ℝ))
        else δ.arc.extend (2 * (t : ℝ) - 1)) = δ.arc.extend _
    rw [if_neg h]

theorem loopToPath_reverse (γ : AnalyticLoop X x₀) :
    loopToPath γ.reverse = (loopToPath γ).symm := by
  ext t
  show γ.arc.extend (1 - (t : ℝ)) = (loopToPath γ) (unitInterval.symm t)
  rfl

/-! ## Hurewicz-side homomorphism lemmas -/

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
/-- `loopToHomology` of a path-homotopy class, as a raw function on classes. -/
private def pathClassToH1 (p : Path.Homotopic.Quotient x₀ x₀) : H1 X x₀ :=
  Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath p))

private theorem loopToHomology_eq_pathClassToH1 (γ : AnalyticLoop X x₀) :
    loopToHomology γ = pathClassToH1 (Path.Homotopic.Quotient.mk (loopToPath γ)) :=
  rfl

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
private theorem pathClassToH1_trans (p q : Path.Homotopic.Quotient x₀ x₀) :
    pathClassToH1 (p.trans q) = pathClassToH1 p + pathClassToH1 q := by
  have hcomp : p.trans q =
      (FundamentalGroup.fromPath q) * (FundamentalGroup.fromPath p) := by
    rw [← FundamentalGroupoid.comp_eq (FundamentalGroupoid.mk x₀)
      (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₀) p q]
    rfl
  unfold pathClassToH1
  rw [show FundamentalGroup.fromPath (p.trans q) =
      FundamentalGroup.fromPath q * FundamentalGroup.fromPath p from hcomp,
    map_mul, ofMul_mul]
  exact add_comm (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath q)))
    (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath p)))

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
private theorem pathClassToH1_refl :
    pathClassToH1 (Path.Homotopic.Quotient.mk (Path.refl x₀)) = (0 : H1 X x₀) := by
  have h1 : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Path.refl x₀)) = (1 : FundamentalGroup X x₀) :=
    (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk x₀)).symm
  unfold pathClassToH1
  rw [h1, map_one]
  rfl

/-- The homology class of the constant loop vanishes. -/
@[simp]
theorem loopToHomology_refl : loopToHomology (AnalyticLoop.refl x₀) = 0 := by
  rw [loopToHomology_eq_pathClassToH1, loopToPath_refl, pathClassToH1_refl]

/-- `loopToHomology` is additive over loop concatenation (Hurewicz). -/
theorem loopToHomology_trans (γ δ : AnalyticLoop X x₀) :
    loopToHomology (γ.trans δ) = loopToHomology γ + loopToHomology δ := by
  rw [loopToHomology_eq_pathClassToH1, loopToPath_trans,
    Path.Homotopic.Quotient.mk_trans, pathClassToH1_trans]
  rfl

/-- `loopToHomology` negates under loop reversal (Hurewicz). -/
theorem loopToHomology_reverse (γ : AnalyticLoop X x₀) :
    loopToHomology γ.reverse = -loopToHomology γ := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← loopToHomology_trans]
  have hpath : loopToPath (γ.reverse.trans γ) =
      (loopToPath γ).symm.trans (loopToPath γ) := by
    rw [loopToPath_trans, loopToPath_reverse]
  have hclass : Path.Homotopic.Quotient.mk ((loopToPath γ).symm.trans (loopToPath γ))
      = Path.Homotopic.Quotient.mk (Path.refl x₀) :=
    Quotient.sound ⟨(Path.Homotopy.reflSymmTrans (loopToPath γ)).symm⟩
  rw [loopToHomology_eq_pathClassToH1, hpath, hclass, pathClassToH1_refl]

/-! ## The subgroup of analytic-loop classes

The Hurewicz lemmas make `Set.range loopToHomology` an additive subgroup, so
its ℤ-span adds nothing: every element of the span IS an analytic-loop class.
This kills the smoothing subproblem — generators extracted from the span by
abstract module theory are automatically represented by analytic loops. -/

/-- The homology classes of analytic loops based at `x₀`, as an additive
subgroup of `H1 X x₀`. -/
def loopHomologyClasses (x₀ : X) : AddSubgroup (H1 X x₀) where
  carrier := Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)
  add_mem' := by
    rintro _ _ ⟨γ, rfl⟩ ⟨δ, rfl⟩
    exact ⟨γ.trans δ, loopToHomology_trans γ δ⟩
  zero_mem' := ⟨AnalyticLoop.refl x₀, loopToHomology_refl⟩
  neg_mem' := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨γ.reverse, loopToHomology_reverse γ⟩

/-- The ℤ-span of the analytic-loop classes is exactly the set of
analytic-loop classes. -/
theorem coe_span_range_loopToHomology (x₀ : X) :
    (Submodule.span ℤ
        (Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)) :
      Set (H1 X x₀)) = Set.range loopToHomology := by
  refine subset_antisymm ?_ Submodule.subset_span
  exact Submodule.span_le.mpr
    (fun w hw => (hw : w ∈ AddSubgroup.toIntSubmodule (loopHomologyClasses x₀)))

/-- Membership form: an element of the ℤ-span of all loop classes is itself
a loop class. -/
theorem exists_loop_of_mem_span {x₀ : X} {v : H1 X x₀}
    (hv : v ∈ Submodule.span ℤ
      (Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀))) :
    ∃ γ : AnalyticLoop X x₀, loopToHomology γ = v := by
  rwa [← SetLike.mem_coe, coe_span_range_loopToHomology] at hv

/-! ## Noetherian extraction: finitely many generating loops -/

/-- **Topological residual T-FG payoff.** If `H1 X x₀` is a finitely
generated ℤ-module, then finitely many analytic loops homology-generate
every analytic loop's class. Pure module theory: the span of all loop
classes is f.g. (ℤ Noetherian), and its generators are loop classes by
`exists_loop_of_mem_span`. -/
theorem exists_finite_generating_loops (x₀ : X)
    [Module.Finite ℤ (H1 X x₀)] :
    ∃ (n : ℕ) (γs : Fin n → AnalyticLoop X x₀),
      ∀ δ : AnalyticLoop X x₀, loopToHomology δ ∈
        Submodule.span ℤ (Set.range fun i => loopToHomology (γs i)) := by
  classical
  haveI : IsNoetherian ℤ (H1 X x₀) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ (H1 X x₀)
  set A := Submodule.span ℤ
    (Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)) with hA
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian A
  have hsub : ∀ s : S, ∃ γ : AnalyticLoop X x₀, loopToHomology γ = (s : H1 X x₀) := by
    intro s
    refine exists_loop_of_mem_span (v := (s : H1 X x₀)) ?_
    rw [← hS]
    exact Submodule.subset_span s.2
  choose f hf using hsub
  refine ⟨S.card, fun i => f (S.equivFin.symm i), fun δ => ?_⟩
  have hrange : (Set.range fun i => loopToHomology (f (S.equivFin.symm i)))
      = (S : Set (H1 X x₀)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      show loopToHomology (f (S.equivFin.symm i)) ∈ (S : Set (H1 X x₀))
      rw [hf]
      exact (S.equivFin.symm i).2
    · intro hv
      refine ⟨S.equivFin ⟨v, hv⟩, ?_⟩
      show loopToHomology (f (S.equivFin.symm (S.equivFin ⟨v, hv⟩))) = v
      rw [Equiv.symm_apply_apply, hf]
  rw [hrange, hS]
  exact Submodule.subset_span ⟨δ, rfl⟩

/-! ## The `2g` count -/

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- **Topological residuals T-FG + T-RANK payoff.** If `H1 X x₀` is free
and finitely generated of rank at most `2 * genus X`, then `2g` analytic
loops homology-generate every analytic loop's class: the span of all loop
classes is a submodule of a free f.g. module over the PID ℤ, hence free
with a basis of ≤ `2g` vectors; each basis vector is itself a loop class;
constant loops pad the count to exactly `2g`. -/
theorem exists_generating_loops (x₀ : X)
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    ∃ γs : Fin (2 * genus X) → AnalyticLoop X x₀,
      ∀ δ : AnalyticLoop X x₀, loopToHomology δ ∈
        Submodule.span ℤ (Set.range fun i => loopToHomology (γs i)) := by
  classical
  set A := Submodule.span ℤ
    (Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)) with hA
  obtain ⟨m, bA⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ (H1 X x₀)) A
  have hli : LinearIndependent ℤ (fun j => (bA j : H1 X x₀)) :=
    bA.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hm : m ≤ Module.finrank ℤ (H1 X x₀) := by
    simpa using hli.fintype_card_le_finrank
  have hcard : m ≤ 2 * genus X := hm.trans hrank
  have hmem : ∀ j : Fin m, ∃ γ : AnalyticLoop X x₀,
      loopToHomology γ = (bA j : H1 X x₀) :=
    fun j => exists_loop_of_mem_span (bA j).2
  choose f hf using hmem
  set γs : Fin (2 * genus X) → AnalyticLoop X x₀ :=
    fun i => if h : (i : ℕ) < m then f ⟨i, h⟩ else AnalyticLoop.refl x₀ with hγs
  have hAspan : Submodule.span ℤ (Set.range fun j => (bA j : H1 X x₀)) = A := by
    have h1 := congrArg (Submodule.map A.subtype) bA.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      Submodule.range_subtype] at h1
  have hAle : A ≤ Submodule.span ℤ (Set.range fun i => loopToHomology (γs i)) := by
    rw [← hAspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j, lt_of_lt_of_le j.isLt hcard⟩, ?_⟩
    have hj : ((⟨(j : ℕ), lt_of_lt_of_le j.isLt hcard⟩ : Fin (2 * genus X)) : ℕ) < m :=
      j.isLt
    rw [hγs]
    simp only [hj, dif_pos, Fin.eta]
    exact hf j
  exact ⟨γs, fun δ => hAle (Submodule.subset_span ⟨δ, rfl⟩)⟩

/-! ## Wiring into the B-4/B-5 engine (axiom-free) -/

/-- **The named hypothesis from topology alone.** Under T-FG and T-RANK,
`2g` analytic loops period-generate: `PeriodGeneratingLoops` holds for
some family, with no `AX_PeriodCycleBasis` in the closure. -/
theorem exists_periodGeneratingLoops (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    ∃ γs : Fin (2 * genus X) → AnalyticLoop X x₀,
      PeriodGeneratingLoops x₀ b γs := by
  obtain ⟨γs, hγs⟩ := exists_generating_loops x₀ hrank
  exact ⟨γs, Jacobians.Layer3.PeriodGeneratingLoops.of_homology_span hγs⟩

/-- **B-4 discreteness from topology alone.** The Forster-model period
lattice is discrete, given only the two named topological facts about
`H1 X x₀` — no chosen cycle basis, no R1/R2, no axiom. -/
theorem discreteTopology_loopPeriodLattice_of_H1 (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    DiscreteTopology (loopPeriodLattice x₀ b) := by
  obtain ⟨γs, hγs⟩ := exists_periodGeneratingLoops x₀ b hrank
  exact hγs.discreteTopology

/-- **B-5 packaging from topology alone**: a `Fin (2g)`-indexed ℤ-basis of
the Forster-model period lattice under T-FG and T-RANK. -/
theorem exists_loopPeriodLattice_basis_of_H1 (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ (loopPeriodLattice x₀ b)) := by
  obtain ⟨γs, hγs⟩ := exists_periodGeneratingLoops x₀ b hrank
  exact hγs.exists_basis

end

end Jacobians.RiemannSurface
