/-
# Subinterval-supported chart-local straight-line homotopy

The cell-by-cell upgrade of `ChartLocalHomotopy.lean`'s
`Path.homotopic_of_extChartLocal`: instead of requiring the *whole* of two paths
to live in one chart, we only require them to live in one chart **on a parameter
subinterval `[a, b]`** and to **agree outside `(a, b)`**. The resulting homotopy
is the straight-line chart homotopy inside `[a, b]` and stationary (`= f`)
outside, glued continuously across the boundary `{a, b}` (where `f = g`).

This is exactly the primitive needed to replace a loop **one subdivision cell at a
time** and chain the homotopies (`Path.homotopic_of_chain`): each step touches a
single cell, where both the original loop and the chart-flat replacement lie in one
chart, while leaving the rest of the loop untouched.

## Main results

* `Path.homotopyOfPartialEquivLocalOn` / `Path.homotopic_of_partialEquivLocalOn` —
  the model-agnostic primitive (homotopy and relation form).
* `Path.homotopic_of_extChartLocalOn` — the manifold specialisation to
  `extChartAt I p`, directly usable on a Riemann surface.

No new axiom; sorry-free; standard-3.
-/
import Jacobians.RiemannSurface.ChartLocalHomotopy

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open unitInterval
open Classical

section SubintervalSupported

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
variable {x₀ x₁ : X}

/-- Support cell of the subinterval homotopy: all `(s,t)` with `a ≤ t ≤ b`. -/
def homotopySupportCell (a b : ℝ) : Set (I × I) :=
  Set.univ ×ˢ {t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}

theorem isClosed_homotopySupportCell (a b : ℝ) : IsClosed (homotopySupportCell a b) := by
  apply IsClosed.prod isClosed_univ
  exact (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

/-- The "inner" straight-line homotopy formula (used inside the support cell). -/
noncomputable def innerH (f g : Path x₀ x₁) (e : PartialEquiv X E) (st : I × I) : X :=
  e.symm (AffineMap.lineMap (e (f st.2)) (e (g st.2)) (st.1 : ℝ))

theorem continuousOn_innerH (f g : Path x₀ x₁) (e : PartialEquiv X E) {a b : ℝ}
    (he : ContinuousOn e e.source) (he' : ContinuousOn e.symm e.target)
    (hf : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → f t ∈ e.source)
    (hg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → g t ∈ e.source)
    (hseg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b →
      segment ℝ (e (f t)) (e (g t)) ⊆ e.target) :
    ContinuousOn (innerH f g e) (homotopySupportCell a b) := by
  set S : Set (I × I) := homotopySupportCell a b with hS
  have hcf : ContinuousOn (fun st : I × I => e (f st.2)) S :=
    he.comp' (f.continuous.comp continuous_snd).continuousOn (fun st hst => hf st.2 hst.2)
  have hcg : ContinuousOn (fun st : I × I => e (g st.2)) S :=
    he.comp' (g.continuous.comp continuous_snd).continuousOn (fun st hst => hg st.2 hst.2)
  have hs : ContinuousOn (fun st : I × I => (st.1 : ℝ)) S :=
    (continuous_subtype_val.comp continuous_fst).continuousOn
  have hline : ContinuousOn (fun st : I × I =>
      AffineMap.lineMap (e (f st.2)) (e (g st.2)) (st.1 : ℝ)) S := by
    simp only [AffineMap.lineMap_apply_module]
    exact (((continuousOn_const.sub hs).smul hcf).add (hs.smul hcg))
  exact he'.comp' hline (fun st hst =>
    hseg st.2 hst.2 (lineMap_mem_segment (𝕜 := ℝ) (e (f st.2)) (e (g st.2)) st.1.2))

/-- Where the two paths agree (`f t = g t ∈ e.source`), the inner homotopy reduces
to `f t`. -/
theorem innerH_eq_of_agree (f g : Path x₀ x₁) (e : PartialEquiv X E) {st : I × I}
    (heq : f st.2 = g st.2) (hmem : f st.2 ∈ e.source) :
    innerH f g e st = f st.2 := by
  unfold innerH
  rw [heq, AffineMap.lineMap_same]
  simp only [AffineMap.coe_const, Function.const_apply]
  rw [← heq, e.left_inv hmem]

/-- **Subinterval-supported chart-local straight-line homotopy.** Two paths
`f g : Path x₀ x₁` that agree outside `(a, b)` and, on `[a, b]`, both lie in
`e.source` with connecting segments inside `e.target`, are homotopic rel endpoints,
via a homotopy that is the straight-line homotopy inside `[a, b]` and stationary
(`= f`) outside. -/
noncomputable def Path.homotopyOfPartialEquivLocalOn (f g : Path x₀ x₁)
    (e : PartialEquiv X E) (a b : ℝ)
    (he : ContinuousOn e e.source) (he' : ContinuousOn e.symm e.target)
    (hagree : ∀ t : I, (t : ℝ) ∉ Set.Ioo a b → f t = g t)
    (hf : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → f t ∈ e.source)
    (hg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → g t ∈ e.source)
    (hseg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b →
      segment ℝ (e (f t)) (e (g t)) ⊆ e.target) :
    f.Homotopy g where
  toFun := Set.piecewise (homotopySupportCell a b) (innerH f g e) (fun st => f st.2)
  continuous_toFun := by
    classical
    have hcl : closure (homotopySupportCell a b) = homotopySupportCell a b :=
      (isClosed_homotopySupportCell a b).closure_eq
    refine continuous_piecewise ?_ ?_ ?_
    · -- frontier agreement
      intro st hst
      have hfr : st ∈ homotopySupportCell a b :=
        (isClosed_homotopySupportCell a b).frontier_subset hst
      -- frontier of a closed set has empty interior; here st has t = a or t = b
      have hsub : frontier (homotopySupportCell a b) ⊆
          {st : I × I | (st.2 : ℝ) = a ∨ (st.2 : ℝ) = b} := by
        intro p hp
        have hpcell : p ∈ homotopySupportCell a b :=
          (isClosed_homotopySupportCell a b).frontier_subset hp
        by_contra hcon
        rw [Set.mem_setOf_eq, not_or] at hcon
        obtain ⟨hpa, hpb⟩ := hcon
        -- p.2 is in the open interior (a,b), so p is in interior of the cell ⇒ not frontier
        have hlt₁ : a < (p.2 : ℝ) := lt_of_le_of_ne hpcell.2.1 (Ne.symm hpa)
        have hlt₂ : (p.2 : ℝ) < b := lt_of_le_of_ne hpcell.2.2 hpb
        have hopen : IsOpen
            (Set.univ ×ˢ {t : I | a < (t : ℝ) ∧ (t : ℝ) < b} : Set (I × I)) := by
          apply IsOpen.prod isOpen_univ
          exact (isOpen_lt continuous_const continuous_subtype_val).inter
            (isOpen_lt continuous_subtype_val continuous_const)
        have hmemopen : p ∈ (Set.univ ×ˢ {t : I | a < (t : ℝ) ∧ (t : ℝ) < b}) :=
          ⟨Set.mem_univ _, hlt₁, hlt₂⟩
        have hsubcell : (Set.univ ×ˢ {t : I | a < (t : ℝ) ∧ (t : ℝ) < b})
            ⊆ homotopySupportCell a b := by
          intro q hq
          exact ⟨Set.mem_univ _, le_of_lt hq.2.1, le_of_lt hq.2.2⟩
        have hint : p ∈ interior (homotopySupportCell a b) :=
          interior_maximal hsubcell hopen hmemopen
        exact (mem_frontier_iff_notMem_interior hpcell).mp hp hint
      have hcase := hsub hst
      have hagree' : f st.2 = g st.2 := by
        apply hagree st.2
        rcases hcase with h | h
        · rw [Set.mem_Ioo]; rintro ⟨h1, _⟩; rw [h] at h1; exact lt_irrefl a h1
        · rw [Set.mem_Ioo]; rintro ⟨_, h2⟩; rw [h] at h2; exact lt_irrefl b h2
      have hmem : f st.2 ∈ e.source := hf st.2 ⟨hfr.2.1, hfr.2.2⟩
      exact innerH_eq_of_agree f g e hagree' hmem
    · rw [hcl]
      exact continuousOn_innerH f g e he he' hf hg hseg
    · exact (f.continuous.comp continuous_snd).continuousOn
  map_zero_left := by
    intro t
    simp only [Path.coe_toContinuousMap]
    by_cases ht : (t : ℝ) ∈ Set.Icc a b
    · have : ((0 : I), t) ∈ homotopySupportCell a b := ⟨Set.mem_univ _, ht.1, ht.2⟩
      rw [Set.piecewise_eq_of_mem _ _ _ this]
      unfold innerH
      rw [show ((0 : I) : ℝ) = 0 from rfl, AffineMap.lineMap_apply_zero]
      exact e.left_inv (hf t ht)
    · have hnotin : ((0 : I), t) ∉ homotopySupportCell a b := by
        simp only [homotopySupportCell, Set.mem_prod, Set.mem_setOf_eq, not_and]
        intro _
        rw [Set.mem_Icc, not_and_or] at ht
        tauto
      rw [Set.piecewise_eq_of_notMem _ _ _ hnotin]
  map_one_left := by
    intro t
    simp only [Path.coe_toContinuousMap]
    by_cases ht : (t : ℝ) ∈ Set.Icc a b
    · have : ((1 : I), t) ∈ homotopySupportCell a b := ⟨Set.mem_univ _, ht.1, ht.2⟩
      rw [Set.piecewise_eq_of_mem _ _ _ this]
      unfold innerH
      rw [show ((1 : I) : ℝ) = 1 from rfl, AffineMap.lineMap_apply_one]
      exact e.left_inv (hg t ht)
    · have hnotin : ((1 : I), t) ∉ homotopySupportCell a b := by
        simp only [homotopySupportCell, Set.mem_prod, Set.mem_setOf_eq, not_and]
        intro _
        rw [Set.mem_Icc, not_and_or] at ht
        tauto
      rw [Set.piecewise_eq_of_notMem _ _ _ hnotin]
      -- here f t = g t since t ∉ [a,b] ⊆ ... need t ∉ Ioo a b
      exact hagree t (fun hc => ht (Set.Ioo_subset_Icc_self hc))
  prop' := by
    intro s t ht
    have hft : f t = g t := by
      rcases ht with ht | ht
      · rw [ht]; simp
      · rw [Set.mem_singleton_iff] at ht; rw [ht]; simp
    simp only [Path.coe_toContinuousMap]
    change Set.piecewise (homotopySupportCell a b) (innerH f g e) (fun st => f st.2) (s, t) = f t
    by_cases htmem : (t : ℝ) ∈ Set.Icc a b
    · have : (s, t) ∈ homotopySupportCell a b := ⟨Set.mem_univ _, htmem.1, htmem.2⟩
      rw [Set.piecewise_eq_of_mem _ _ _ this]
      exact innerH_eq_of_agree f g e (st := (s, t)) hft (hf t htmem)
    · have hnotin : (s, t) ∉ homotopySupportCell a b := by
        simp only [homotopySupportCell, Set.mem_prod, Set.mem_setOf_eq, not_and]
        intro _
        rw [Set.mem_Icc, not_and_or] at htmem
        tauto
      rw [Set.piecewise_eq_of_notMem _ _ _ hnotin]

/-- Relation form of the subinterval-supported chart-local homotopy. -/
theorem Path.homotopic_of_partialEquivLocalOn (f g : Path x₀ x₁)
    (e : PartialEquiv X E) (a b : ℝ)
    (he : ContinuousOn e e.source) (he' : ContinuousOn e.symm e.target)
    (hagree : ∀ t : I, (t : ℝ) ∉ Set.Ioo a b → f t = g t)
    (hf : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → f t ∈ e.source)
    (hg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → g t ∈ e.source)
    (hseg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b →
      segment ℝ (e (f t)) (e (g t)) ⊆ e.target) :
    f.Homotopic g :=
  ⟨Path.homotopyOfPartialEquivLocalOn f g e a b he he' hagree hf hg hseg⟩

end SubintervalSupported

section ExtChartLocalOn

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [TopologicalSpace H] {IM : ModelWithCorners 𝕜 E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold IM 0 X]
variable {x₀ x₁ : X}

set_option linter.unusedSectionVars false in
/-- **Subinterval-supported chart-local homotopy via `extChartAt`.** Two paths
`f g : Path x₀ x₁` that agree outside `(a, b)` and, on `[a, b]`, both lie in
`(extChartAt IM p).source` with connecting segments inside `(extChartAt IM p).target`,
are homotopic rel endpoints. The manifold specialisation of
`Path.homotopic_of_partialEquivLocalOn` to `e := extChartAt IM p`. -/
theorem Path.homotopic_of_extChartLocalOn (f g : Path x₀ x₁) (p : X) (a b : ℝ)
    (hagree : ∀ t : I, (t : ℝ) ∉ Set.Ioo a b → f t = g t)
    (hf : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → f t ∈ (extChartAt IM p).source)
    (hg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b → g t ∈ (extChartAt IM p).source)
    (hseg : ∀ t : I, (t : ℝ) ∈ Set.Icc a b →
      segment ℝ (extChartAt IM p (f t)) (extChartAt IM p (g t)) ⊆ (extChartAt IM p).target) :
    f.Homotopic g :=
  Path.homotopic_of_partialEquivLocalOn f g (extChartAt IM p) a b
    (continuousOn_extChartAt p) (continuousOn_extChartAt_symm p) hagree hf hg hseg

end ExtChartLocalOn

end Jacobians.RiemannSurface
