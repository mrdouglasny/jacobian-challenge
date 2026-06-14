/-
# The H1-fields composite for the `AX_PeriodCycleBasis` flip (H1C lane)

Conditional assembly of the three H₁ fields of `AX_PeriodCycleBasis`
(`loops` / `isBasis` / `loops_to_basis`) from

* **K-LITE's named output** — `[DiscreteTopology (loopPeriodLattice x₀ b)]`
  (TR-DISC), which via the image route (`PeriodDiscreteness.lean`, #208)
  yields freeness and ℤ-rank `2g` of the period lattice; and
* **named topology residuals**, sharpened here to their minimal form.

No axiom is introduced and `AX_PeriodCycleBasis` appears in **no** closure
in this file: everything is stated over the axiom-free developing-value
period map `devValPeriodVec` (`Layer3/PeriodLatticeDiscrete.lean`) and the
axiom-free loop algebra of `HomologyGeneration.lean` (#198).

## The sharpened residual (KIROV_214_STUDY.md Q3(a), corrected)

The study's splitting observation used the surjection `H1 ↠ loopPeriodLattice`.
That surjection **does not exist unconditionally**: `devValPeriodVec` is
defined on all of `H1` (developing values along arbitrary continuous loop
classes), while the lattice is the ℤ-span of *analytic*-loop periods only.
The missing ingredient is

  **T-GEN** (`AnalyticLoopsGenerateH1`): the classes of piecewise-analytic
  loops ℤ-span `H1 X x₀`.

T-GEN is *necessary* for the axiom's H₁ fields (any basis tied to analytic
loops by `loops_to_basis` spans, so its members' loop classes generate),
and it is **not implied by T-FG** (`Group.FG (FundamentalGroup X x₀)`
supplies finitely many *continuous* generators; `loopSpan = 2ℤ × ℤ ⊂ ℤ²`
is consistent with T-FG + T-RANK + period-injectivity). By the #198
subgroup trick, under T-GEN every `H1` class is a *single* analytic-loop
class (`AnalyticLoopsGenerateH1.exists_loop`) — no smoothing needed
downstream.

With T-GEN in place the splitting goes through:

* `devValPeriodVecToLattice` — the period surjection `H1 ↠ Λ`
  (`surjective_devValPeriodVecToLattice`);
* `Λ` is free (Mathlib `ZLattice.module_free`, from K-LITE's
  discreteness + the axiom-free B-3 spanning), so the surjection **splits**:
  `exists_section_devValPeriodVecToLattice`, and
  `H1 ≅ ker(devValPeriodVec) ⊕ Λ`
  (`nonempty_ker_prod_lattice_equiv_h1`);
* the kernel dies under the topology lane's T-FG + T-RANK
  (`h1PeriodInjective_of_finrank_le`): `finrank H1 = finrank ker + 2g ≤ 2g`
  forces `ker = 0`. Torsion classes always have zero periods, so
  `ker = 0` genuinely contains H1-torsion-freeness — supplied here by
  `Module.Free ℤ (H1 X x₀)`, which is in any case *necessary* for the
  `isBasis` field to exist;
* `H1 ≃ₗ Λ`, the rank-2g lattice basis (#208 `exists_loopPeriodLattice_basis`)
  pulls back, and T-GEN + #198 realize each basis vector as one analytic
  loop: `exists_h1LoopBasis_of_periodInjective` /
  `exists_h1LoopBasis_of_topology`.

**Minimal residual for the three H₁ fields, given K-LITE:**
  `T-GEN + KER-0`, where KER-0 is period-injectivity
  (`∀ v, devValPeriodVec x₀ b v = 0 → v = 0`);
equivalently (and derivably from the splitting):
  `T-GEN + T-FG + Module.Free ℤ H1 + finrank ℤ H1 ≤ 2g`.
Each member of the second list is also necessary
(`analyticLoopsGenerateH1_of_h1LoopBasis`, `finrank_h1_of_h1LoopBasis`),
so this is exact, not just sufficient.

## What this does NOT supply: R1/R2

The axiom's `R1`/`R2` fields (Riemann bilinear relations over the bundled
loops' `arcPeriodVec`) are **not** produced by this composite, and the
K-route never needs them (KIROV_214_STUDY.md §2). Their only proof-level
consumers are `Layer3/Periods.lean` (`choicePeriodCycleBasis_r1`/`_r2`,
:141/:149), feeding `riemannBilinear_exists` and the Phase-C Siegel lattice
instances — the latter already have R2-free twins in
`Layer3/PeriodLatticeDiscrete.lean`. For the general flip, R1/R2 either
remain on the boundary-word path (`ArcBoundaryWordData`, #203) **for the
specific extracted loops**, or the K-MID restatement drops the fields.
`periodCycleBasis_nonempty_of_h1Fields_of_R1R2` records the final
composition shape with R1/R2 as explicit hypotheses.

Route doc: `docs/planning/H1_COMPOSITE_ROUTE.md`.
-/
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Submission.Jacobians.RiemannSurface.HomologyGeneration

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Axioms (loopToHomology arcPeriodVec conjArcPeriodVec)
open Jacobians.Layer3 (devValPeriodVec devValPeriodVec_loopToHomology Q)

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## T-GEN: the named topological-generation residual -/

/-- **Named residual T-GEN.** The homology classes of piecewise-analytic
loops ℤ-span `H1 X x₀`. Strictly stronger than T-FG (which supplies
*continuous* generators); exactly what the slit-sheet/lasso topology lane
produces, since its π₁ generators are concrete analytic loops. Necessary
for the H₁ fields of `AX_PeriodCycleBasis`
(`analyticLoopsGenerateH1_of_h1LoopBasis`). -/
def AnalyticLoopsGenerateH1 (x₀ : X) : Prop :=
  Submodule.span ℤ
    (Set.range (loopToHomology : AnalyticLoop X x₀ → H1 X x₀)) = ⊤

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Under T-GEN, every `H1` class is the class of a **single** analytic
loop — the #198 `AddSubgroup` trick applied to the whole of `H1`. -/
theorem AnalyticLoopsGenerateH1.exists_loop {x₀ : X}
    (hgen : AnalyticLoopsGenerateH1 x₀) (v : H1 X x₀) :
    ∃ γ : AnalyticLoop X x₀, loopToHomology γ = v :=
  exists_loop_of_mem_span (hgen.symm ▸ Submodule.mem_top)

/-! ## The period surjection `H1 ↠ Λ` under T-GEN -/

variable (x₀ : X) (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))

/-- Under T-GEN, every developing-value period vector lands in the
loop-period lattice. -/
theorem devValPeriodVec_mem_loopPeriodLattice
    (hgen : AnalyticLoopsGenerateH1 x₀) (v : H1 X x₀) :
    devValPeriodVec x₀ b v ∈ loopPeriodLattice x₀ b := by
  obtain ⟨γ, rfl⟩ := hgen.exists_loop v
  rw [devValPeriodVec_loopToHomology]
  exact loopPeriodVec_mem_loopPeriodLattice x₀ b γ

/-- Under T-GEN, the range of the developing-value period map is exactly
the loop-period lattice (the corrected form of the study's
`range φ = Λ` step). -/
theorem range_devValPeriodVec_eq_loopPeriodLattice
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    LinearMap.range (devValPeriodVec x₀ b) = loopPeriodLattice x₀ b := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact devValPeriodVec_mem_loopPeriodLattice x₀ b hgen v
  · rw [loopPeriodLattice]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, rfl⟩
    exact ⟨loopToHomology γ, devValPeriodVec_loopToHomology x₀ b γ⟩

/-- The period surjection `H1 ↠ loopPeriodLattice` (T-GEN-conditional
corestriction of `devValPeriodVec`). -/
def devValPeriodVecToLattice (hgen : AnalyticLoopsGenerateH1 x₀) :
    H1 X x₀ →ₗ[ℤ] loopPeriodLattice x₀ b :=
  LinearMap.codRestrict (loopPeriodLattice x₀ b) (devValPeriodVec x₀ b)
    (devValPeriodVec_mem_loopPeriodLattice x₀ b hgen)

@[simp]
theorem coe_devValPeriodVecToLattice (hgen : AnalyticLoopsGenerateH1 x₀)
    (v : H1 X x₀) :
    (devValPeriodVecToLattice x₀ b hgen v : Fin (genus X) → ℂ)
      = devValPeriodVec x₀ b v :=
  rfl

theorem surjective_devValPeriodVecToLattice
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    Function.Surjective (devValPeriodVecToLattice x₀ b hgen) := by
  rintro ⟨w, hw⟩
  rw [← range_devValPeriodVec_eq_loopPeriodLattice x₀ b hgen] at hw
  obtain ⟨v, hv⟩ := hw
  exact ⟨v, Subtype.ext hv⟩

theorem ker_devValPeriodVecToLattice (hgen : AnalyticLoopsGenerateH1 x₀) :
    LinearMap.ker (devValPeriodVecToLattice x₀ b hgen)
      = LinearMap.ker (devValPeriodVec x₀ b) :=
  LinearMap.ker_codRestrict _ _ _

/-! ## The splitting, conditional on K-LITE's output

`[DiscreteTopology (loopPeriodLattice x₀ b)]` is exactly the shape of
K-LITE's named output (TR-DISC). Freeness of the lattice is then Mathlib
(`ZLattice.module_free`, spanning side from axiom-free B-3), so the period
surjection splits and `H1 ≅ ker ⊕ Λ`. -/

variable [DiscreteTopology (loopPeriodLattice x₀ b)]

/-- **The splitting.** Under T-GEN and K-LITE's discreteness, the period
surjection `H1 ↠ Λ` admits a ℤ-linear section (`Λ` is free, hence
projective). -/
theorem exists_section_devValPeriodVecToLattice
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    ∃ s : loopPeriodLattice x₀ b →ₗ[ℤ] H1 X x₀,
      (devValPeriodVecToLattice x₀ b hgen).comp s = LinearMap.id := by
  haveI := isZLattice_loopPeriodLattice x₀ b
  haveI : Module.Free ℤ (loopPeriodLattice x₀ b) :=
    ZLattice.module_free ℝ (loopPeriodLattice x₀ b)
  exact Module.projective_lifting_property
    (devValPeriodVecToLattice x₀ b hgen) LinearMap.id
    (surjective_devValPeriodVecToLattice x₀ b hgen)

/-- **The split decomposition** `H1 ≅ ker(devValPeriodVec) ⊕ Λ` from the
section (right-split short exact sequence). -/
theorem nonempty_ker_prod_lattice_equiv_h1
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    Nonempty ((LinearMap.ker (devValPeriodVec x₀ b)
      × loopPeriodLattice x₀ b) ≃ₗ[ℤ] H1 X x₀) := by
  obtain ⟨s, hs⟩ := exists_section_devValPeriodVecToLattice x₀ b hgen
  exact ⟨lequivProdOfRightSplitExact
    (Submodule.injective_subtype (LinearMap.ker (devValPeriodVec x₀ b)))
    (by rw [Submodule.range_subtype, ker_devValPeriodVecToLattice]) hs⟩

/-! ## The collapse certificate: KER-0 ⟹ the three H₁-module residuals

`docs/planning/TOPOLOGY_FINISH_ROUTE.md` §3. Under T-GEN + K-LITE, KER-0
(period-injectivity) makes `φ̄ : H1 ↠ Λ` *injective*, hence an iso `H1 ≃ Λ`.
Since `Λ` is free, finitely generated, of `finrank = 2g` (K-LITE / ZLattice),
all three transfer to `H1`. This certifies that the four named residuals
{T-GEN, T-FG, Free, T-RANK≤} collapse to {T-GEN, KER-0}: the
`_of_topology` triple and the `_of_periodInjective` KER-0 are inter-derivable
given T-GEN + discreteness. -/

/-- Under T-GEN + K-LITE, KER-0 (period-injectivity) gives the period
surjection a two-sided inverse: `H1 X x₀ ≃ₗ[ℤ] loopPeriodLattice x₀ b`. -/
noncomputable def h1EquivLattice_of_periodInjective
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀, devValPeriodVec x₀ b v = 0 → v = 0) :
    H1 X x₀ ≃ₗ[ℤ] loopPeriodLattice x₀ b :=
  LinearEquiv.ofBijective (devValPeriodVecToLattice x₀ b hgen)
    ⟨by
        rw [← LinearMap.ker_eq_bot, ker_devValPeriodVecToLattice]
        exact LinearMap.ker_eq_bot'.mpr hker,
      surjective_devValPeriodVecToLattice x₀ b hgen⟩

/-- **The collapse certificate.** Under T-GEN + K-LITE's discreteness, KER-0
(period-injectivity) *outputs* all three H₁-module residuals — `H1 X x₀` is
`Module.Free ℤ`, `Module.Finite ℤ`, and has `finrank ℤ = 2g`. Together with
`h1PeriodInjective_of_finrank_le` (the converse), this shows the four named
residuals collapse to `{T-GEN, KER-0}`. -/
theorem h1Free_finite_rank_of_periodInjective
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀, devValPeriodVec x₀ b v = 0 → v = 0) :
    Module.Free ℤ (H1 X x₀) ∧ Module.Finite ℤ (H1 X x₀)
      ∧ Module.finrank ℤ (H1 X x₀) = 2 * genus X := by
  haveI := isZLattice_loopPeriodLattice x₀ b
  haveI hfree : Module.Free ℤ (loopPeriodLattice x₀ b) :=
    ZLattice.module_free ℝ (loopPeriodLattice x₀ b)
  haveI hfin : Module.Finite ℤ (loopPeriodLattice x₀ b) :=
    ZLattice.module_finite ℝ (loopPeriodLattice x₀ b)
  set e := h1EquivLattice_of_periodInjective x₀ b hgen hker with he
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, finrank_loopPeriodLattice x₀ b]

/-! ## KER-0 from the topology lane's residuals

The splitting converts the Hodge-flavoured period-injectivity into pure
rank bookkeeping: `finrank H1 = finrank ker + 2g`, so T-RANK's `≤` half
kills the kernel. This is where K-LITE's `2g` (the lattice rank, #208
image route) enters as the `≥` side. -/

/-- **KER-0 from T-FG + T-RANK (≤) + T-GEN + K-LITE.** Period-injectivity
on `H1`: a class with all developing-value periods zero is zero. The
`Module.Free` hypothesis carries the (necessary) torsion-freeness of `H1`;
the rank bound forces the free complement of the lattice to vanish. -/
theorem h1PeriodInjective_of_finrank_le
    (hgen : AnalyticLoopsGenerateH1 x₀)
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    ∀ v : H1 X x₀, devValPeriodVec x₀ b v = 0 → v = 0 := by
  classical
  obtain ⟨e⟩ := nonempty_ker_prod_lattice_equiv_h1 x₀ b hgen
  obtain ⟨n, bker⟩ := Submodule.basisOfPid
    (Module.Free.chooseBasis ℤ (H1 X x₀))
    (LinearMap.ker (devValPeriodVec x₀ b))
  obtain ⟨bΛ⟩ := exists_loopPeriodLattice_basis x₀ b
  have hfr : Module.finrank ℤ (H1 X x₀) = n + 2 * genus X := by
    rw [Module.finrank_eq_card_basis ((bker.prod bΛ).map e)]
    simp
  have hn : n = 0 := by omega
  subst hn
  intro v hv
  have hvk : (⟨v, LinearMap.mem_ker.mpr hv⟩ :
      LinearMap.ker (devValPeriodVec x₀ b)) = 0 := by
    have h0 : bker.repr ⟨v, LinearMap.mem_ker.mpr hv⟩ = 0 :=
      Finsupp.ext fun i => i.elim0
    exact (LinearEquiv.map_eq_zero_iff bker.repr).mp h0
  exact congrArg Subtype.val hvk

/-! ## The extraction: the three H₁ fields -/

/-- **The H1-fields composite (sharp residual form).** From K-LITE's
discreteness + T-GEN + KER-0: `2g` analytic loops whose classes form a
ℤ-basis of `H1 X x₀` — the `loops`/`isBasis`/`loops_to_basis` fields of
`AX_PeriodCycleBasis`. The basis is the pullback of the #208 lattice basis
along `H1 ≃ₗ Λ`; the loop representatives come from T-GEN + the #198
subgroup trick. -/
theorem exists_h1LoopBasis_of_periodInjective
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀, devValPeriodVec x₀ b v = 0 → v = 0) :
    ∃ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
      (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
      ∀ i, isB i = loopToHomology (loops i) := by
  classical
  have hinj : Function.Injective (devValPeriodVecToLattice x₀ b hgen) := by
    rw [← LinearMap.ker_eq_bot, ker_devValPeriodVecToLattice]
    exact LinearMap.ker_eq_bot'.mpr hker
  obtain ⟨bΛ⟩ := exists_loopPeriodLattice_basis x₀ b
  set e : H1 X x₀ ≃ₗ[ℤ] loopPeriodLattice x₀ b :=
    LinearEquiv.ofBijective (devValPeriodVecToLattice x₀ b hgen)
      ⟨hinj, surjective_devValPeriodVecToLattice x₀ b hgen⟩ with he
  set isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀) :=
    bΛ.map e.symm with hisB
  have hloop : ∀ i, ∃ γ : AnalyticLoop X x₀, loopToHomology γ = isB i :=
    fun i => hgen.exists_loop (isB i)
  choose loops hloops using hloop
  exact ⟨loops, isB, fun i => (hloops i).symm⟩

include b in
/-- **The H1-fields composite (topology-lane residual form)** — the flip's
final composition shape on the H₁ side:

  K-LITE (TR-DISC) + T-GEN + T-FG + `Module.Free ℤ H1` + T-RANK(≤)
    ⟹ `loops` / `isBasis` / `loops_to_basis`. -/
theorem exists_h1LoopBasis_of_topology
    (hgen : AnalyticLoopsGenerateH1 x₀)
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X) :
    ∃ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
      (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
      ∀ i, isB i = loopToHomology (loops i) :=
  exists_h1LoopBasis_of_periodInjective x₀ b hgen
    (h1PeriodInjective_of_finrank_le x₀ b hgen hrank)

/-! ## Minimality certificates: the residuals are necessary -/

variable {x₀}

/-- T-GEN is **necessary** for the H₁ fields: a loop-represented basis
spans, so analytic-loop classes generate `H1`. -/
theorem analyticLoopsGenerateH1_of_h1LoopBasis
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀))
    (htie : ∀ i, isB i = loopToHomology (loops i)) :
    AnalyticLoopsGenerateH1 x₀ := by
  rw [AnalyticLoopsGenerateH1, eq_top_iff, ← isB.span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨loops i, (htie i).symm⟩

/-- The rank count is **necessary**: the H₁ fields force
`finrank ℤ (H1 X x₀) = 2g` (freeness is `Module.Free.of_basis isB`). -/
theorem finrank_h1_of_h1LoopBasis
    (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)) :
    Module.finrank ℤ (H1 X x₀) = 2 * genus X := by
  rw [Module.finrank_eq_card_basis isB, Fintype.card_fin]

/-! ## The final flip shape -/

variable (x₀)

/-- **Bill-of-materials packaging.** The full `PeriodCycleBasis` bundle
from the three H₁ fields plus arc-level R1/R2 **for the same loops**.
The H₁ fields come from this file's composite; R1/R2 do NOT — they remain
on the boundary-word path (`ArcBoundaryWordData`, #203) for these specific
loops, or drop under the K-MID restatement
(see the file header and `docs/planning/H1_COMPOSITE_ROUTE.md`). -/
theorem periodCycleBasis_nonempty_of_h1Fields_of_R1R2
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀))
    (htie : ∀ i, isB i = loopToHomology (loops i))
    (hR1 : ∀ η ζ : HolomorphicOneForm X,
      Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0)
    (hR2 : ∀ η : HolomorphicOneForm X, η ≠ 0 →
      0 < (Complex.I * Q (arcPeriodVec loops η)
        (conjArcPeriodVec loops η)).re) :
    Nonempty (Jacobians.Axioms.PeriodCycleBasis X x₀) :=
  ⟨⟨loops, isB, htie, hR1, hR2⟩⟩

end

end Jacobians.RiemannSurface
