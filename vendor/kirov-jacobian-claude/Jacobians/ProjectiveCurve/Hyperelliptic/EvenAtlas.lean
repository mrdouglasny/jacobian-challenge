/-
# HyperellipticEven atlas — entry point (Phase EA2)

Assembles the affine atlas (from `OddAtlas/AffineChart.lean`, valid for
`HyperellipticAffine H` for any `H`) and the affine-infinity atlas (from
`EvenAtlas/InfinityAffineChart.lean`, the EA1 transfer via `reverseData`)
into:

* `instance : ChartedSpace ℂ (HyperellipticEvenProj H)`
* `instance : IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticEvenProj H)`

(Recall `HyperellipticEven H h ≡ HyperellipticEvenProj H` for
`h : ¬ Odd H.f.natDegree`.)

## Lifting strategy

The plan doc proposed a generic `lift_openQuotientMap` lemma, but a
*much simpler* path works: the composition `q ∘ Sum.inl` (where `q` is
the quotient map and `Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H`)
is itself an **open embedding**, because:

* `Sum.inl` is an open embedding (`Topology.IsOpenEmbedding.inl`).
* `q` is an open quotient map (`hyperellipticEven_isOpenQuotientMap`,
  Even.lean:1016) — in particular continuous and an open map.
* Their composition is therefore continuous and an open map.
* Injectivity of `q ∘ Sum.inl` follows from
  `hyperellipticEvenSetoid_rel_iff` (Even.lean:671): the equivalence
  relation is `p = q ∨ Glue p q ∨ Glue q p`, and `Glue` is `False` on
  any pair of `Sum.inl` arguments, so two `Sum.inl` points are
  identified iff they are equal.

By `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`, this
makes `q ∘ Sum.inl` an open embedding. Then we apply Mathlib's
existing `OpenPartialHomeomorph.lift_openEmbedding` — the same machinery
Codex used for the OnePoint case in `OddAtlas`. Same story for
`Sum.inr`.

This means **no custom `lift_openQuotientMap` lemma is needed** — the
existing Mathlib API suffices once the right open-embedding facts are
established. EA2 reduces to ~150–200 LOC instead of the planned
230–400.

See `docs/hyperelliptic-even-atlas-plan.md` §EA2 (the design doc still
recommends the generic lemma; this file's reduction supersedes it).
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas.InfinityAffineChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace Jacobians.ProjectiveCurve.HyperellipticEvenProj

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData} {h : ¬ Odd H.f.natDegree}

/-- The quotient projection `HyperellipticEvenPre H → HyperellipticEvenProj H`. -/
def proj (H : HyperellipticData) : HyperellipticEvenPre H → HyperellipticEvenProj H :=
  fun x => Quotient.mk (hyperellipticEvenSetoid H) x

/-- The composition `proj ∘ Sum.inl` is injective: two affine points map to the
same quotient class iff they are equal. -/
theorem proj_inl_injective (H : HyperellipticData) :
    Function.Injective (proj H ∘ (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)) := by
  intro a₁ a₂ heq
  have hrel : (hyperellipticEvenSetoid H).r (Sum.inl a₁) (Sum.inl a₂) :=
    Quotient.exact heq
  rw [hyperellipticEvenSetoid_rel_iff] at hrel
  rcases hrel with hEq | hglue | hglue
  · exact Sum.inl_injective hEq
  · exact absurd hglue (by simp [HyperellipticEvenGlue])
  · exact absurd hglue (by simp [HyperellipticEvenGlue])

/-- The composition `proj ∘ Sum.inr` is injective: two affine-infinity points
map to the same quotient class iff they are equal. -/
theorem proj_inr_injective (H : HyperellipticData) :
    Function.Injective (proj H ∘
      (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) := by
  intro b₁ b₂ heq
  have hrel : (hyperellipticEvenSetoid H).r (Sum.inr b₁) (Sum.inr b₂) :=
    Quotient.exact heq
  rw [hyperellipticEvenSetoid_rel_iff] at hrel
  rcases hrel with hEq | hglue | hglue
  · exact Sum.inr_injective hEq
  · exact absurd hglue (by simp [HyperellipticEvenGlue])
  · exact absurd hglue (by simp [HyperellipticEvenGlue])

/-- `proj ∘ Sum.inl` is an open embedding from the affine chart into the
even-projective curve. -/
theorem isOpenEmbedding_proj_inl (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Topology.IsOpenEmbedding
      (proj H ∘ (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)) := by
  have hq : IsOpenQuotientMap (proj H) := hyperellipticEven_isOpenQuotientMap H h
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_
    (proj_inl_injective H) ?_
  · exact hq.continuous.comp continuous_inl
  · exact hq.isOpenMap.comp Topology.IsOpenEmbedding.inl.isOpenMap

/-- `proj ∘ Sum.inr` is an open embedding from the affine-infinity chart into
the even-projective curve. -/
theorem isOpenEmbedding_proj_inr (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Topology.IsOpenEmbedding
      (proj H ∘ (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) := by
  have hq : IsOpenQuotientMap (proj H) := hyperellipticEven_isOpenQuotientMap H h
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_
    (proj_inr_injective H) ?_
  · exact hq.continuous.comp continuous_inr
  · exact hq.isOpenMap.comp Topology.IsOpenEmbedding.inr.isOpenMap

/-! ## Lifted charts -/

/-- Affine chart, lifted via `proj ∘ Sum.inl` to a chart on the
even-projective curve. -/
noncomputable def affineLiftChart (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a : HyperellipticAffine H) :
    OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ :=
  (HyperellipticAffine.affineChartAt (H := H) a).lift_openEmbedding
    (isOpenEmbedding_proj_inl H h)

/-- Affine-infinity chart, lifted via `proj ∘ Sum.inr` to a chart on the
even-projective curve. -/
noncomputable def infinityLiftChart (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (b : HyperellipticAffineInfinity H) :
    OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ :=
  (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H h) b).lift_openEmbedding
    (isOpenEmbedding_proj_inr H h)

/-- Preferred chart at a point of `HyperellipticEvenProj H`: pick the
canonical representative via `Quotient.out` and case-split on `Sum.inl` /
`Sum.inr` to use the affine or affine-infinity lifted chart. -/
noncomputable def chartAt (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    HyperellipticEvenProj H → OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ :=
  fun q =>
    match Quotient.out q with
    | Sum.inl a => affineLiftChart H h a
    | Sum.inr b => infinityLiftChart H h b

/-! ## ChartedSpace instance

The hypothesis `h : ¬ Odd H.f.natDegree` is wrapped as `Fact` so the
ChartedSpace instance can be auto-resolved by typeclass synthesis: a
caller declares `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩` once, and
then `ChartedSpace ℂ (HyperellipticEvenProj H)` resolves automatically.
-/

theorem mem_chartAt_source (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (q : HyperellipticEvenProj H) :
    q ∈ (chartAt H h q).source := by
  haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
  have hQout : Quotient.mk (hyperellipticEvenSetoid H) (Quotient.out q) = q :=
    Quotient.out_eq q
  rcases hQout_cases : Quotient.out q with a | b
  · -- Sum.inl case: chart is `affineLiftChart H h a`, source contains `proj (Sum.inl a)`
    simp only [chartAt, hQout_cases, affineLiftChart,
      OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨a, ?_, ?_⟩
    · exact ChartedSpace.mem_chart_source a
    · -- Need `(proj H ∘ Sum.inl) a = q`
      change Quotient.mk _ (Sum.inl a) = q
      rw [← hQout_cases]
      exact hQout
  · -- Sum.inr case: symmetric (typeclass synth picks up the Fact for HyperellipticAffineInfinity)
    simp only [chartAt, hQout_cases, infinityLiftChart,
      OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨b, ?_, ?_⟩
    · exact ChartedSpace.mem_chart_source b
    · change Quotient.mk _ (Sum.inr b) = q
      rw [← hQout_cases]
      exact hQout

/-- `ChartedSpace ℂ (HyperellipticEvenProj H)` for even-degree `H.f`. -/
noncomputable instance instChartedSpace (H : HyperellipticData)
    [hf : Fact (¬ Odd H.f.natDegree)] :
    ChartedSpace ℂ (HyperellipticEvenProj H) where
  atlas := Set.range (chartAt H hf.out)
  chartAt := chartAt H hf.out
  mem_chart_source q := mem_chartAt_source H hf.out q
  chart_mem_atlas q := ⟨q, rfl⟩

/-! ## Chart-transition compatibility (EA2 stage 3)

Four pairwise compatibility theorems on the lifted charts:

* `affineLiftChart_compat_affineLiftChart` -- mechanical via
  `lift_openEmbedding_trans` + Codex's `affineChartAt_compat`.
* `infinityLiftChart_compat_infinityLiftChart` -- same, with
  `affineChartAt_compat` for the `reverseData` polynomial.
* `affineLiftChart_compat_infinityLiftChart` and the symmetric
  `infinityLiftChart_compat_affineLiftChart` -- the cross-summand
  transitions, where the underlying chart-level map involves the
  Möbius identification `x ↦ 1/x` on the gluing region. Currently
  axiomatized; their discharge requires explicit chart-formula
  computations (see docstrings below). -/

/-- Same-summand affine compatibility, transferred from
`HyperellipticAffine.affineChartAt_compat` via `lift_openEmbedding_trans`. -/
theorem affineLiftChart_compat_affineLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a a' : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((affineLiftChart H h a).symm.trans (affineLiftChart H h a')) : ℂ → ℂ)
      ((affineLiftChart H h a).symm.trans (affineLiftChart H h a')).source := by
  have hLift :
      (affineLiftChart H h a).symm.trans (affineLiftChart H h a') =
        (HyperellipticAffine.affineChartAt (H := H) a).symm.trans
          (HyperellipticAffine.affineChartAt (H := H) a') := by
    simp [affineLiftChart]
  rw [hLift]
  exact HyperellipticAffine.affineChartAt_compat (H := H) a a'

/-- Same-summand affine-infinity compatibility, transferred from
`HyperellipticAffine.affineChartAt_compat` for the `reverseData` polynomial. -/
theorem infinityLiftChart_compat_infinityLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (b b' : HyperellipticAffineInfinity H) :
    ContDiffOn ℂ ω
      (((infinityLiftChart H h b).symm.trans (infinityLiftChart H h b')) : ℂ → ℂ)
      ((infinityLiftChart H h b).symm.trans (infinityLiftChart H h b')).source := by
  have hLift :
      (infinityLiftChart H h b).symm.trans (infinityLiftChart H h b') =
        (HyperellipticAffine.affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H h) b).symm.trans
          (HyperellipticAffine.affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H h) b') := by
    simp [infinityLiftChart]
  rw [hLift]
  exact HyperellipticAffine.affineChartAt_compat
    (H := HyperellipticAffineInfinity.reverseData H h) b b'

/-- **Cross-summand compatibility (affine → infinity).** The chart-transition
between an affine chart and an affine-infinity chart through the gluing
region. The underlying chart-level transition involves the Möbius map
`x ↦ 1/x` (when both sides use proj-X) plus root-of-polynomial corrections
when proj-Y is used on either side.

**Currently axiomatized.** Discharge requires explicit case-split on the
four sub-cases (projX/Y × projX/Y) and explicit computation of the
transition formula in each. The smoothness of `x ↦ 1/x` on its domain
is `Inv.contDiffOn` style; the polynomial-root cases use Codex's
`polynomialLocalHomeomorph` machinery from `OddAtlas/AffineChart.lean`. -/
axiom affineLiftChart_compat_infinityLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H) :
    ContDiffOn ℂ ω
      (((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)) : ℂ → ℂ)
      ((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)).source

/-- **Cross-summand compatibility (infinity → affine).** Symmetric to
`affineLiftChart_compat_infinityLiftChart`. -/
axiom infinityLiftChart_compat_affineLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (b : HyperellipticAffineInfinity H) (a : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)) : ℂ → ℂ)
      ((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)).source

/-- Combined chart-transition compatibility for `chartAt`, by case-split on
both `Quotient.out` representatives. -/
theorem chartAt_compat (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (q q' : HyperellipticEvenProj H) :
    ContDiffOn ℂ ω
      (((chartAt H h q).symm.trans (chartAt H h q')) : ℂ → ℂ)
      ((chartAt H h q).symm.trans (chartAt H h q')).source := by
  unfold chartAt
  rcases Quotient.out q with a | b <;>
    rcases Quotient.out q' with a' | b'
  · exact affineLiftChart_compat_affineLiftChart H h a a'
  · exact affineLiftChart_compat_infinityLiftChart H h a b'
  · exact infinityLiftChart_compat_affineLiftChart H h b a'
  · exact infinityLiftChart_compat_infinityLiftChart H h b b'

/-- `IsManifold ℂ ω (HyperellipticEvenProj H)` for even-degree `H.f`. -/
noncomputable instance instIsManifold (H : HyperellipticData)
    [hf : Fact (¬ Odd H.f.natDegree)] :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticEvenProj H) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
    chartAt_compat H hf.out q q'

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
