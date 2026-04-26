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

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
