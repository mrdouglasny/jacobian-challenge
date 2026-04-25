# Hyperelliptic Odd Atlas Progress

Updated: 2026-04-25

This note records the current state of the odd hyperelliptic atlas work after
repairing the imported scaffold and pushing the first real reductions of the
placeholder boundary.

## What is now real

### Affine smooth-locus setup

In `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/AffineChart.lean`:

- `smoothLocusY` and `smoothLocusX` are defined.
- `isOpen_smoothLocusY` and `isOpen_smoothLocusX` are proved.
- `eval_derivative_ne_zero_of_eval_eq_zero` and
  `mem_smoothLocusX_of_y_eq_zero` reduce the squarefree argument at branch
  points to a usable local lemma.
- `smoothLocus_cover` is proved, so the two affine chart families really cover
  `HyperellipticAffine H`.
- `affineChartAt` is defined by case split on the cover, with simp lemmas for
  the two branches.
- `ChartedSpace ℂ (HyperellipticAffine H)` is a real instance.

### Affine manifold assembly

The old broad placeholder

`axiom affine_isManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticAffine H)`

has been removed.

Instead, the remaining OA1 boundary is now explicit:

- `affineChartProjX_compat_affineChartProjX`
- `affineChartProjX_compat_affineChartProjY`
- `affineChartProjY_compat_affineChartProjX`
- `affineChartProjY_compat_affineChartProjY`

From those four compatibility axioms, `affineChartAt_compat` and the affine
`IsManifold` instance are now assembled in Lean.

This is a real improvement: the fake boundary now sits exactly at the missing
inverse-function-theorem chart outputs and their overlap formulas, instead of
at the whole affine manifold package.

### Odd one-point assembly

In `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean`:

- affine charts are lifted to `OnePoint` via `lift_openEmbedding`;
- `chartAt` on `HyperellipticOdd H h` is a real definition;
- `ChartedSpace ℂ (HyperellipticOdd H h)` is a real instance;
- `IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h)` is assembled by case split on
  affine points versus `∞`.

The affine-affine compatibility leg no longer depends on a blanket axiom; it
now routes through the real theorem `HyperellipticAffine.affineChartAt_compat`.

### Extension-level progress

In `Jacobians/Extensions/Hyperelliptic.lean`:

- `HyperellipticAffine.involution` is now defined as `(x, y) ↦ (x, -y)`;
- `hyperellipticInvolution` on `HyperellipticOdd H h` is now a real global
  function;
- `hyperellipticInvolution_involutive` is proved.

These were genuine `sorry`s that are now discharged.

## What is still axiomatized

### OA1 chart construction

The actual local charts are still placeholders:

- `affineChartProjX`
- `affineChartProjX_mem_source`
- `affineChartProjY`
- `affineChartProjY_mem_source`

and the four affine compatibility axioms listed above are still placeholders.

This is the current affine boundary.

### OA2 infinity chart

In `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`, the
following remain axiomatized:

- `infinityInverseMap`
- `infinityChart`
- `infinityChart_mem_source`

In `OddAtlas.lean`, the mixed compatibility statements remain axioms:

- `infinityChart_compat_affineLift`
- `affineLift_compat_infinityChart`

This is the current infinity boundary.

### Extension theorems still open

The main hyperelliptic extension theorems are still open, including:

- `hyperellipticDxOverY`
- `hyperellipticBasisDifferential`
- `hyperellipticBasisDifferential_linearIndependent`
- `genus_HyperellipticOdd_eq`
- `hyperellipticInvolution_contMDiff`
- `card_fixedPoints_hyperellipticInvolution`

## What builds

As of this checkpoint, the following targets build:

- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas`
- `lake build Jacobians.Extensions.Hyperelliptic`

The extension file still has its remaining `sorry`s, but the odd atlas and its
downstream imports are back in a consistent state.

## Recommended next steps

1. Replace the four affine compatibility axioms with real transition formulas
   coming from the `ProjX` / `ProjY` inverse-function-theorem charts.
2. Prove `hyperellipticInvolution_contMDiff` once those chart formulas are
   exposed, since in local coordinates the involution should become either
   `x ↦ x`, `y ↦ -y`, or an explicit transition through the infinity chart.
3. Only after the chart package is less axiomatic, start the real construction
   of `dx / y` and the basis differentials.
