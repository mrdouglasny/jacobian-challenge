/-
Copyright (c) 2026 Michal J Wallace. All rights reserved.
Released under the MIT license (the upstream repository LICENSE; © Michal J Wallace).
Original source: https://github.com/tangentstorm/JacobianChallenge
                 Jacobian/HolomorphicForms/CotangentBundle.lean (commit 82349bc8, 2026-06-01).
Note: the upstream repo LICENSE is MIT; on full adoption, vendor the upstream
LICENSE under `vendor/wallace-jacobian-challenge/`.

Vendored (trial) into this repository on 2026-06-02 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced under `Jacobians.Vendor.Wallace.HolomorphicForms.*`.
- Internal imports retargeted to the vendored module paths.
No mathematical content was altered.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions

/-!
# The cotangent bundle of a complex manifold

- `TangentBundle 𝓘(ℂ, E) X` — the tangent bundle (PRESENT in Mathlib).
- `Bundle.Trivial X ℂ` — the trivial line bundle (PRESENT).
- `Bundle.ContinuousLinearMap` — the bundle of continuous linear maps
  between two vector bundles over the same base (PRESENT in
  `Mathlib/Topology/VectorBundle/Hom.lean`).

The cotangent bundle is `Bundle.ContinuousLinearMap (RingHom.id ℂ)`
applied to the tangent bundle and the trivial line bundle. Its
fiber at `x : X` is `TangentSpace 𝓘(ℂ, E) x →L[ℂ] ℂ`.

`VectorBundle ℂ (E →L[ℂ] ℂ) CotangentSpace` is then automatic via
`Bundle.ContinuousLinearMap.vectorBundle`.
-/

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.unusedSectionVars false

namespace Jacobians.Vendor.Wallace.HolomorphicForms

/-!
## Fiber norm on the tangent / cotangent space

In Mathlib v4.31, `TangentSpace I x := E` is a `not reducible` type synonym
whose `deriving` clause provides `TopologicalSpace, AddCommGroup, Module 𝕜,
ContinuousSMul, ContinuousConstSMul` — but no longer a `NormedAddCommGroup`
or `NormedSpace`. Consequently the operator-norm instance
`ContinuousLinearMap.toNormedAddCommGroup` cannot synthesize a norm on the
cotangent fiber `TangentSpace 𝓘(ℂ,E) x →L[ℂ] (Bundle.Trivial X ℂ) x`.

We register the missing fiber norms by transporting `E`'s own structure
through the definitional equality `TangentSpace 𝓘(ℂ,E) x ≡ E` (the synonym
body), following Mathlib's own
`Mathlib.Geometry.Manifold.Riemannian.Basic.normedAddCommGroupTangentSpaceVectorSpace`.
The instances are tagged `@[instance_reducible]` so that their underlying
`AddCommGroup` / `TopologicalSpace` / `Module` projections stay definitionally
equal to the `deriving`-supplied ones (they are literally `E`'s, transported
through the synonym), which keeps the `VectorBundle ℂ (CotangentModelFiber ℂ)
(CotangentSpace ℂ X)` synthesis diamond-free — see the `example` below.

Because `TangentSpace` is `not reducible`, downstream consumers that need to
*synthesize the operator norm* through these instances must enable
`set_option backward.isDefEq.respectTransparency false` (exactly as Mathlib's
Riemannian-bundle lemmas do); see `SectionMetric.lean` /
`CompactRiemannSurface.lean`.
-/

/-- `NormedAddCommGroup` on the tangent space, transported from the model
fiber `E`. Diamond-free: the underlying `AddCommGroup` / `TopologicalSpace`
coincide definitionally with the `deriving`-supplied ones. -/
@[instance_reducible]
noncomputable instance instNormedAddCommGroupTangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℂ E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- `NormedSpace ℂ` on the tangent space, transported from the model fiber
`E`. Its `toModule` coincides definitionally with the `deriving`-supplied
`Module ℂ (TangentSpace …)`. -/
@[instance_reducible]
noncomputable instance instNormedSpaceTangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    NormedSpace ℂ (TangentSpace (modelWithCornersSelf ℂ E) x) :=
  inferInstanceAs (NormedSpace ℂ E)

/--
The cotangent space at `x : X`: continuous ℂ-linear functionals on
the tangent space at `x`. The model fiber `E` is exposed as an
explicit argument because Mathlib's `TangentSpace` indexes the model
through the `ModelWithCorners`.
-/
abbrev CotangentSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    (x : X) : Type _ :=
  TangentSpace (modelWithCornersSelf ℂ E) x →L[ℂ] (Bundle.Trivial X ℂ) x

/-- Model fiber of the cotangent bundle: `E →L[ℂ] ℂ`. -/
abbrev CotangentModelFiber
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Type _ :=
  E →L[ℂ] ℂ

/--
Sanity check: the cotangent space inherits a `VectorBundle` structure
automatically from Mathlib's `Bundle.ContinuousLinearMap.vectorBundle`,
because the tangent bundle and the trivial line bundle are both
vector bundles over `X`.
-/
example
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    VectorBundle ℂ (CotangentModelFiber E) (CotangentSpace E X) :=
  inferInstance

-- Sanity check: with the transported fiber norms above (and the
-- `backward.isDefEq.respectTransparency false` relaxation needed because
-- `TangentSpace` is `not reducible`), the cotangent fiber carries the
-- operator `NormedAddCommGroup`.
set_option backward.isDefEq.respectTransparency false in
noncomputable example
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    (x : X) :
    NormedAddCommGroup (CotangentSpace E X x) :=
  inferInstance

end Jacobians.Vendor.Wallace.HolomorphicForms
