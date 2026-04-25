/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license; see the LICENSE file vendored alongside the
original source at `vendor/kirov-jacobian-claude/LICENSE`.
Original source: https://github.com/rkirov/jacobian-claude
                 (commit 7ce9e2e8, 2026-04-24).

Vendored into this repository on 2026-04-25 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced from `Jacobians[.Montel]` to `Jacobians.Vendor.Kirov[.Montel]`.
- Updated transitive imports to match the new namespace.
No mathematical content was altered.
-/

import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# `ChartedSpace` from a surjective local homeomorphism

If `f : X → Y` is a surjective local homeomorphism (e.g. a covering map),
then `Y` inherits a `ChartedSpace X Y` structure: at each `y : Y`, the
chart is the inverse of a partial homeomorphism agreeing with `f` near a
chosen preimage of `y`.

We do not register this as an instance — the constructor
`chartedSpaceOfIsLocalHomeomorph` is intended to be supplied explicitly
in contexts like `Jacobians.ZLatticeQuotient`.

Candidate for Mathlib upstreaming.
-/

namespace IsLocalHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A partial homeomorphism agreeing with `f` near `x`, chosen by
`Classical.choose`. -/
noncomputable def chartAtPreimage {f : X → Y} (hf : IsLocalHomeomorph f)
    (x : X) : OpenPartialHomeomorph X Y :=
  Classical.choose (hf x)

lemma mem_source_chartAtPreimage {f : X → Y} (hf : IsLocalHomeomorph f)
    (x : X) : x ∈ (chartAtPreimage hf x).source :=
  (Classical.choose_spec (hf x)).1

lemma eq_chartAtPreimage {f : X → Y} (hf : IsLocalHomeomorph f) (x : X) :
    f = chartAtPreimage hf x :=
  (Classical.choose_spec (hf x)).2

/-- Charted space structure on `Y` induced by a surjective local
homeomorphism `f : X → Y`. The chart at `y` is the inverse of a partial
homeomorphism around a chosen preimage of `y`. -/
@[implicit_reducible]
noncomputable def chartedSpace {f : X → Y} (hf : IsLocalHomeomorph f)
    (hs : Function.Surjective f) : ChartedSpace X Y where
  atlas := Set.range fun y : Y =>
    (chartAtPreimage hf (Classical.choose (hs y))).symm
  chartAt y := (chartAtPreimage hf (Classical.choose (hs y))).symm
  mem_chart_source y := by
    set x := Classical.choose (hs y) with hx
    have hfx : f x = y := Classical.choose_spec (hs y)
    show y ∈ (chartAtPreimage hf x).target
    have hxs : x ∈ (chartAtPreimage hf x).source := mem_source_chartAtPreimage hf x
    have := (chartAtPreimage hf x).map_source hxs
    rwa [← eq_chartAtPreimage hf x, hfx] at this
  chart_mem_atlas y := ⟨y, rfl⟩

end IsLocalHomeomorph
