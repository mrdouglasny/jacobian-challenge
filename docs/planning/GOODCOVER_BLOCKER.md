# Good-cover blocker — what separates the T-FG engine from `Group.FG π₁` of a compact surface

Date: 2026-06-11. Branch `feat/s2-topology` (S2 lane,
`HANDOVER_PARALLEL_ACCOUNT.md` Package 1 Goal B). Companion to
`S2_LANE_PROGRESS.log`.

## What is DONE (this branch)

`Jacobians/Topology/FiniteGoodCover.lean` proves the **engine**:

```
theorem SimplyConnectedGoodCover.fundamentalGroup_fg_of_goodCover
    (C : SimplyConnectedGoodCover X) [PathConnectedSpace X] (x₀ : X) :
    Group.FG (FundamentalGroup X x₀)
```

where `SimplyConnectedGoodCover X` packages: finitely many open sets covering
`X`, each simply connected, all pairwise intersections path-connected when
nonempty. Generators are explicit (`coverGen b e₁ e₂`: spoke–detour–spoke
conjugates through chosen anchor points of the pairwise intersections), at most
`n·(n²+1)²` of them.

Proof method: ι-indexed Lebesgue subdivision of a loop + membership-form
telescope (following the two-open van Kampen telescoping in the ported
`KirovDolbeault/VanKampen.lean`), plus the key finiteness device: routing each
junction spoke through a fixed anchor of the adjacent-charts intersection makes
each conjugated-arc class depend only on the charts' *indices*, by uniqueness
of path classes inside a simply connected set.

## What is NOT done: good-cover EXISTENCE (the named gap)

**(GC-1)** `SimplyConnectedGoodCover X` for `X` a compact Riemann surface
(compact charted ℂ-manifold). The classical proof takes a Riemannian metric
and covers `X` by finitely many **geodesically convex** balls: convexity is
closed under intersection, and convex ⇒ contractible ⇒ simply connected with
path-connected intersections. Mathlib at our pin has **no geodesic convexity /
totally normal neighborhoods** (`Mathlib.Geometry.Manifold` has no Riemannian
exponential map), so this route is closed for now.

Candidate Lean routes, in rough order of plausibility:

1. **Hyperbolic/euclidean/spherical uniformization-free local geometry.** For
   a *chart-level* metric: pull back small euclidean disks. The blocker is
   that intersections of disks from *different* charts need not be
   path-connected. No uniform fix without geometry of the transition maps.
2. **Triangulation-style combinatorics.** A finite atlas of closed disk
   charts with controlled overlaps (`good atlas`). Constructing one from raw
   `ChartedSpace ℂ X` is essentially the existence of a good cover again.
3. **Wait for Mathlib Riemannian geometry** (exponential map + totally normal
   neighborhoods are on the community roadmap), then route 0 (convex balls)
   is ~1–2 sessions of glue.

**(GC-2)** Worth checking before investing in GC-1: the H-lane consumer
(`moduleFinite_H1_of_fundamentalGroup_fg`) only needs `Module.Finite ℤ (H1)`,
i.e. FG of the *abelianization*. No obviously easier route is known to us
(H₁ finiteness for compact surfaces is the same classical input), but a
Dolbeault/Hodge-side argument by the keystone machinery (finite-dimensional
`H^{0,1}` + period pairing) might bound `rank H1` directly — that would
*also* hit T-RANK. Scoping that belongs to the T-RANK stretch goal, not here.

## Consumer wiring (done over the gap)

`Group.FG (FundamentalGroup X x₀)` is exactly the instance hypothesis of
`moduleFinite_H1_of_fundamentalGroup_fg` (H-lane, merged PR #198):
a `SimplyConnectedGoodCover X` + `PathConnectedSpace X` instance for the
surface discharges T-FG with no further work.
