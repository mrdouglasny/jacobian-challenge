# HyperellipticEven atlas + genus plan

_Drafted 2026-04-26. Companion to
[`hyperelliptic-odd-atlas-plan.md`](hyperelliptic-odd-atlas-plan.md);
narrows to the even-degree parity (two points at infinity, glued via
quotient construction). Target: derive
`genus_HyperellipticEven_eq` honestly._

## What's in scope

The classical formula:
```
genus (HyperellipticEven H h) = H.f.natDegree / 2 - 1
```
when `H.f.natDegree = 2g + 2`.

Currently:
- `HyperellipticEven H h` has `TopologicalSpace`, `T2Space`,
  `CompactSpace`, `ConnectedSpace`, `Nonempty` instances (real, in
  `Even.lean`).
- It has **no `ChartedSpace ℂ`, no `IsManifold`** — so
  `HolomorphicOneForm (HyperellipticEven H h)` is not yet well-typed
  and the genus theorem cannot even be stated.
- The unified `Hyperelliptic H` carries the genus via
  `genus_Hyperelliptic_eq_of_even`, but that routes through the axiom
  `AX_Hyperelliptic_genus`. **Honest path: build the atlas + basis +
  RR upper bound directly on `HyperellipticEven`.**

## Phase EA1 — `HyperellipticAffineInfinity` charted-space + manifold

Mirror of `OddAtlas/AffineChart.lean` over the second affine chart.
The defining polynomial in this chart is `Polynomial.reverse H.f`;
otherwise the structure is identical (smooth-locus split via `y ≠ 0`
vs `f'(x) ≠ 0` on the reverse-poly side, two `OpenPartialHomeomorph`
families via the implicit function theorem).

**Files**: `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas/InfinityAffineChart.lean`.

Estimated ~150–300 LOC. Mostly mechanical translation of
`OddAtlas/AffineChart.lean` with `H.f → Polynomial.reverse H.f`.

## Phase EA2 — Open-quotient chart lifting (the novel piece)

Codex's OddAtlas lifts charts via
`OpenPartialHomeomorph.lift_openEmbedding`, valid for an *open
embedding* of the source space. The map
`HyperellipticEvenPre → HyperellipticEvenProj` is an *open quotient
map*, not an open embedding (it identifies points across the gluing
relation), so the OnePoint trick doesn't carry over directly.

### Design (chosen, 2026-04-26)

**Approach (2): generic chart-lifting through an open quotient map
with injective-on-source restriction.** Build a reusable lemma:

```lean
namespace OpenPartialHomeomorph

/-- Lift a chart `e : OpenPartialHomeomorph α β` through an open
quotient map `q : α → γ` whose restriction to `e.source` is injective.

Source: `q '' e.source` (open in `γ` because `q` is an open map and
`e.source` is open in `α`).
Target: `e.target`.
Forward map: `e ∘ (any preimage in e.source)` — well-defined because
`q` is injective on `e.source`.
Inverse map: `q ∘ e.symm`. -/
noncomputable def lift_openQuotientMap
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
      [TopologicalSpace γ]
    (e : OpenPartialHomeomorph α β) (q : α → γ)
    (hq : IsOpenQuotientMap q)
    (hinj : Set.InjOn q e.source) :
    OpenPartialHomeomorph γ β := …
```

Plus the corresponding `lift_openQuotientMap_trans` lemma analogous
to `lift_openEmbedding_trans` (so chart transitions on the lifted
charts reduce to chart transitions on the source charts — this is
what makes the eventual `IsManifold` proof clean).

### Why (2) over (1)

- **Reusable**: the lemma is independent of hyperelliptic curves and
  could land in Mathlib (`Topology.OpenPartialHomeomorph.Constructions`
  has `lift_openEmbedding` already; `lift_openQuotientMap` is a
  natural sibling).
- **Symmetric structure**: makes the chart-lifting code symmetric
  between affine and affine-infinity sides. Per-summand-chart (option
  1) requires a case split on `Sum.inl` / `Sum.inr` baked into every
  chart-side computation; the lift-via-quotient version pushes that
  case split entirely into the proof of `Set.InjOn q e.source`.
- **Overlap proof modularity**: `lift_openQuotientMap_trans` reduces
  affine × affine-infinity overlap compatibility to a single fact
  about the gluing equivalence (injective on each affine side, and
  the gluing identification on the overlap matches the
  `affineInfinityOverlapHomeomorph` Codex already built in `Even.lean`
  around line 656).
- **Long-run upstream**: same applies to any other open quotient
  manifold construction (e.g., the period-lattice quotient itself,
  via Kirov's `ZLatticeQuotient` infrastructure). One lemma serves
  many.

**Files**: 
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas/QuotientLift.lean`
  — the generic `lift_openQuotientMap` lemma (could be PR'd to
  Mathlib as a standalone). ~80–150 LOC.
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — apply
  twice (affine and affine-infinity), assemble `ChartedSpace +
  IsManifold` via the lifted charts. ~150–250 LOC.

## Phase EA3 — Even basis differentials

Mirror of the planned odd basis-differential theorems
(`hyperellipticDxOverY`, `hyperellipticBasisDifferential` in
`Extensions/Hyperelliptic.lean`), specialized to the even case.

The form `x^k dx/y` is holomorphic on `HyperellipticEven H h` for
`k = 0, …, g - 1` where `g = H.f.natDegree / 2 - 1`. The constraint
`k ≤ g - 1` is exactly what keeps the form finite at *both* infinity
points ∞₊ and ∞₋ in the even case (vs the single ∞ in odd).

**Files**: `Jacobians/Extensions/HyperellipticEven.lean` (companion
to the existing `Extensions/Hyperelliptic.lean`).

Estimated ~100–200 LOC. Concrete polynomial algebra; mechanical once
EA2 lands.

## Phase EA4 — Linear independence + genus formula

```lean
theorem hyperellipticEvenBasisDifferential_linearIndependent : …
theorem genus_HyperellipticEven_eq
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticEven H h) =
      H.f.natDegree / 2 - 1
```

Lower bound: the basis above is linearly independent in
`HolomorphicOneForm`, so its rank gives a lower bound on
`Module.finrank` (uses bridge-derived `FiniteDimensional`).

Upper bound: `AX_RiemannRoch` applied to the canonical divisor on the
even hyperelliptic.

Estimated ~100–200 LOC. Same shape as the planned odd theorems.

## Total estimate

~600–1100 LOC, multi-day work. Closest analog landed: `OddAtlas`
under `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/` (~700 LOC
total per Codex's progress doc).

## File layout (proposed)

```
Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean             -- EA2 entry point + ChartedSpace/IsManifold
Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas/
├── InfinityAffineChart.lean   -- EA1 (HyperellipticAffineInfinity atlas)
└── QuotientLift.lean          -- EA2 generic lemma (Mathlib-PR candidate)

Jacobians/Extensions/HyperellipticEven.lean                        -- EA3 + EA4
```

Add `import` lines to:
- `Jacobians/ProjectiveCurve.lean` (for the atlas)
- `Jacobians/Extensions.lean` (for the genus theorem)

## Discharge order

EA1 → EA2 → EA3 → EA4. Each phase is an independent commit.

EA1 is fully mechanical and unblocks nothing else conceptually new
— a good first commit.

EA2 is the design-novel piece (the `lift_openQuotientMap` lemma is
the long-run upstream contribution).

EA3 + EA4 are mechanical mirrors of the planned odd theorems, gated
on EA1+EA2 only because `HolomorphicOneForm (HyperellipticEven H h)`
isn't well-typed without the chart structure.

## Out of scope

- The unified `Hyperelliptic H` axioms (`AX_Hyperelliptic_genus`,
  `AX_Hyperelliptic_evenEquiv`, `AX_Hyperelliptic_oddEquiv`) — those
  retire automatically once both `genus_HyperellipticEven_eq` and the
  planned `genus_HyperellipticOdd_eq` are real, by routing the
  unified-type theorems through homeomorphism transfer.
- The "real" `pullbackOneForm` axiom — orthogonal track in
  `Axioms/AbelJacobiMap.lean`.
