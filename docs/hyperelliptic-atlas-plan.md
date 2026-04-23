# Hyperelliptic atlas construction plan

_Drafted 2026-04-23. Target: discharge the 8 Hyperelliptic-specific
axioms (type + 7 instances + `AX_Hyperelliptic_genus`) to a concrete
manifold with proved instances. Estimated effort: 2-3 weeks of focused
Lean work._

## What's axiomatized today

In `Jacobians/ProjectiveCurve/Hyperelliptic.lean` (commit `78a28e8`):

```
axiom Hyperelliptic (H : HyperellipticData) : Type
axiom Hyperelliptic.inst{TopologicalSpace, T2Space, CompactSpace,
      ConnectedSpace, ChartedSpace, IsManifold}
axiom AX_Hyperelliptic_genus : genus (Hyperelliptic H) = H.genus
```

Where `HyperellipticData = { f : Polynomial ℂ // Squarefree f ∧
3 ≤ f.natDegree }`, and `H.genus = (H.f.natDegree - 1) / 2`.

This plan dissolves all 8 axioms into a real `def Hyperelliptic` with
proved instances and derived genus.

## Data model decision

Three reasonable encodings:

(A) **OnePoint-style compactification.** Affine piece `HyperellipticAffine`
    (already exists) plus 1 or 2 points at infinity glued via `OnePoint`
    or `WeightedProjective`. Matches the `ProjectiveLine := OnePoint ℂ`
    pattern.

(B) **Zariski-style quotient.** `{v ∈ ℂ³ \ {0} | F(v) = 0} / ℂ^×`
    where `F` is the homogenization of `y² - f(x)`. Matches
    `PlaneCurve`'s eventual construction — both live in weighted
    projective space `ℙ(1, g+1, 1)`.

(C) **Sheet-pair model.** `HyperellipticSheets H := {(x, y) | y² = f(x)}
    ∪ {points at infinity}` with an explicit sheet-swap involution.
    More direct; matches classical textbook exposition.

**Recommended: (A)**. Minimal prerequisites, matches `ProjectiveLine`
pattern, works for both parity cases:

```
def Hyperelliptic (H : HyperellipticData) : Type :=
  -- For odd deg f: OnePoint (HyperellipticAffine H)
  -- For even deg f: WithTwoInftyPoints (HyperellipticAffine H)
  match H.hasBranchAtInfinity with
  | true  => OnePoint (HyperellipticAffine H)
  | false => OnePoint (HyperellipticAffine H) ⊕ ...  -- or similar
```

Actually cleaner:

```
def Hyperelliptic (H : HyperellipticData) : Type :=
  -- Always a OnePoint compactification; the extra infinity point for
  -- even deg gets absorbed via the sheet-pair treatment on HAffine.
  OnePoint (HyperellipticAffine H)
```

## Phases

### Phase H0: Data model + topology (3-4 days)

**H0.1** Decide on the type formula (recommended: option (A) with
OnePoint).

**H0.2** Show `HyperellipticAffine H` is a nonempty locally-compact
Hausdorff topological space — it's a closed subtype of `ℂ²` via the
equation `y² = f(x)`, so inherits from ℂ². Use
`Topology.isEmbedding_subtype_val` and friends.

**H0.3** Show `OnePoint (HyperellipticAffine H)` is compact + T2 +
connected. `OnePoint` + compactification properties are in Mathlib
(`OnePoint.compactSpace`, etc.). Need `Nonempty` (from picking any
non-branch point) and `LocallyCompactSpace` (from ℂ² being locally
compact + closed subtype).

**H0.4** Derive `TopologicalSpace`, `T2Space`, `CompactSpace`,
`ConnectedSpace`, `Nonempty` instances.

**Deliverable:** 5 of 7 Buzzard instances proved. Remaining:
`ChartedSpace ℂ` and `IsManifold 𝓘(ℂ) ω`.

### Phase H1: Affine smooth-locus chart (3-4 days)

**H1.1** Define `smoothLocus H` — points where `∂F/∂y ≠ 0`, i.e.
`y ≠ 0`. (For the minority of points where `∂F/∂x` is the non-zero
partial, the projection onto `y` works; handle both cases.)

**H1.2** At a smooth point `p = (x₀, y₀)` with `y₀ ≠ 0`, the map
`(x, y) ↦ x` is a local chart via the implicit function theorem: for
`x` near `x₀`, there's a unique `y` near `y₀` with `y² = f(x)`, given
by the analytic function `y = (a branch of) √(f(x))`.

**H1.3** Use Mathlib's `ContDiffAt.toPartialHomeomorph` or similar
(from `Mathlib.Analysis.Calculus.InverseFunctionTheorem`) to extract
the local chart as an `OpenPartialHomeomorph`.

**H1.4** Package as a family `(affineChart p : OpenPartialHomeomorph
(HyperellipticAffine H) ℂ)` for each smooth point `p`.

**Deliverable:** Affine-patch chart functions. No instance yet.

### Phase H2: Branch-point charts (4-5 days)

**H2.1** At a root `a` of `f`, the point `(a, 0)` is a branch point.
Local parameter: `t := √(x - a)`, so `x = a + t²`, `y = t · √(f(x)/(x-a))`
(the other factor analytic because `f(x)/(x - a)` is a polynomial).

**H2.2** Define `branchChart a : OpenPartialHomeomorph
(HyperellipticAffine H) ℂ` on a neighborhood of `(a, 0)` via the
parameter `t`.

**H2.3** Prove the chart is analytic by verifying the local square-root
function via Mathlib's `Complex.cpow` or a custom `analyticAt_sqrt`
lemma on a slit neighborhood of `a`.

**H2.4** Verify compatibility with affine charts on the overlap: at
points `(x, y)` near a branch point with `x ≠ a`, both charts are
defined and the transition is `t ↦ a + t²` → `(a + t², y(t))`, which is
analytic.

**Deliverable:** Branch-point charts (one per root of `f`) + their
transitions with affine charts.

### Phase H3: Infinity chart(s) (3-5 days)

**H3.1** **Odd deg (`d = 2g + 1`):** Single point at infinity `∞`, which
is a branch point. Local parameter `u := 1/y` or similar; explicit formula
involves `x = y² / leadCoeff f + ...`.

**H3.2** **Even deg (`d = 2g + 2`):** Two points at infinity, `∞₊` and
`∞₋`, distinguished by the sign of the leading `y` coefficient. Local
parameter `w := 1/x`, with `y = ± x^{g+1} · √(1 + ...)`.

**H3.3** Chart functions on the infinity neighborhood, transitioning
to the affine chart via `(x, y) ↦ 1/x`.

**H3.4** OnePoint-compatibility: the chart extends to `OnePoint
(HyperellipticAffine H)` by mapping `OnePoint.infty` to the chosen
parameter origin.

**Deliverable:** Atlas complete.

### Phase H4: ChartedSpace + IsManifold instances (2-3 days)

**H4.1** Package the collection `{affine charts, branch charts,
infinity chart(s)}` into a `ChartedSpace ℂ (Hyperelliptic H)`.

**H4.2** Prove `IsManifold 𝓘(ℂ) ω (Hyperelliptic H)` by verifying
all pairwise chart transitions are in `contDiffGroupoid ω 𝓘(ℂ)` — i.e.
`ContDiff ω` on their overlap domains.

**H4.3** The two non-trivial transitions:
* Affine × branch: computed above (Phase H2.4).
* Affine × infinity: `x ↦ 1/x` + inverse, analytic on `x ≠ 0`.
* Branch × infinity: composition of the above two; analytic where
  both are defined.

**Deliverable:** 7/7 Buzzard typeclass instances proved. **All 7
instance axioms retire.** Only `Hyperelliptic H : Type` and
`AX_Hyperelliptic_genus` remain axiomatic.

### Phase H5: Retire `Hyperelliptic H : Type` axiom (1 day)

**H5.1** Replace `axiom Hyperelliptic (H : HyperellipticData) : Type`
with `def Hyperelliptic (H : HyperellipticData) : Type :=
OnePoint (HyperellipticAffine H)`.

**H5.2** Remove the 6 instance axioms — instances are now derived
through the `OnePoint`-wrapped structure.

**Deliverable:** `Hyperelliptic` is a real `def`. 8 axioms → 1
axiom (just `AX_Hyperelliptic_genus`).

### Phase H6: Prove `AX_Hyperelliptic_genus` (5-7 days, depends on
`HolomorphicOneForm` infrastructure)

**H6.1** Construct the explicit holomorphic differentials
`ω_k := x^k dx / y` for `0 ≤ k < H.genus`.

**H6.2** Verify each `ω_k` satisfies `IsHolomorphicOneFormCoeff` +
`SatisfiesCotangentCocycle` on the atlas from Phase H4.

**H6.3** Show `{ω_k}_{k=0}^{g-1}` is linearly independent in
`HolomorphicOneForm (Hyperelliptic H)`.

**H6.4** Show `{ω_k}` spans `HolomorphicOneForm (Hyperelliptic H)` —
the hard part; uses residue analysis at branch points and infinity to
show any holomorphic 1-form must be of the form `∑ c_k · x^k dx / y`.

**H6.5** Conclude `Module.finrank ℂ (HolomorphicOneForm (Hyperelliptic
H)) = g`, retiring `AX_Hyperelliptic_genus`.

**Deliverable:** Hyperelliptic atlas + genus fully discharged. 0
Hyperelliptic-specific axioms.

## Dependencies

Phase H1 needs Mathlib's implicit function theorem infrastructure — we
have it (`ContDiffAt.toPartialHomeomorph` etc.).

Phase H2 needs a holomorphic square-root on a slit neighborhood.
Mathlib has `Complex.cpow` but the `analyticAt` lemmas may need
supplementation.

Phase H3 needs care with the parity split but no exotic dependencies.

Phase H6 needs the `HolomorphicOneForm` predicates refined (done, per
commit `8ffe985`) and the residue analysis; residues at branch points
are a mini-project in their own right.

## Suggested assignment

Single focused contributor can complete H0-H5 in ~2 weeks. H6 is
another 1-2 weeks. Total: **3-4 weeks** for a concrete implementation
from today's axiomatic state.

Parallel parallelism is limited: H1-H3 can share a branch but H4 needs
all three done. H6 depends on H5.

## Payoff

- All 8 Hyperelliptic-specific axioms discharged.
- First non-torus concrete Riemann surface in the project (Elliptic is a
  torus; ProjectiveLine is trivial).
- Demonstrates the framework handles "real" curves (with branch points
  and multiple components at infinity) correctly.
- Unlocks `AX_PluckerFormula` for a non-plane example (hyperelliptic
  curves are not generically plane curves).
- Path forward for `PlaneCurve` atlas (similar structure; `x ↦ x`-style
  patches + implicit function theorem at smooth points).

## Status

Plan drafted but not yet executed. When work begins, break into
focused PRs per phase (H0 → H1 → H2 → H3 → H4 → H5 → H6). Track
against `docs/completion-plan.md` workstream E2.
