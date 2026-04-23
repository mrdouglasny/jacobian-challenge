# Plan #5: Construct `localOrder`

## Axiom being retired

```lean
axiom localOrder {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (p : X) (q : Y) : ℕ
```

Location: `Jacobians/Axioms/BranchLocus.lean:62`.

## Classical content

Given a map `f : X → Y` between complex 1-manifolds, a point `p : X`,
and a target point `q : Y`:
- If `f p ≠ q`: return `0`.
- If `f p = q` and `f` is holomorphic: return the **order of zero** of
  the map `z ↦ f(z) - q` at `p`, computed in chart coordinates. This is
  a positive integer (because non-constant holomorphic functions have
  isolated zeros of finite order).
- If `f` is not locally non-constant at `p` (e.g., identically `q`
  near `p`): return `0` (or we could use an arbitrary convention; the
  `AX_BranchLocus` axiom only uses this on non-constant `f`).

For a non-constant holomorphic map between compact Riemann surfaces,
this integer is well-defined by the Taylor-series structure.

## Target replacement

```lean
noncomputable def localOrder {X Y} [...] (f : X → Y) (p : X) (q : Y) : ℕ :=
  if hne : f p ≠ q then 0
  else
    -- f p = q; compute Taylor order of (z ↦ (chart_q ∘ f ∘ chart_p.symm) z - chart_q q) at chart_p p
    let φ_p := extChartAt 𝓘(ℂ) p
    let φ_q := extChartAt 𝓘(ℂ) q
    let F : ℂ → ℂ := fun z => φ_q (f (φ_p.symm z)) - φ_q q
    -- F(φ_p p) = 0; return its order-of-zero at z = φ_p p
    Polynomial.order_at_zero F (φ_p p)  -- or analogous via formal power series
```

Where `Polynomial.order_at_zero` is a placeholder for the real Mathlib
name — we need the "order of vanishing of an analytic function at a
point."

## Prerequisites

### A. Order of zero for analytic functions `ℂ → ℂ` at a point

Mathlib has `Polynomial.rootMultiplicity` and `HasEigenvalue.order` and
formal-power-series order (`HahnSeries.order` / `PowerSeries.order`),
but the specific "order of vanishing at a point for an analytic
function" at the pin may or may not exist. Check:
- `AnalyticAt.order` or similar
- If missing: construct from first principles as
  `inf {n | n ≠ 0 ∧ iteratedDeriv n F (φ_p p) ≠ 0}`

Effort: ~100 LOC if Mathlib has it, ~250 if we need to build it.

### B. Chart-independence of `localOrder`

The order should be well-defined independent of the choice of charts
at `p` and `q`. Proof: chart transitions are biholomorphic (derivative
nonvanishing), so composition doesn't change the zero-order.

Effort: ~100 LOC.

### C. Non-constant maps have finite positive order at a zero

For non-constant holomorphic `F : ℂ → ℂ` with `F(a) = 0`, the order at
`a` is in `1 ≤ order < ∞`. Uses: principle of isolated zeros.

Effort: ~50 LOC (mostly unpacking Mathlib's existing isolated-zeros
machinery).

### D. `AX_BranchLocus` compatibility

Once `localOrder` is a real def, verify that the existing axiom
`AX_BranchLocus` is still well-formed and that its `∑' p, localOrder f p q`
fiber-sum matches the classical fiber count. (Should follow from
well-definedness.)

Effort: ~50 LOC.

## Phases

| Phase | Content | Effort |
|---|---|---|
| P1 | `AnalyticAt.order` for `ℂ → ℂ` (either use Mathlib or build) | 2–4 days |
| P2 | Chart-independence of the order | 2 days |
| P3 | Positive order for non-constant maps | 1 day |
| P4 | `localOrder` as real `def` | 1 day |
| P5 | Compatibility with `AX_BranchLocus` (no downstream changes needed) | 1 day |

**Total: ~1 week** focused contributor.

## References

* Forster, Ch. I §4 (local behaviour of holomorphic maps).
* Mumford, Vol I §II.2.
* Miranda, Ch. II §2 (ramification and degree).

## Exit criterion

- `localOrder` is a real `noncomputable def`.
- Build green; net axiom count delta: **–1**.

## Downstream impact

- Unblocks Plan #4 (`pushforwardOneForm`), which needs `localOrder` to
  weight fiber sums.
- `degreeImpl` (currently real def via `Classical.choose` on
  `AX_BranchLocus`) becomes more structural: could be redefined as
  `∑' p ∈ f⁻¹(q), localOrder f p q` for a specific generic `q`, though
  the current definition via `AX_BranchLocus` is already acceptable.
