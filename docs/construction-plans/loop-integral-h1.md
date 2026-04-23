# Plan #2: Construct `loopIntegralToH1`

## Axiom being retired

```lean
axiom loopIntegralToH1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)
```

Location: `Jacobians/RiemannSurface/PathIntegral.lean:101`.

`H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` —
Hurewicz-style first integral homology.

## Classical content

Given a loop class `[γ] ∈ H_1(X, ℤ)` and a holomorphic 1-form `ω`,
return `∫_γ ω`. Linear in `[γ]` (additive-group-homomorphism),
ℂ-linear in `ω`. Well-definedness on `H_1`:
- Homotopy-invariance of path integration.
- Independence of the representative loop in the homotopy class.
- Additivity over loop concatenation (fundamental-group-to-H_1 descent).

## Target replacement

```lean
noncomputable def loopIntegralToH1 {X} [...] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) := by
  -- Descend through Additive / Abelianization / FundamentalGroup
  -- to an underlying `π₁(X, x₀) →* Multiplicative (...)` hom
  -- which is induced by loop integration.
  apply Additive.toMul.symm.toAddMonoidHom.comp
  apply AddMonoidHom.mk'
  · exact fun γ_ab => -- integrate a representative loop of γ_ab
  · -- proof of additivity
```

## Prerequisites

### A. Shared with Plan #1
- Path existence (`AX_pathExists`) — already needed.
- Multi-chart path integration (`pathIntegralAnalyticArc`) — shared
  infrastructure.

### B. Homotopy invariance of path integration

**The core deep fact**: if `γ, γ' : [0, 1] → X` are smoothly homotopic
loops based at `x₀`, then `∫_γ ω = ∫_{γ'} ω` for any holomorphic 1-form
`ω`.

Classical proof: Cauchy's theorem on chart disks (for the holomorphic
1-form restricted to a disk, `∮ ω = 0`) + Stokes on the homotopy
rectangle (the two loops are two sides of a cylinder; integrals over
opposite sides agree).

Lean path:

1. **Cauchy on a disk**: for a holomorphic function on a closed disk,
   the contour integral around the boundary vanishes. Mathlib has this
   for functions `ℂ → ℂ` (`Complex.integral_boundary_eq_zero`). Our
   setting is slightly shifted: integrate a 1-form `ω` around a disk in
   a chart. Reduces to Cauchy on the chart coefficient.

2. **Smooth homotopy decomposition**: divide the homotopy rectangle
   into small sub-rectangles each contained in a single chart. Apply
   Cauchy to each sub-rectangle boundary. Sum to see that the total
   loop-integral difference vanishes.

3. **Extension from smooth to piecewise-real-analytic homotopy**: by
   approximation.

Effort: ~300 LOC. This is the hard part of Plan #2.

### C. π₁ → H_1 descent

Once homotopy invariance is proved, the path integral becomes a
well-defined map `π₁(X, x₀) → Multiplicative ℂ^∨` (group hom). By
Abelianization, this descends to `H_1(X, ℤ) → ℂ^∨`. Then `Additive`
wraps for the additive-group convention.

Effort: ~100 LOC (mostly typeclass plumbing via `Abelianization.lift`
and `Additive.toMul`).

### D. Linearity in `ω` (ℂ-linearity)

Follows from linearity of the underlying `intervalIntegral`. Should be
easy once the def is in place.

Effort: ~30 LOC.

## Phases

| Phase | Content | Effort |
|---|---|---|
| P1 | Shared with Plan #1: path existence, multi-chart integration | (from Plan #1) |
| P2 | Cauchy on chart disks (local version) | 3 days |
| P3 | Stokes on homotopy rectangle / smooth homotopy invariance | 5 days |
| P4 | π₁ → Abelianization → Additive descent as a proper `AddMonoidHom` | 2 days |
| P5 | Retire `loopIntegralToH1` axiom to def | 1 day |
| P6 | Retire downstream: `periodMap` no longer wraps an axiom | 1 day |

**Total: ~1.5 weeks** on top of Plan #1's infrastructure.

Combined with Plan #1: **~3 weeks total** for the full path-integral
machinery.

## References

* Mumford, *Tata Lectures on Theta I*, §II.2–II.4.
* Forster, *Lectures on Riemann Surfaces*, Ch. I §10–13.
* Griffiths–Harris, Ch. 0.2.

## Exit criterion

- `loopIntegralToH1` is a real `noncomputable def`.
- `periodMap` is no longer wrapping an axiom.
- Build green; net axiom count delta: **–1**.

## Downstream impact

Once discharged, `periodMap`, `periodMapInBasis`, and
`periodLatticeInBasis` all become fully axiom-free at the path-integral
level — their only residual axioms are `AX_PeriodLattice` (lattice
rank) and `instPeriodLatticeDiscrete` (discreteness), both Prop-level
Riemann-bilinear consequences.
