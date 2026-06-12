# SUP lane — discharging `AX_AbelSupset` (Abel ⊇, Abel–Jacobi side)

*Opened 2026-06-12 on `feat/abel-supset` (based on `origin/feat/abel-flip`;
`#222` not yet on `origin/main` at lane start). Target:*

    AX_AbelSupset : PrincipalDivisors X ≤ (abelJacobiDiv X).ker

*one of the two remaining challenge-critical axioms after the #222
split-flip.*

## Route refresh (2026-06-12)

The planned route is the Liouville / symmetric-product argument
([`ABEL_SUPSET_LIOUVILLE_ROUTE.md`](ABEL_SUPSET_LIOUVILLE_ROUTE.md), "Route L").
It was chosen 2026-06-07 to bypass the residue theorem and manifold Stokes.
Since then #221 landed the E-vocabulary (`SmoothOneChain`, `period`,
`exists_meromorphic_of_zeroPeriodChain'`, the E6 translation bricks), so a
**direct chain route** ("Route C") deserves a fresh look before committing:

**Route C (pullback chain + trace).** Pick a path `σ` in `ℙ¹` from `0` to
`∞`; lift it through the branched cover `toP1 f` to a smooth 1-chain `c`
with `∂c = ±(div f)` (each zero of order `e` emits `e` sheet-lifts); then
`period(c, ω) = ∫_σ trace_f(ω)`, and `trace_f(ω)` is a holomorphic 1-form
on `ℙ¹` (IFT off branch values + removable singularities), hence `0`
(`g(ℙ¹) = 0`); a chain↔lattice bridging lemma (reverse of the E6 adapter
computation) converts the zero-period bounding chain into
`divisorPeriodVector x₀ (div f) ∈ Λ`.

**Comparison.** The two routes share their analytic core: local sheet
structure of `toP1 f` (IFT local roots off the branch locus), fiber-divisor
bookkeeping (`weightedFiberConservation`, `mapAnalyticOrderAt_toP1*` — all
landed), and a removable-singularity step at branch values. They differ in:

| | Route L (Liouville) | Route C (chain + trace) |
|---|---|---|
| removable step | symmetric sum of **integrals** `∑ᵢ ∫^{xᵢ(y)} ω`: each term individually bounded (ω holomorphic), so boundedness is term-by-term — the route doc's "single load-bearing lemma" stays easy | symmetric sum of **derivative-weighted values** `∑ᵢ ω(xᵢ(y)) xᵢ'(y)`: individual terms BLOW UP like `y^{1/e−1}` at a branch value; boundedness needs the root-of-unity cancellation `∑ᵢ ζ^{i(k+1)} = 0` — strictly harder |
| extra construction | covering lift `ℙ¹ → ℂ^g` (the #199 `simplyConnectedPrimitive` lift-and-Liouville pattern, `Topology/SphereSimplyConnected.lean` landed) + `MDifferentiable.exists_eq_const_of_compactSpace` (already used in `GenusZeroBackward`, `Elliptic/OneForm`) | path-lifting through the branched cover incl. endpoint behaviour at the (ramified) fibers over `0`/`∞`, smoothness (`IsSmoothPath`) of lifts in charts, + the bridging lemma B |
| `ℙ¹`-rigidity input | compactness + Liouville (landed pattern) | `H⁰(ℙ¹, Ω¹) = 0` + trace globalization |
| engine reuse | none needed (engine is the ⊆ direction) | E-vocabulary reused, but the engine itself is the WRONG direction (it produces `f` from chains; here we'd consume `f` to produce a chain) |

**Verdict: Route L stands.** Route C is not cheaper — it keeps every hard
ingredient of Route L's analysis, makes the removable-singularity step
strictly harder (no term-by-term boundedness shortcut), and adds branched
path-lifting chain construction. The #221 vocabulary does not change the
2026-06-07 conclusion. One Route-C artifact IS worth holding in reserve:
the **bridging lemma B** (any smooth 1-chain `c` with
`c.boundary = equivFinsupp D` gives
`divisorPeriodVector x₀ D ≡ (period(c, bridged ωᵢ))ᵢ mod Λ`) — it is a
~200-LOC reverse reading of the E6 adapter computation
(`devVal_trans`/`devVal_symm`/`devVal_bridgeArcPath`/
`devVal_loop_mem_periodLatticeInBasis`), is route-independent, and turns
ANY future zero-period bounding chain into a discharge. Not on the
critical path; pick it up only if Route L's S5 stalls.

## Rung ladder

New plumbing file: `Jacobians/RiemannSurface/AbelSupsetPlumbing.lean`
(below `Axioms/AbelTheorem.lean` in the import graph — the discharge will
convert the axiom in place, Phase-C pattern; the file must NOT import the
axiom, and kernel closures must show standard-3 + `AX_PeriodCycleBasis`
at most).

| Rung | Statement | Status |
|------|-----------|--------|
| **S1** (kernel converse, = R1) | `mem_abelJacobiDiv_ker_of_mem_lattice`: `deg D = 0` + `divisorPeriodVector x₀ D ∈ Λ` ⇒ `D ∈ (abelJacobiDiv X).ker` (converse of A1's `divisorPeriodVector_mem_lattice_of_mem_ker`, via `ulift_abelJacobiDiv_apply`); + reduction `abel_supset_of_principalPeriodVectorInLattice` over the named hypothesis `∀ f, divisorPeriodVector x₀ (divisor f) ∈ Λ` | **PROVEN** (this lane) |
| **S2** (fiber divisor, = R2a) | `fiberDivisor f hf y : Divisor X` (fiber of `toP1 f` weighted by `mapAnalyticOrderAt`) + `divisor_eq_fiberDivisor_zero_sub_infty`: `divisor f = fiberDivisor 0 − fiberDivisor ∞` for nonconstant `f` (coefficientwise from `toP1_eq_zero_iff` / `toP1_eq_infty_iff` / `mapAnalyticOrderAt_toP1*`) | **PROVEN** (this lane) |
| **S3** (Φ + constancy reduction) | `fiberAJ f hf : ProjectiveLine → Fin (genus X) → ℂ`-level or Jacobian-level `Φ(y) := abelJacobiDiv (fiberDivisor y)`; named hypothesis `FiberAJConstancy` (`Φ` constant); `abel_supset_of_fiberAJConstancy`. Needs the constant-`f` degenerate case `¬Nonconstant f ⇒ divisor f = 0` (de-privatize `orderAtMF_eq_zero_of_not_nonconstant` in `DegreeTheorem.lean`) | open (next) |
| **S4** (holomorphy off branch) | local holomorphic root functions of `toP1 f` off the branch locus (IFT / `AnalyticLocalMapping`); `Φ` locally = sum of `ofCurveAmbient`-developments along IFT tracks ⇒ holomorphic on `ℙ¹ ∖ B` | open |
| **S5** (removable across branch) | the load-bearing lemma: symmetric sum of endpoint integrals bounded near a branch value ⇒ holomorphic extension (`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) | open |
| **S6** (lift + Liouville) | `ℙ¹` simply connected (`Topology/SphereSimplyConnected`) ⇒ lift `Φ` through `ℂ^g → ℂ^g/Λ` (#199 `simplyConnectedPrimitive` pattern, Kirov `ZLatticeQuotient` local-homeo API); compact source ⇒ constant (`MDifferentiable.exists_eq_const_of_compactSpace` per coordinate / `Differentiable.exists_eq_const_of_bounded`) | open |
| **S7** (assembly) | `Φ(0) = Φ(∞)` + S2 + S1 ⇒ `AX_AbelSupset` becomes a theorem in place (Phase-C in-place conversion in `Axioms/AbelTheorem.lean`) | open |
| **B** (reserve) | chain↔lattice bridging (Route-C insurance, route-independent) | parked |

Critical-path risk concentrates in S4–S5 (the same analytic content as the
route doc's step 2–3). S1–S3 are assembly over landed toolkit.

## Lane log

- 2026-06-12: lane opened on `feat/abel-flip` base. Route refresh: Route L
  confirmed over the post-#221 direct-chain alternative (table above).
  S1 + S2 proven in `Jacobians/RiemannSurface/AbelSupsetPlumbing.lean`;
  kernel closures of the S1/S2 headline theorems verified standard-3 +
  `AX_PeriodCycleBasis` only (no `AX_AbelSupset` — no circularity).
