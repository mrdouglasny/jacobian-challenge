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
| **S3** (Φ + constancy reduction) | `fiberAJ f hf y := abelJacobiDiv X (fiberDivisor f hf y)` (the Jacobi pencil map, Jacobian-valued); named hypothesis `FiberAJConstancy`; `abel_supset_of_fiberAJConstancy` (`AJ(div f) = Φ(0) − Φ(∞) = 0`); degenerate case `divisor_eq_zero_of_not_nonconstant` (de-privatized `orderAtMF_eq_zero_of_not_nonconstant` in `DegreeTheorem.lean`); bonus `deg_fiberDivisor_const` (fiber-degree constancy in divisor form, for the S6 basepoint bookkeeping) | **PROVEN** (this lane) |
| **S4a** (branch values) | `branchValues f : Set ProjectiveLine` (finite, via `AX_BranchLocus`-the-theorem) + `mapAnalyticOrderAt_eq_one_of_not_branchValue` (regular fibers are unramified) | **PROVEN** (this lane) |
| **S4b** (local sections) | over `y₀ ∉ branchValues f`: `d` disjoint local holomorphic sections `sᵢ : V → X` of `toP1 f` through the fiber points (Wallace `IsHolomorphicAt.localInverse` + Mathlib `analyticAt_localInverse`; order-1 by S4a), with `fiberDivisor f hf y = ∑ᵢ of (sᵢ y)` near `y₀` (kfold uniqueness + properness) — `exists_fiberDivisor_sections` in `AbelSupsetSections.lean` | **PROVEN** (this lane) |
| **S4c** (pencil smoothness at regular values) | `contMDiffAt_fiberAJ`: `Φ = fiberAJ f hf` is `ContMDiffAt` at every `y₀ ∉ branchValues f` — REVISED ROUTE: no ambient lift; compose the proven `AX_ofCurve_contMDiff` (AJ is `ContMDiff ω` into the Jacobian) with the S4b sections through `map_sum` + the Jacobian `LieAddGroup` (`ContMDiffAt.sum`) | **PROVEN** (this lane) |
| **S5** (removable across branch) | `mdifferentiable_fiberAJ` (`AbelSupsetPencil.lean`): `Φ` is `MDifferentiable` on ALL of `ℙ¹` — S5a `eventually_fiberDivisor_cluster` (general kfold clustering at any value, prescribed neighborhoods) + `continuousAt_fiberAJ` (sumset-neighborhood brick `exists_nhds_zero_finsetSum_mem` + continuity of AJ) + S5b `mdifferentiableAt_of_continuousAt_of_eventually_mdifferentiableAt` (generic manifold-valued removable singularity via Mathlib `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` in the target chart) | **PROVEN** (this lane) |
| **S6** (lift + Liouville) | `fiberAJ_eq` / `fiberAJConstancy` (`AbelSupsetLiouville.lean`): `ℙ¹` simply connected (`simplyConnectedSpace_projectiveLine`, Kirov van-Kampen capstone for `OnePoint ℂ`); continuous lift through the lattice covering (Mathlib `IsCoveringMap.existsUnique_continuousMap_lifts`); the lift is holomorphic (`ComplexTorus.mdifferentiable_lift_of_mdifferentiable` — locally chart-composite + one lattice constant, discrete-subgroup isolation); constant by `MDifferentiable.apply_eq_of_compactSpace` ⇒ **`FiberAJConstancy X` HOLDS** | **PROVEN** (this lane) |
| **S7** (assembly) | **EXECUTED**: `AX_AbelSupset` is a `theorem` in place (`Axioms/AbelTheorem.lean`, statement verbatim, `abel_supset_of_fiberAJConstancy (fiberAJConstancy X)`); ledger 13 → 12, challenge-critical 2 → 1; full protocol run (audit/README/closure-doc/report regen/guard/verification log) | **DONE** (this lane) |
| **B** (reserve) | chain↔lattice bridging (Route-C insurance, route-independent) | parked |

Critical-path risk concentrates in S4–S5 (the same analytic content as the
route doc's step 2–3). S1–S3 are assembly over landed toolkit.

## Lane log

- 2026-06-12: lane opened on `feat/abel-flip` base. Route refresh: Route L
  confirmed over the post-#221 direct-chain alternative (table above).
  S1 + S2 proven in `Jacobians/RiemannSurface/AbelSupsetPlumbing.lean`;
  kernel closures of the S1/S2 headline theorems verified standard-3 +
  `AX_PeriodCycleBasis` only (no `AX_AbelSupset` — no circularity).
- 2026-06-12 (same session): S3 proven — `fiberAJ`, `FiberAJConstancy`,
  `abel_supset_of_fiberAJConstancy` (closure: standard-3 +
  `AX_PeriodCycleBasis`), degenerate case + `deg_fiberDivisor_const`
  (standard-3 only). `AX_AbelSupset` is now reduced to EITHER named
  hypothesis: `PrincipalPeriodVectorInLattice` (ambient form, S1) or
  `FiberAJConstancy` (Jacobian form, S3). Next: S4 (pencil holomorphy off
  the branch locus — the analytic core).
- 2026-06-12 (same session): S4a proven — `branchValues` +
  `branchValues_finite` + `mapAnalyticOrderAt_eq_one_of_not_branchValue`
  (closures standard-3 only). S4 decomposed into S4a/S4b/S4c in the
  ladder; the next rung is S4b (local holomorphic sections over a regular
  value — the first genuinely analytic step).
- 2026-06-12 (SUP-2 session): S4b proven — new file
  `Jacobians/RiemannSurface/AbelSupsetSections.lean`:
  local-inverse API upgrades (`IsHolomorphicAt.localInverse_apply_self`,
  `localInverse_tendsto`, `contMDiffAt_of_isHolomorphicAt_of_continuousAt`;
  two DegreeOneGenusZero helpers de-privatized), single-point section
  `exists_section_at`, and the headline `exists_fiberDivisor_sections`
  (sections through every fiber point over a regular value + eventual
  fiber-divisor trivialization `fiberDivisor f hf y = ∑ᵢ of (sᵢ y)`).
  Kernel closures: ALL standard-3 only (no `AX_PeriodCycleBasis` even).
  Note for S4c: with `AX_ofCurve_contMDiff` a THEOREM, S4c can compose
  `ofCurve`-smoothness with the S4b sections directly in the Jacobian
  (no ambient chart-lift needed): `fiberAJ` is `ContMDiffAt` at every
  non-branch value via `map_sum` over the section trivialization.
- 2026-06-12 (SUP-2 session): S4c proven on the revised (Jacobian-valued)
  route — `contMDiffAt_fiberAJ` in `AbelSupsetSections.lean`. Kernel
  closure: standard-3 + `AX_PeriodCycleBasis` (inherited from
  `ofCurveImpl`). S5 decomposition (next): S5a continuity of `fiberAJ`
  at ALL values (general kfold clustering + sumset-neighborhood lemma in
  the topological group `Jacobian X`); S5b generic removable-singularity
  for manifold-valued maps (`MDifferentiableAt` from `ContinuousAt` +
  punctured-nbhd `MDifferentiableAt`, via `mdifferentiableAt_iff_of_mem_source`
  charts + Mathlib `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  in the Jacobian chart — no explicit `ℂ^g` lift needed at S5);
  then `mdifferentiable_fiberAJ` everywhere. The explicit lift through
  `ℂ^g → ℂ^g/Λ` is needed only at S6 (Liouville).
- 2026-06-12 (SUP-2 session): S5 PROVEN — `AbelSupsetPencil.lean`:
  `exists_nhds_zero_finsetSum_mem` (sumset brick, standard-3),
  `mdifferentiableAt_of_continuousAt_of_eventually_mdifferentiableAt`
  (S5b generic removable singularity, standard-3),
  `eventually_fiberDivisor_cluster` (S5a clustering, standard-3),
  `continuousAt_fiberAJ` + `mdifferentiable_fiberAJ` (standard-3 +
  `AX_PeriodCycleBasis`). The pencil map is holomorphic on all of `ℙ¹`.
  Remaining: S6 (lift through `ℂ^g → ℂ^g/Λ` over simply connected `ℙ¹`
  + Liouville per coordinate ⇒ `FiberAJConstancy`), then the S7 flip.
- 2026-06-12 (SUP-2 session): S6 PROVEN — `AbelSupsetLiouville.lean`:
  `simplyConnectedSpace_projectiveLine` (standard-3, Kirov van-Kampen
  capstone), `ComplexTorus.mdifferentiable_lift_of_mdifferentiable`
  (standard-3, generic), `fiberAJ_eq` + `fiberAJConstancy` (standard-3 +
  `AX_PeriodCycleBasis`). GOTCHA recorded in the file header: the vendor
  `KirovDolbeault.ProjectiveLine` carries a competing
  `ChartedSpace ℂ (OnePoint ℂ)` instance; the vendor package must be
  imported BEFORE the main package modules so the main `ProjectiveLine`
  instances win resolution. Next: the S7 in-place flip of
  `AX_AbelSupset`.
- 2026-06-12 (SUP-2 session): **S7 EXECUTED — `AX_AbelSupset` is a
  THEOREM.** In-place conversion in `Axioms/AbelTheorem.lean`
  (statement verbatim; proof `abel_supset_of_fiberAJConstancy
  (fiberAJConstancy X)`). Kernel: `AX_AbelSupset`, `AX_AbelTheorem`,
  `Jacobian.ofCurve_inj` all standard-3 + `AX_PeriodCycleBasis`; full
  `lake build` green; `scripts/check_axiom_consistency.sh` ✓ at 12.
  Ledger: 13 → 12 axioms, challenge-critical 2 → **1**
  (`AX_PeriodCycleBasis` alone). Artifacts: AXIOM_AUDIT.md (header,
  Class-1 row, Recently-discharged row, by-class table, verification
  block), README.md (at-a-glance + topic table),
  docs/CHALLENGE_AXIOM_CLOSURE.md (status note + Cluster B),
  docs/axiom-report.txt regenerated,
  docs/planning/ABEL_FLIP_VERIFICATION.log (SUP section). The lane is
  COMPLETE: every rung S1–S7 proven on one route, no new axioms, no
  sorries.
