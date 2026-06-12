# AB-E route — the Forster §20 weak-solution engine (Abel ⊆, E-block)

*2026-06-12, AB-E lane (`feat/abel-engine`). Refines the E-block of
[`AB_ROUTE.md`](AB_ROUTE.md) into buildable rungs against the landed P-block
(PR #213, `AbelSubsetPairing.lean`) and the A-block plumbing (PR #211,
`AbelPlumbing.lean`). New Lean lives in
`vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/AbelSubsetEngine.lean`
(fresh Forster §20 against our substrate; ideas-with-citation only).*

## 0. The exact #211 contract (engine target)

PR #211 (`Jacobians/RiemannSurface/AbelPlumbing.lean`) consumes ONE named
hypothesis:

```lean
def ZeroPeriodChainSolvability (X) : Prop :=
  ∀ D : Divisor X, D ∈ (Divisor.deg X).ker →
    HasZeroPeriodLoopPresentation (Classical.arbitrary X) D →
    D ∈ PrincipalDivisors X
```

where (all ROOT-side vocabulary)

```lean
def HasZeroPeriodLoopPresentation (x₀ : X) (D : Divisor X) : Prop :=
  ∃ m : Fin (2 * genus X) → ℤ,
    divisorPeriodVector x₀ D =
      ∑ j, m j • periodMapInBasis X x₀ (jacobianBasis X)
        (loopToHomology ((pinnedCycleBasis x₀).loops j))
```

i.e. the vector of basepoint developing values `∑_P D(P)·∫_{x₀}^P ωᵢ` equals a
ℤ-combination of pinned-loop periods. Equivalently: the 1-chain

> `c := ∑_P D(P)·(arc x₀→P) − ∑_j m_j·(pinned loop j)`

has `∂c = D` (using `deg D = 0`) and **all g `jacobianBasis` periods exactly
zero** — Forster §20.1's hypothesis on the nose. Note: *exactly zero*, not
"in 2πiℤ" — the lattice part is absorbed into the chain by the loop terms.

**Match analysis / division of labour.** The engine (this lane, port-side)
cannot state #211's hypothesis: the port package cannot import root modules
(root `require`s the port, not vice versa). So:

* **Engine output (port vocabulary, this file's E5):** for a port
  `SmoothOneChain` `c` (ℤ-weighted `IsSmoothPath`s) with
  `lineIntegral α (each path)`-periods summing to `0` for **every**
  `α : HolomorphicOneForms X`: `∃ f : MeromorphicFunction X, f.div = c.boundary`
  (port `Divisor X = X →₀ ℤ`, port `MeromorphicFunction.div`).
* **Adapter (root-side `Jacobians/Bridge/`, the FINAL rung E6):** discharges
  `ZeroPeriodChainSolvability` from the engine output. Each translation brick
  already exists or is an E6 sub-rung:
  - basepoint arcs: `exists_smoothPath_family` / `smoothPath` (port
    `PeriodLattice.lean`) gives port paths `x₀ → P`; the value match
    `lineIntegral (bridged ωᵢ) (smoothPath x₀ P) = ofCurveAmbient x₀ P i` is the
    **open-path** analogue of `exists_isClosedSmoothLoop_lineIntegral_eq_developingValue`
    (`Bridge/KirovDolbeaultPeriods.lean`) — E6a, the one genuinely fresh bridge
    brick. (Direction: pick the port path FIRST, then evaluate the developing
    value along it via `developingValue`-vs-`lineIntegral` cell FTC,
    `lineIntegral_cell_eq_primitive_sub` — same architecture as the closed-loop
    proof, without the closing-up step.)
  - pinned loops: `exists_isClosedSmoothLoop_lineIntegral_eq_developingValue`
    **already lands this** (PROVEN, `KirovDolbeaultPeriods.lean:718`).
  - forms: `bridgeKDFormEquiv : HolomorphicOneForm X ≃ₗ HolomorphicOneForms X`
    + `genus_eq_kirovGenus`; `jacobianBasis` transports to a port basis, so
    "periods vanish on the bridged basis" + E1 ⟹ "periods vanish for all α".
  - divisors: root `Divisor X = FreeAbelianGroup X` vs port `X →₀ ℤ`
    (`FreeAbelianGroup ≃ X →₀ ℤ` is Mathlib's `FreeAbelianGroup.equivFinsupp`);
    port `f.div = D_port` ⟹ root `D ∈ PrincipalDivisors X` needs the port→root
    meromorphic-function + order faithfulness (AB_ROUTE A2; the
    `holToMero`-style Phase-D alignment) — E6b.

## 1. Route note: where the prompt's "third-kind + exp(∫ω)" picture lands

The classical Route-B chain (third-kind ω, correct periods into 2πiℤ by a
holomorphic form, `f = exp(∫ω)`) needs the second↔third-kind reciprocity to
control B-periods — the wall AB_ROUTE §1 rejected. The §20 engine **dissolves
both Route-B analytic layers**:

* **Period correction:** never happens on a meromorphic form. The chain
  carries the homology data and its periods are *exactly zero* (the loop part
  of `HasZeroPeriodLoopPresentation` is the correction, done root-side in #211
  by pure lattice algebra). What survives port-side is only the linear-algebra
  rung E1: vanishing on a spanning family ⟹ vanishing on all of `Ω¹(X)`.
  `pairPeriodL_surjective` (#213) enters only inside the already-proven P6,
  not in any fresh correction step.
* **Exponential well-definedness:** `f := F·exp(−u)` with `u` a GLOBAL
  single-valued smooth function (P6 output) and `F` the weak solution, built
  single-valued per arc as `exp(ψ·log)` in one disk (Forster 20.5). No
  developing-layer/homotopy-class argument is needed anywhere (the #199
  pattern stays in the genus-0 lane). Residue/2πiℤ bookkeeping is replaced by
  the local normal form `F = (unit)·z^{±1}` near each boundary point.

## 2. Rung ladder (port-side, `AbelSubsetEngine.lean`)

Difficulty: E ≤ 1 day, M = days, H = week+. Kirov §20-engine calibration
≈ 5.2k LoC total; multi-session block.

| rung | statement | diff | status |
|---|---|---|---|
| **E0** chain layer | `SmoothOneChain X`: finite ℤ-weighted family of `IsSmoothPath`s; `boundary : Divisor X` (Finsupp, `∑ᵢ nᵢ·((tgtᵢ) − (srcᵢ))`); `period α c := ∑ᵢ nᵢ·lineIntegral α (pathᵢ)`; `boundary` degree 0; period additive/ℂ-homogeneous in `α` (integrability from `velCont` via `intervalIntegrable_form_pathSpeed_of_velContinuous`) | E | **PROVEN this session** |
| **E1** zero-period extension | periods vanish on a spanning family of `HolomorphicOneForms X` ⟹ vanish for every `α` (the Route-A residue of "period correction"; consumed by E6's bridged-basis input) | E | **PROVEN this session** |
| **E2** `LogDbarDatum c` interface | bundling of the Forster 20.4/20.5 weak-solution output: smooth `F : X → ℂ` off `supp ∂c`, global `σ ∈ A^{0,1}`, fields: (i) `∂̄F = F·σ` off the support, (ii) local normal form `F = unit·z^{D(a)}` at each `a ∈ supp ∂c`, (iii) the pairing identity `pairOmega 𝔇 σ α = 2πi·period α c` (E4 as a FIELD — construction obligations live with the constructor E3/E4, consumers stay clean) | E (design) / — | **interface LANDED this session** |
| **E3** per-arc constructor | chart-disk subdivision of an `IsSmoothPath`; one-disk weak solution `exp(ψ·log((z−b)/(z−a)))` ≡ 1 off the disk (Forster 20.5); product/fold over the subdivision and the chain | H | **groundwork landed** (slit-segment log layer: `ratio_mem_slitPlane_of_notMem_segment`, `slitLogRatio` + `differentiableAt_`/`exp_slitLogRatio`, `isCompact_segment`); cutoff/gluing + fold open. W1's planar core also already in-tree: `differentiableOn_complex_of_dbar_eq_zero_local` (CechFinitenessBallSolve.lean:933) |
| **E4** pairing identity | `pairOmega 𝔇 σ_F α = 2πi·∫_c α` for the E3 datum (Forster 20.3/20.5: planar change of variables; contour↔Laurent brick `resAt_eq_planarCoeff_neg_one` landed in `TailFrameWitness.lean`) | H | open (discharged per-datum; E2 carries it as a field) |
| **E5** assembly | zero periods + E2 ⟹ `pairOmega σ α = 0` ∀α (E1 not even needed here if periods given for all α) ⟹ P6 `dbar_solvable_of_pairOmega_eq_zero` gives `u`, `f := F·exp(−u)`; `∂̄f = exp(−u)·(∂̄F − F·σ) = 0` off supp ⟹ holomorphic there; near `a`: `f = z^{D(a)}·(unit·e^{−u})` ⟹ `MeromorphicAt`, order `D(a)` ⟹ `f.div = ∂c` | M | **assembly THEOREM proven this session** over two named local-analysis walls (W1, W2 below) |
| **E6** adapter (root-side, separate Bridge file/PR) | E6a open-path developing↔lineIntegral; E6b divisor faithfulness; assemble `ZeroPeriodChainSolvability` | M/H | open |

### E5's named walls (no new axioms — hypotheses on the consuming theorem)

* **W1 `mero_of_dbar_vanish`** — a smooth `g : X → ℂ` with `∂̄g = 0` on a
  punctured neighbourhood of every point and the E2 normal form at the support
  is `IsMeromorphic`. Splits as: (a) ∂̄-kernel ⟹ chart-holomorphic on the open
  part (elliptic regularity is FREE here — `g` is already smooth, so this is
  just "Wirtinger ∂̄ = 0 + C¹ ⟹ ℂ-differentiable", Mathlib-adjacent); (b)
  removable singularity/`MeromorphicAt` from `z^n·(continuous unit)`
  (Mathlib `MeromorphicAt` + `Complex.differentiableOn_update_limUnder...`).
* **W2 `orderAt_of_normalForm`** — `orderAtPoint f a = n` when the chart-read
  of `f` is `z^n·h`, `h` continuous nonvanishing at `a`, holomorphic off `a`
  (port `Abel.lean` order machinery: `orderAtPoint_chart_invariant`, etc.).

Both walls are *local planar complex analysis with no surface topology* —
exactly the kind of brick this codebase discharges quickly; they are stated
as `Prop`-valued named hypotheses of `exists_meromorphic_of_logDbarDatum`
until their own sessions land them.

## 3. Order of work

1. ~~E0 + E1 + E2-interface + E5-assembly~~ (this session, kernel-clean).
2. W1/W2 (1–2 sessions; pure local analysis).
3. E3 (the long pole; chart-disk subdivision exists root-side as
   `ChartPartition`/`SquareSubdivision` patterns — port-side needs its own,
   over `IsSmoothPath`'s `velCont`).
4. E4 (per-arc, folded with E3's constructor — the E2 field discharges).
5. E6 adapter + `ZeroPeriodChainSolvability` discharge; #211's
   `abel_subset_of_engine` then yields Abel ⊆; with the Liouville ⊇,
   `AX_AbelTheorem := le_antisymm` closes tracker #14.

Kernel discipline (AB_ROUTE §3): every brick `#print axioms`-clean (standard 3
+ named hypotheses only); **no `AX_AbelTheorem` in any closure**; no new
`axiom` declarations.
