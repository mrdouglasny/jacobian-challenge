# AB route — Abel ⊆ (`AX_AbelTheorem`, kernel ⇒ principal), post-keystone

*2026-06-11, AB-lane (`feat/abel-subset`). Supersedes the pre-keystone route docs
[`ABEL_SUBSET_FORSTER_ROUTE.md`](ABEL_SUBSET_FORSTER_ROUTE.md) (third-kind/exponential,
2026-06-07) and the gating analysis in [`ABEL_WALL_GAP_ANALYSIS.md`](ABEL_WALL_GAP_ANALYSIS.md)
(2026-06-10), both written when RR/Serre were axioms. **They are theorems now**:
`exists_serreDualityData_cover` (KeystonePackaging.lean, unconditional, PR #201) and
`exists_riemannRoch_divisor` (RiemannRoch.lean, no isolated input). This doc re-derives the
route choice on that substrate and fixes the rung decomposition. If a parallel-account
fallback version of this file lands, reconcile here — the port-side engine work is this
lane's.*

## 0. Target

```
(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker  ≤  PrincipalDivisors X
```
(`Jacobians/Axioms/AbelTheorem.lean:80-83`): a degree-0 divisor with vanishing
Abel–Jacobi image is `div f` of a global meromorphic function. The ⊇ direction
(principal ⇒ AJ = 0) is the Liouville route (`ABEL_SUPSET_LIOUVILLE_ROUTE.md`);
**in-tree status at 67af290: route-vetted, not yet landed Lean** (no
`PrincipalDivisors X ≤ (abelJacobiDiv X).ker` declaration exists — the
2026-06-10 gap-analysis correction still stands). The two halves are independent;
nothing below consumes ⊇.

Substrate facts that fix the plumbing shape:

* `Jacobian X = ULift (ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ (jacobianBasis X)))`,
  `abelJacobiDiv = FreeAbelianGroup.lift (ofCurveImpl X x₀)`, `x₀ = Classical.arbitrary`.
  Kernel membership for a deg-0 `D` unfolds to: the vector of canonical arc integrals
  `∑_P D(P)·∫_{x₀}^P ωᵢ` lies in the pinned lattice = ℤ-span of the
  `AX_PeriodCycleBasis` loop periods. So the engine's input is a **1-chain with all
  g basis periods zero** — exactly Forster §20's `c` with `∂c = D`, `∫_c ωᵢ = 0`.
* Port genus `kirovGenus X = finrank ℂ (Jacobians.HolomorphicOneForms X)`; root
  `genus X = finrank ℂ (HolomorphicOneForm X)`; identified by
  `Bridge.bridgeKDFormEquiv` (Phase-D type alignment, already landed for the trace trio).

## 1. Route comparison

### Route A — Forster §20 ∂̄-engine, solvability criterion FROM SerreDualityData

The §20 program replaces all surface topology by ONE analytic criterion
(Forster 19.10): for a smooth (0,1)-form `σ`,

> `σ = ∂̄u` solvable  ⟺  `∫_X σ∧ω = 0` for every holomorphic 1-form `ω`.

**This criterion IS Serre duality for `H^{0,1}`**, and post-keystone its hard half is
free: `SerreDualityData` gives `h¹(𝒪) = g` (`data.arithmeticGenus`), the port's
`comparison_linearEquiv` (DolbeaultComparisonEquiv.lean:648, proven) transports it to
`finrank ℝ (DolbeaultH01 X) = 2g`, and then the criterion is a **dimension count**: the
period functional `Λ : A^{0,1} → ℂ^g`, `σ ↦ (∫σ∧ωᵢ)`, kills `im ∂̄` (Stokes), is onto
(positivity of the Hermitian Gram matrix `∫ ω̄ᵢ∧ωⱼ`), and an ℝ-linear surjection from a
2g-dimensional quotient onto a 2g-real-dimensional target is injective — so
`ker Λ = im ∂̄`. **No fresh cohomology is built; the keystone supplies the only deep
input (E3a, `h¹(𝒪)=g`).** Kirov's completed repo proves Abel-⊆ exactly this way
(`KIROV_ROUTE_IDEAS.md` item 1, files cited there; his §20 engine actuals ≈ 5.2k LoC).

Remaining genuinely fresh content: the global pairing `∫_X σ∧ω` (but the port's
FineResidue lane already has the PoU-planar global integral
`resIntegral : oneOneCoeff 𝔇 →ₗ[ℂ] ℂ` with integrability, smooth-PoU and planar-Stokes
atoms — FineResidue/{OneOneCoeff,Integral,Stokes}.lean — so this is a *constructor*, not
a theory), the Stokes kill, positivity, and the §20 weak-solution engine itself.

### Route B — third-kind differentials + exponential of the primitive

With RR a theorem, **third-kind existence is now nearly free** (pure `lDim`
arithmetic): `omegaDim (P+Q) = lDim (P+Q+K) = g+1 > g = omegaDim 0` via
`lDim_add_K_eq_omegaDim` (CanonicalFormIso.lean:605) + RR at `D = P+Q+K` +
`lDim_eq_zero_of_deg_neg`, so a form with a genuine (simple) pole among `{P,Q}` exists;
the unconditional residue atom (`exists_canonicalData_residueAtom`, FrameTrace.lean:941,
with `F = α/ω₀` via `meroFormDiv`) forces poles at BOTH with opposite nonzero residues.
The exponential well-definedness layer also exists now (the #199
developing-value/homotopy-class pattern from genus-0 backward).

**But the route still has the reciprocity wall**: relating the B-periods of the
normalized third-kind form to the Abel–Jacobi integrals requires (i) an A/B symplectic
cycle basis — on our substrate `AX_AnalyticCycleBasis`, an *axiom* — and (ii) the
second-vs-third-kind Riemann reciprocity — the load-bearing clause of
`AX_RiemannBilinear`, an *axiom*, whose proof needs the 4g-gon dissection PLUS a third
boundary word with meromorphic τ. Kirov's walls-plan evaluated exactly this and
**rejected it** ("third-kind + reciprocity require *more* polygon topology than the
4g-gon itself"); the dissection itself is our closure doc's hardest open item. So Route
B's bricks would close only *relative to two deep axioms* — disqualifying for an
axiom-free ⊆ campaign.

### Verdict

**Route A.** Criterion derived from `SerreDualityData` (not rebuilt), then the Forster
§20 weak-solution engine. Route B is the *reserve*; its one cheap rung (third-kind
existence) is worth banking anyway — it is also consumed by the Forster 21.4 lattice
program (B-4) and costs days, not weeks.

## 2. Rung decomposition (Route A)

Port-side files `vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/AbelSubset*.lean`
(fresh Lean from Forster §§19–20 against our substrate; ideas-with-citation only, per
the no-more-vendoring policy). Difficulty: E = easy (≤1 day), M = medium (days),
H = hard (week+).

### S — the dimension block (criterion skeleton)   [FIRST BRICKS]

| rung | statement | diff | status |
|---|---|---|---|
| S1 `exists_serreDualityData_chartDiskCover` | the ∃-cover keystone strengthened to exhibit a **ChartDiskCover** (both keystone legs already produce one; re-statement of `exists_serreDualityData_cover_of_genus_split_residueAtom`'s proof) | E | target — this session (AbelSubsetCriterion.lean) |
| S2 `h1Dim_zero_eq_kirovGenus` (at the S1 cover) | `data.arithmeticGenus` re-read | E | target — this session |
| S3 `finrank_real_dolbeaultH01_eq_two_mul_kirovGenus` | `dim_ℝ H^{0,1} = 2g`, intrinsic (E3a payoff): S1 + S2 + `cechH1_dolbeault_comparison_proof` | E | target — this session |
| S4 `mem_dbarImage_of_periodFunctional` | ABSTRACT criterion: any ℝ-linear `Λ : A^{0,1} → (Fin g → ℂ)` with `im ∂̄ ⊆ ker Λ` and `Λ` surjective has `ker Λ = im ∂̄` (descend to `DolbeaultH01`, S3 dim count, `LinearMap.injective_iff_surjective`-style finrank argument) | E/M | target — this session |

### P — the pairing block (realize Λ)

| rung | statement | diff |
|---|---|---|
| P1 `zeroOneCoeff` read | chart-coefficient family of `σ ∈ OneFormsZeroOne` with the `conj φ′` overlap law (mirror of `omegaCoeff`/`IsOneZeroCoeff`, FineResidue/SlotMatch + CupWitness patterns) | M |
| P2 `pairCoeff` constructor | (0,1)-family × holomorphic (1,0)-family → `oneOneCoeff 𝔇` member (`conj φ′ · φ′ = |φ′|²` Wirtinger algebra on the germ-eventual laws) | M |
| P3 `pairForm σ ω := resIntegral (pairCoeff …)` | ℝ-bilinear; independence of cover/PoU choices deferred — fix ONE canonical `𝔇` (the S1 cover) globally, as FineResidue already does | E |
| P4 `pairForm_dbarL` | Stokes kill `pairForm (∂̄u) ω = 0`: per-chart `integral_dbar_eq_zero` (FineResidue/Stokes.lean:99) + PoU telescoping (`pouSplit_telescope` pattern); Kirov actual 336 LoC | M/H |
| P5 `pairForm_conj_pos` → `pairPeriod_surjective` | `conjForm ω` as (0,1)-section; `pairForm (conjForm ω) ω ≠ 0` from pointwise `2|w|²`; Gram nondegeneracy ⟹ `Λ = (pairForm · ωᵢ)ᵢ` surjective | M |
| P6 `dbar_solvable_of_orthogonal_holomorphic` | Forster 19.10 assembled: S4 + P3-P5 | E |

### E — the weak-solution engine (Forster §20; Kirov C-0…C-5 calibration 5.2k LoC)

| rung | statement | diff |
|---|---|---|
| E1 `OneChain` layer | finitely many arcs with ℤ-coefficients over OUR piecewise-analytic arc algebra (`ArcAlgebra`, `canonicalArcIntegral`); `boundary : Divisor X`; `period ω` | M |
| E2 `WeakSolution D` | global smooth `f` locally `unit·(chart coord)^{D a}`; soundness lemma "`∂̄f/f` smooth ACROSS the divisor" | M/H |
| E3 per-curve solution | chart-disk subdivision of an arc; Forster 20.5 piece `exp(ψ·log((z−b)/(z−a)))`, `≡1` off the disk; fold | H |
| E4 `pairForm_logDbar_curve` | `Λ(σ_f) = ∫_c ω` (Forster 20.3/20.5; planar change of variables) — the E3b atom; the contour↔Laurent brick `resAt_eq_planarCoeff_neg_one` (TailFrameWitness.lean) is already landed | H |
| E5 `exists_meromorphic_of_oneChain` | zero periods ⟹ ∂̄-datum exact (P6) ⟹ `F := e^{−u}·G` meromorphic, `div F = ∂c`, WITH centred normal form | M/H |

### A — root-side plumbing (`Jacobians/RiemannSurface/`, `Jacobians/Extensions/`)

| rung | statement | diff |
|---|---|---|
| A1 kernel unfolding | `D ∈ ker(abelJacobiDiv) ⊓ deg-0` ⟹ a 1-chain (basepoint arcs − ℤ-combination of pinned loops) with `∂c = D`, all `jacobianBasis` periods 0. *Relative to the `AX_PeriodCycleBasis` pin (its `loops_to_basis` completeness field) — same conditionality as the rest of the Jacobian layer; flag in the audit row.* | M |
| A2 divisor bridge | port `MeromorphicFunction.div` ↔ root `MeromorphicFunctionField.divHom` / `PrincipalDivisors` (Phase-D type alignment; `holToMero`-style faithfulness both ways) | M |
| A3 `abel_subset` + retirement | assemble; `AX_AbelTheorem := le_antisymm ⊆ ⊇` once the Liouville ⊇ lands; close tracker #14 | E |

### TK — Route-B reserve brick (banked independently)

| rung | statement | diff | notes |
|---|---|---|---|
| TK1 `exists_form_with_pole` | `P ≠ Q` ⟹ `∃ α ∈ Ω(P+Q)` with a genuine simple pole (dim count `g+1 > g`) | E/M | also feeds lattice B-4 |
| TK2 `exists_thirdKind_form` | + poles at BOTH `P,Q`, residues `c, −c`, `c ≠ 0` (residue atom with `F = meroFormDiv α`) | M | |

## 3. Order of work & estimates

S-block (landed this session) → P-block (~1–2 wk) → E-block (~2–4 wk) → A-block (~1 wk),
TK interleaved as a breather. Total ≈ 4–7 wk of lane time, consistent with the
KIROV_ROUTE_IDEAS item-1 estimate (3–6 wk on shared atoms) now that E3a and RR are free.

Kernel discipline: every brick `#print axioms`-clean (standard 3 + explicitly named
hypotheses only); **no `AX_AbelTheorem` anywhere in any closure**; no new `axiom`
declarations — open inputs become named hypotheses on the consuming theorem, never
axioms.
