# Kirov route ideas — comparison against our seven open items (2026-06-11)

**Provenance & policy.** Read-only mining pass over `rkirov/jacobian-claude` at HEAD
`88b113e` (2026-06-11), cloned to `/tmp/kirov-current`, diffed against our vendored
base `4437c2b` (2026-06-09, the Phase-D Dolbeault-port snapshot at
`vendor/kirov-dolbeault-port/`). Per owner policy this document carries **ideas with
citation only — no code from the new clone enters our tree**. File pointers below
reference *his* tree (cite as `rkirov/jacobian-claude@88b113e:<path>`); any future
re-vendoring of post-`4437c2b` material is a separate owner decision, not taken here.

**Headline context.** Kirov's repo is now **COMPLETE**: sorry-free, zero custom
axioms, every v0.4 challenge declaration `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`), conformance machine-checked
(`ChallengeConformance.lean` + leaderboard form). The endgame (~16k LoC: RR
re-route + Abel converse + period lattice + primitives/monodromy) landed in roughly
**three days of parallel agent relays** (plan docs dated 06-09/06-10, retro 06-11).
His two books-first plan docs are the best single sources for the routes:
`docs/rr_close_plan_2026-06-09.md` and `docs/walls_bc_plan_2026-06-10.md`; the
project retro is `docs/RETRO.md`. Every one of our 6 challenge-critical axioms now
has a *proven counterpart* (or a proof that the axiom's content is unnecessary) in
his tree.

**Crucial structural fact for us:** `TraceForm.lean` and `TracePullback.lean` are
**unchanged since `4437c2b`** — the entire preimage-cycle / trace machinery behind
item 7 is *already in our vendored port*. All genuinely new work (the Abel engine,
the Laurent-tail Serre duality, the residue–Stokes atoms, the dissection-free
lattice, the primitives/monodromy files) is post-base, i.e. **not** in our port,
and is covered here as route ideas only.

Diff summary vs `4437c2b` (additions, ~18.0k LoC): Abel engine cluster ~5.2k
(15 files `Jacobians/Abel*.lean`), Laurent-tail Serre/RR tower ~4.4k
(`Jacobians/LaurentTail/`), residue–Stokes atoms ~3.7k (11 files under
`Jacobians/Dolbeault/`), Čech `h¹(𝒪)=g` trio ~0.7k, primitives/monodromy ~1.1k,
dissection-free period lattice ~1.4k; deletions ~6.7k = the abandoned §17
Čech-pairing program (`CechModel*`, `MeromorphicCousin*`, `GluedDbarDatum`,
`SerreResiduePairing`, …).

---

## 1. Abel ⊆ direction / `abelJacobi_twoPoint_ne_zero` (our `AX_AbelTheorem`, issue #14)

### His route — Forster §20 weak solutions (the "Abel engine"); NOT third-kind forms, NOT Jacobi inversion

He explicitly evaluated and **rejected** the Miranda/G–H polygon route (third-kind
differentials + reciprocity require *more* polygon topology than the 4g-gon itself:
a third boundary word with meromorphic τ plus punctured-surface H₁ generation —
`docs/walls_bc_plan_2026-06-10.md`, "Verdict on key question (a)"). Jacobi
inversion appears nowhere. The route is Forster 20.1–20.7: replace all surface
topology with one ∂̄-solvability criterion (Forster 19.10).

Decomposition (phases C-0…C-5 of the walls plan; all files post-base):

* **C-0 chains** — `Jacobians/AbelChains.lean`. `structure OneChain` (finitely many
  curves `ℝ → X` continuous on `[0,1]`, ℤ-coefficients), `OneChain.boundary : Divisor X`
  (signed endpoint Finsupp), `OneChain.period` via the *discrete* path value.
  Bridges: `pathPrimValue_eq_lineIntegral` (:128) on smooth paths;
  `exists_oneChain_of_abelJacobi_eq_zero` (:251) — `abelJacobi (P−Q) = 0` unfolds to
  a chain `smoothPath P₀ P − smoothPath P₀ Q − ∑ nₖ λₖ` with **all basis periods 0**.
* **C-1 weak solutions** — `AbelWeakSolutions.lean`. `structure WeakSolution D`:
  global smooth `f` locally `unit · (chart coord)^{D a}` with nonvanishing smooth
  unit; products, ℤ-powers; the soundness-critical lemma "`∂̄f/f` is smooth ACROSS
  the divisor" (`= ∂̄ψ/ψ` locally) is a named lemma, exactly as his plan's
  soundness-guard demanded.
* **C-2 per-curve solution** — `AbelPlanarPiece.lean` (698 LoC),
  `AbelPieceSolution.lean`, `AbelCurveSolution.lean`. Chart-disk subdivision of a
  curve; the explicit Forster-20.5 piece `exp(ψ · log((z−b)/(z−a)))` (bump ψ),
  `= 1` off the disk; `CurveWeakSolution` folds the pieces.
* **E3b the ONE integration atom** — `AbelPairing.lean` + `AbelPairingStokes.lean`.
  Global pairing `pairForm η g := ∑_j ∫ (PoU-cutoff chart reads)` over the fixed
  chart cover (a PoU-planar `∬_X σ∧ω`, never a manifold 2-form theory);
  `pairForm_dbarL` (:336, Stokes kill `Λ(∂̄u) = 0`, per-chart planar Stokes +
  telescoping) and `pairForm_logDbar_curve` (`AbelEngineSigma.lean:305`,
  `Λ(σ_f) = ∫_c ω` — the Forster 20.3/20.5 identity, planar change of variables).
* **E3c positivity** — `AbelPairingPositivity.lean`: conjugate forms `conjForm` as
  (0,1)-sections; `pairForm_conjForm_ne_zero` (:143) from pointwise `2|w|² ≥ 0`.
* **E3a `h¹(𝒪) = g`** — see item 4 below (his C-4 crux).
* **E3d the ∂̄-kill (Forster 19.10)** — `AbelDbarKill.lean`:
  `finrank_dolbeaultH01 : finrank ℝ (DolbeaultH01 X) = 2g` (:227, via the *base*
  port's `comparison_linearEquiv` + item 4), `pairMatrix_det_ne_zero` (:86),
  `exists_dbarL_eq_of_pairForm_eq_zero` (:237): `Λ[σ] = 0 ⟹ σ = ∂̄u` by a
  dimension count (Λ surjects onto ℂ^g from a 2g-dimensional space whose kernel is
  exactly the ∂̄-image).
* **C-5/E4 the engine** — `AbelEngineSigma.lean`
  (`exists_dbar_potential_of_oneChain` :392: zero periods ⟹ the weak solution's
  ∂̄-datum is exact) and `AbelEngineMeromorphic.lean:72`:

  > `exists_meromorphic_of_oneChain (c : OneChain X) (hper : ∀ i, c.period ωᵢ = 0) :`
  > `∃ f : MeromorphicFunction X, f.div = c.boundary ∧ (centred local normal form`
  > `f̂ = H·(w−w₀)^{∂c(a)} at every point, H analytic nonvanishing)`

  via `F := e^{−u}·G`; the normal-form payload is what B-4 (item 5) reads residues
  from.
* **Headline** — `AbelFinal.lean:49` `abelJacobi_twoPoint_ne_zero`: engine ⟹
  `div f = P − Q` ⟹ single simple pole ⟹ `X ≃ₜ S²` ⟹ `genus X = 0`, contradiction.

**Scope note.** He proved only the challenge-scoped two-point nonvanishing. But the
engine is stated for **arbitrary** chains/divisors, so the full ⊆ direction of our
`AX_AbelTheorem` (`ker(abelJacobiDiv) ∩ deg-0 ⊆ Principal`) is engine + plumbing
(unfold an arbitrary kernel element to a zero-period chain). The ⊇ direction
(principal ⟹ AJ = 0) is **not in his tree** — our Liouville route
(`docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`) remains our own and is unaffected.

### Our independent implementation

Against our substrate: our `abelJacobiDiv` lives over the H1-quotient model with
`AX_PeriodCycleBasis`; the C-0 unfolding step becomes "kernel membership ⟹
finite ℤ-combination of the bundle's loops periods" — directly available from the
`loops_to_basis` pin. The big-ticket inputs E3a–E3d consume exactly the Dolbeault
package **already in our port** (`DolbeaultH01`, `comparison_linearEquiv`,
`dbar_solvable_open_disk`, `chartDiskCover`, skyscraper machinery) plus the two
post-base towers we'd build fresh from the books: the residue–Stokes atoms
(Forster 10.20/10.21 planar, ~2–3k LoC) and the `h¹(𝒪)=g` count (item 4). Engine
proper ~4–6k LoC fresh (Forster §20, his actuals 5.2k as calibration). Our
arc-integral layer (piecewise-analytic arcs) substitutes for his
`pathPrimValue`/`lineIntegral` bridge; item 6's monodromy toolkit is the shared
prerequisite.

### Estimate & verdict

Our current plan rates the ⊆ half "the hard half (Jacobi inversion)", i.e.
research-grade gated on the full RR/Serre tower. Kirov's route demotes it to a
**bounded engineering program**: ~8–12k LoC over our port (engine + atoms + h¹
count), realistically **3–6 weeks** of agent relays given his 3-day actuals on a
hot substrate and our colder one. **Verdict: ADOPT-ROUTE** (for ⊆; keep our
Liouville ⊇ as is). This also banks the engine that items 4 and 5 consume.

---

## 2. `HasHolomorphicPrimitives` / `genus_eq_zero_iff_homeo` backward (issue #15)

### His route — discrete monodromy, no de Rham, no covering spaces, no integration

Backward direction (`X ≃ₜ S² ⟹ genus 0`), decomposition:

1. **S² simply connected, unconditionally** — a from-scratch **two-open
   Seifert–van Kampen** for π₁ (`Jacobians/VanKampen.lean:402`
   `twoOpenVanKampen_holds`; Mathlib has no SVK): Lebesgue subdivision of a loop
   over the two charts, spokes through the path-connected overlap, conjugation
   cancellation; side conditions in `SphereSimplyConnected.lean` (two-chart cover of
   the one-point compactification). Both files predate our vendored base — check
   the port before rebuilding.
2. **Transport** simple connectivity across the homeomorphism
   (`GenusSphereBackward.lean:92-106`).
3. **The holomorphic Poincaré lemma** — `HolomorphicPrimitives.lean:242`
   `hasHolomorphicPrimitives : HasHolomorphicPrimitives X`: define
   `F x := pathPrimValue η (somePath x₀ x)`; well-defined by monodromy (item 6);
   locally `F = local primitive + const` via
   `pathPrimValue_trans_primitive_block` (the chain of a concatenation = half-scaled
   chain + one disk block); `MDifferentiable` with `dF = η` via
   `EventuallyEq.mfderiv_eq`. The supporting stack is
   `HolomorphicPrimitiveLocal.lean` (`IsLocalPrimitiveOn`, existence on chart disks,
   "two primitives differ locally by a constant"), `HolomorphicPrimitiveChain.lean`
   (`PrimitiveChain`: partition `t k` + per-block primitives; chain-independence of
   the value), `HolomorphicPrimitiveMonodromy.lean` (item 6).
4. **Liouville step** — `GenusZeroOfSphere.lean:99`
   `holomorphicOneForm_eq_zero_of_hasPrimitive`: a global primitive on compact
   connected X is constant (Mathlib's
   `MDifferentiable.exists_eq_const_of_compactSpace`), so `η = 0`; hence
   `genus = finrank Ω = 0`.

Forward direction (for completeness): RR at a point gives `l(P) = 2` ⟹ single
simple pole ⟹ degree-1 map ⟹ `X ≃ₜ S²` (`GenusSphereHeadline.lean:43`,
`DegreeOneSphere.lean` — the degree-one endgame largely predates our base).
Forward consumes RR, i.e. his unconditional tail-RR (item 3/4 tower).

### Our independent implementation

Our `AX_genus_eq_zero_iff_homeo` is the full iff. The backward half is the
self-contained part: van Kampen + sphere files (audit the port first — likely
already present at `4437c2b`), then primitives/monodromy over OUR chart-primitive
layer (the PR #179 chart-line descent built `localLift`-grade assets we can reuse),
then the Liouville step (Mathlib API, direct). The forward half should be scheduled
*after* a tail-RR decision (item 3), since `exists_riemannRoch_divisor` is its only
deep input; our Wallace GenusZero/degree-one material covers the
single-pole ⟹ homeo endgame.

### Estimate & verdict

Backward: ~1.5–2.5k LoC fresh (his post-base actuals: 1.1k primitives/monodromy;
van Kampen predates base), **1–2 weeks**. Forward: days of assembly once RR is a
theorem in our tree (else stays conditional). **Verdict: ADOPT-ROUTE** (backward
now; forward gated on the item-3 decision). This is strictly stronger than our
Wallace-progress note in `docs/CHALLENGE_AXIOM_CLOSURE.md`.

---

## 3. §17.7 unwind + §17.9 pole-bound regularity (our `UnwindRegularity`, `R6D2_BLOCKER.md` §2)

### His route — there is no §17.7/§17.9 in the final proof; the whole §17 program was deleted

The decisive fact: his final Serre duality **abandons the Čech §17 residue-pairing
program entirely** (≈6.7k LoC deleted: `CechModel*`, `MeromorphicCousin*`,
`GluedDbarDatum`, `SerreResiduePairing`, `GlobalResidueConstruct`, …; see
`docs/RETRO.md` "Hardest"). Serre duality is re-proved at the **Laurent-tail
level** (Miranda Ch. VI): `H¹(D) := coker(α_D : ℳ(X) → 𝒯[D](X))` on tail
*polynomials*, residue functional = finite Laurent-coefficient algebra, descent via
the (Stokes-proven, unconditional) `∑Res = 0`.

Where our two R6D2 §2 walls go in his model:

* **"The bad point is forced, not chosen"** — *dissolves*. The Miranda Lemma 3.6
  analogue is `pairOrderBounded_of_vanishing`
  (`Jacobians/LaurentTail/PairDualitySurjective.lean:261`):

  > if the residue functional of `h·dg₀` (defined at fine level `D'`) vanishes on
  > every `D'`-tail killed by the `D`-truncation, then `h·dg₀` satisfies the
  > coarser bound `D`.

  Proof = the **single-monomial witness** `Finsupp.single (p, −1−o) 1` pairing to
  the nonzero leading Laurent coefficient. The higher-order-pole evaluation that
  forced our Cauchy–Pompeiu derivative ladder is, in the tail model, *by
  definition* a coefficient read — no cover, no isolated-point refinement, no
  `MLIsolated`, no integration.
* **"Level bookkeeping at `E` of arbitrary sign"** — *dissolves*. Tail membership
  at negative divisor entries is a support/degree condition on a Finsupp
  (`tailSubspace`, `TailSpace.lean`), not holomorphy-with-zeros on cover overlaps.

The rest of the surjectivity half: `pairDualMap_recovery` (:321, pull a functional
back along `μ_ψ`; the composite of multiplication and truncation identities W1/W2)
and `pairDualMap_surjective` (:435, the growth-rate pigeonhole on `H¹(D−nP)*` using
RR-I dimension counts) — both shapes his plan correctly predicted match our
already-proven abstract `serre_surjectivity_dim_core` style. Output:
`h1TailDim_eq_lDim_pairCanonical_sub : h¹(D) = l(K−D)` for `K = div(dg₀)` — **no
genus hypothesis anywhere** (pair frame over any nonconstant meromorphic `g₀`).
The Čech tower is kept *below* as the M-bound supplier
(`riemannRoch_inequality`, in our port) — "the bridge between the towers".

### Our independent implementation

Our `UnwindRegularity` isolation (`docs/planning/R6D2_BLOCKER.md` §2) is the exact
pain his deletion log predicts. Recommendation: **do not discharge UnwindRegularity
as stated** — re-point our keystone (`exists_serreDualityData` /
`serreDuality_equiv`) at a Laurent-tail duality engine built fresh from Miranda
Ch. VI over our port's `linearSystem`/`lDim`/principal-part APIs: tail algebra
(~1–1.5k), residue functional + descent (~1k, consuming a pair-frame `∑Res = 0` —
the same atom as item 4), injectivity witness + Lemma 3.6 + recovery + pigeonhole
(~1.5–2k). His full tower actuals: 4.4k LoC. The banked R6D2 D2a/D2b engines stay
as archival theorems, same as his banked CutSurface files.

### Estimate & verdict

Our R6D2 plan's next steps were "higher-order Cauchy–Pompeiu atom, then
forced-point refinement, then UnwindRegularity" — all three are *unnecessary* on
the tail route. Fresh tail tower over our port: ~4–5k LoC, **2–4 weeks**, mostly
LOW-risk Finsupp/dimension bookkeeping (his rr-plan's 80% estimate held up).
**Verdict: ADOPT-ROUTE** — retire the UnwindRegularity lane (and the
`CupMLWitnessR` construction of R6D2 §1) rather than complete it.

---

## 4. `h¹(𝒪) = 0` at genus 0 (our `hga`, `G0_BLOCKER.md`)

### His route — `h¹(𝒪) = g` uniformly in genus; no Hodge, no Dolbeault-vanishing, no uniformization

`FiniteCover.h1Dim_zero_eq_genus` (`Jacobians/Dolbeault/CechH1Genus.lean:120`,
Miranda Prop. X.2.6 GAGA-free), with **no genus split**, so `g = 0` gives `hga`
outright. Three steps:

1. **Čech vanishing at large `A`** — `exists_effective_h1Incl_eq_zero`
   (`CechH1CupKill.lean:224`): for each basis class of the finite-dimensional
   `H¹(𝒪)`, a cup-multiplication pigeonhole produces an effective `Aᵢ` killing it;
   `h1Incl_surjective` (`CechH1Monotonicity.lean:153`, Forster 16.8 via the
   skyscraper LES — machinery in our port) makes `H¹(𝒪) → H¹(𝒪_A)` zero AND
   surjective, so `H¹(𝒪_A) = 0` for `A := ∑Aᵢ + m·P`.
2. **Tail vanishing at the same `A`** — choose `m > deg K` for the pair-frame
   `K = div(dg₀)`; tail Serre duality (item 3) gives
   `h¹_tail(A) = l(K−A) = 0` (`lDim_eq_zero_of_deg_neg`).
3. **Subtract the two RRs at `A`** — cohomological RR (skyscraper-χ, in our port)
   gives `l(A) = deg A + 1 − h¹(0)`; tail RR
   (`riemannRoch_tailForm` + `h1TailDim_zero_eq_genus_unconditional`,
   `LaurentTail/RiemannRochUnconditional.lean:53`) gives `l(A) = deg A + 1 − g`;
   hence `h¹(0) = g`.

The genus-0 enabler is exactly our `G0_BLOCKER.md` "plausible discharge shape 1"
(meromorphic-frame residue functional), realized: the unconditional pair-frame
residue theorem `residueSum_pairForm_mul_eq_zero_unconditional`
(`Dolbeault/ResidueTheoremStokes.lean:780`), proved by classical Stokes atoms —
planar compact-support Stokes (`PlanarCompactSupportStokes.lean`, seeded from
Wallace's MIT rectangle Green's theorem, credited in-file), radial pole bump
(`ResidueStokesPoleBump.lean`), PoU off the poles (`ResidueStokesCoverPoU.lean`),
annulus atoms (`AnnulusResidue*.lean`) — **uniform in genus**, no `ω₀ ∈ Ω(X)`
needed. His G0 equivalents of our circularity worries simply never arise: nothing
in the chain consumes `exists_serreDualityData` or uniformization.

### Our independent implementation

This is the direct discharge plan for `hga` (and it simultaneously feeds our
keystone's `g = 0` leg `exists_serreDualityData_of_arithmeticGenus_zero`, making
the keystone equation `hpos + hga` collapse to `hpos`). Inputs from our port:
skyscraper LES, `h0Dim_eq_lDim`, `cohomological_riemannRoch`,
`riemannRoch_inequality`, `exists_nonconstant_meromorphic`. Fresh: the
Stokes-atom tower (~2.5–3.5k, shared with item 1's E3b), the tail tower (item 3),
the monotonicity/cup-kill trio (~0.7k).

### Estimate & verdict

Our G0 doc rates `hga` "research-grade today" with three speculative shapes;
Kirov's tree confirms shape 1 end-to-end with a concrete lemma decomposition.
Incremental cost *on top of items 1/3* (which share the atoms and tails): ~1k LoC,
**days**; standalone: ~2–3 weeks. **Verdict: ADOPT-ROUTE.**

---

## 5. Period lattice without dissection — Forster 21.4 (our Cluster A / `AX_PeriodCycleBasis`)

### His route — confirmed; B-1…B-5 details for our reimplementation briefs

The owner's summary is verified; the decomposition is five phases, with the
critical dependency reversal **the lattice theorem CONSUMES the Abel engine
(B-4 ← C-5), not a homology basis**. `CutSurface`/dissection/R1/R2 were retired
unbuilt ("the worst wall … was never built", `docs/RETRO.md`).

* **B-1** `JacobiBasePoints.lean` (Forster 21.3): `formEvalSelf a` (chart-centre
  coefficient functional); `exists_finset_formEvalSelf_ker` (induction dropping
  the kernel intersection dimension by one per point);
  `exists_jacobiBasePoints_det_ne_zero` (:194): `g` points + invertible `g×g`
  evaluation matrix `jacobiEvalMatrix a`.
* **B-2** `JacobiLocalMap.lean` (21.4a): `jacobiMap a z i = ∑_j Φ̃_{a j, i}(z j)`
  (chart-coordinate primitives `localLiftChart`); strict Fréchet derivative
  assembled by hand from one-variable `HasStrictDerivAt`
  (`jacobiMap_hasStrictFDerivAt` :152); IFT openness
  `jacobiMap_map_nhds : map G (𝓝 center) = 𝓝 0` (:205) via
  `HasStrictFDerivAt.map_nhds_eq_of_equiv` — Mathlib only, no manifold IFT.
* **B-3** `PeriodLatticeNondegenerate.lean` (21.4c):
  `span_real_truePeriodLattice_eq_top` (:108). Shape: a real functional killing the
  lattice is `Re⟨d,·⟩` (`exists_re_dotProduct_repr`); `u(x) := Re ∑_j d_j ·
  periodVec(somePath x₀ x)_j` is well-defined (two smooth paths differ by a loop
  period, killed by hypothesis) and locally `Re ∘ (analytic H)`; at a max
  (compactness), Mathlib's **open-mapping dichotomy**
  (`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`, packaged as
  `eventually_const_of_re_le` :40) forces local constancy; clopen ⟹ `∑ d_j ω_j = 0`
  ⟹ contradiction. **No harmonic theory, no surface integration.**
* **B-4** `PeriodLatticeDiscrete.lean` (21.4b):
  `truePeriodLattice_isolated_zero` (:120). Shape: nonzero `t = G(z) ∈ Γ ∩ W`;
  the chain (straight chart segments `a_j → x_j`, in pairwise-disjoint disks —
  `exists_pairwise_disjoint_opens` :87) minus the loop combination realizing `t`
  has all basis periods 0; the **engine** returns `f` with
  `div f = ∑ (x_j − a_j)` *plus the centred normal form*, so simple poles at the
  `a_j` have nonzero leading coefficients; the residue theorem on each `f·ωᵢ`
  (`resAt_analyticAt_mul_sub_inv` :45 + the pair-frame residue sum) yields
  `A·c = 0`, contradicting B-1.
* **B-5** `PeriodLatticeBasis.lean`: `DiscreteTopology` instance (:38) from
  isolated-zero; `IsZLattice ℝ` (:57) from B-3; then Mathlib ZLattice
  (`ZLattice.module_free`, `ZLattice.rank` = 2g, `Basis.ofZLatticeBasis` +
  `ofZLatticeBasis_span`) gives `exists_periodLattice_realBasis` (:66) verbatim;
  `g = 0` handled trivially.

**What this does and does not give vs `AX_PeriodCycleBasis`.** It gives:
discreteness, `IsZLattice`, rank 2g, and a ℤ-basis *of the lattice in ℂ^g* —
without dissection, without R1/R2, and (critically) with the lattice DEFINED as the
span of **all** closed-smooth-loop periods, so the lattice-completeness condition
(the X1/HI conditionality that PR #179 transferred into our `loops_to_basis` pin)
is **true by definition** on this model. It does NOT give: 2g distinguished
*loops* realizing the basis, the H₁/Hurewicz tie, or the Riemann bilinear
relations — his verdict (walls plan, "What this changes") is that R1/R2 are simply
**not needed by the challenge** once the lattice instance comes from 21.4; the
symplectic basis is "a consequence, not an input" (Forster 21.5 Remark).

### Our independent implementation

Two levels. (i) *Conservative*: keep `AX_PeriodCycleBasis` as the model and use
B-1/B-2/B-3 + engine as its discharge engine — but the axiom's `loops_to_basis` +
R1/R2 fields are stronger than what 21.4 produces, so a pure 21.4 discharge does
not close it as stated. (ii) *Restructure (recommended for discussion)*: re-point
the Jacobian's lattice at the full loop-period span (our `periodLatticeInBasis`
already sits over pinned loops; the move is to *derive* the pinned basis from the
ZLattice basis instead of axiomatizing loops), making the discreteness/rank/
completeness content a theorem and **eliminating the R2-Hodge wall** (the single
hardest barrier in `docs/CHALLENGE_AXIOM_CLOSURE.md`) plus the dissection topology
from the challenge-critical path. The H₁/Hurewicz tie then either becomes
non-critical Part-3 debt (like `intersectionForm` post-D1) or is re-derived later.
This is a Cluster-A-shaped major change ⟹ **needs a GitHub Discussion before any
PR** (per CLAUDE.md), and the satisfiability-vetting discipline applies to any
interface change.

### Estimate & verdict

His actuals: B-phases ~1.4k LoC, but B-4 consumes the Abel engine (item 1) and
the residue atoms. On our side, after items 1+4 land: ~1.5–2.5k LoC, **1–2 weeks**.
Without restructuring (level i) it shaves the basis/discreteness half of Cluster A
but leaves R1/R2 pinned. **Verdict: HYBRID** — adopt B-1…B-5 as the engine;
the model-level restructuring decision (drop R1/R2 + loops pin from the critical
path) goes to the owner/Discussion.

---

## 6. Homotopy invariance (our Fork-1 workstream / the X1 conditionality)

### His route — full endpoint-fixed HI, by discrete continuation; no developing map, no covering space, no integration

Yes — full HI is proven: `pathPrimValue_eq_of_homotopy`
(`Jacobians/HolomorphicPrimitiveMonodromy.lean:72`): for continuous
`H : ℝ → ℝ → X` (totalized via `projIcc`) with fixed endpoints, the discrete path
value of a holomorphic form along `H s` is constant in `s`. Proof shape (170 LoC
total, "one inline day" per the retro):

1. `PrimitiveChain` (item 2): partition + per-block local primitives; value
   chain-independent (`value_eq_of_chains`).
2. **Tube compactness**: for `s` near `s₀`, the SAME partition/primitive data is a
   chain for `H s` (`IsCompact.eventually_forall_of_forall_eventually`).
3. **Abel summation** (`sum_telescope_abel` :40): rewrite the value as fixed
   boundary terms minus interior-node defects `(F_k − F_{k−1})(H s (t_k))`.
4. Each defect is **locally constant in `s`** (two primitives differ by a constant
   on a path-connected neighbourhood — step-0 rigidity), so the value is locally
   constant on ℝ, hence constant.

Companions: `pathPrimValue_eq_of_homotopic` (`Path.Homotopic` version,
`HolomorphicPrimitives.lean:52`) and the smooth bridge
`pathPrimValue_eq_lineIntegral` / `…_eq_periodVec` (`AbelChains.lean:128-194`)
tying the discrete value to `lineIntegral`/`periodVec` on (closed) smooth paths —
so HI transfers to the genuine line integrals used by the lattice and Abel layers.

### Our independent implementation

Exactly the shape our un-parked Fork-1 needs: discrete monodromy over OUR
chart-primitive assets (PR #179's chart-line descent built `localLift`-grade
primitives; our arcs are piecewise-analytic, strictly nicer than his merely
continuous curves). Deliverables: `PrimitiveChain`-analogue over our arc partition
(the `U ∩ Icc` refinement discipline from `STRENGTHEN_ANALYTICARC.md` matches his
block structure), the tube + Abel-summation argument, and a bridge to our
`loopIntegralToH1`/`periodMap`. Note: if item 5's restructuring is adopted, HI's
*load-bearing* role shrinks (path discrepancies land in the full loop-period
lattice definitionally); HI remains valuable for basepoint-independence statements
and the Albanese layer.

### Estimate & verdict

~0.8–1.5k LoC, **under a week** given his one-day actual on a hot context.
**Verdict: ADOPT-ROUTE.**

---

## 7. Pushforward/pullback lattice naturality + projection formula (issues #30, #31, #34)

### His route — span-induction naturality + preimage-cycle trace identity + basis off-lattice extension

All three were resolved; crucially the heavy machinery **predates our vendored
base** (`TraceForm.lean`/`TracePullback.lean` unmodified since `4437c2b` ⟹ already
in `vendor/kirov-dolbeault-port/`):

* **#30-analogue (pushforward direction)** —
  `ambientPhi_preserves_truePeriodLattice` (`PeriodLattice.lean:856`):
  `Submodule.span_induction` over closed-loop generators; on a generator,
  `periodVec_pushforward` (`∫_{f∘γ} ω = ∫_γ f*ω`, proven period-map naturality) +
  `f ∘ γ` is again a closed smooth loop. Direction matches our
  `pushforwardAmbientLinear` = dual of the REAL `pullbackOneForm` (per our DT vet).
  ~40 LoC over the naturality lemma.
* **#31-analogue (pullback/trace direction)** —
  `ambientPullbackJac_preserves_truePeriodLattice` (`TracePullback.lean:2604`).
  Constant `f`: the trace is 0. Non-constant: the **preimage cycle**:
  `exists_loop_off_branchLocus` (:788 — homotope the loop off the finite branch
  locus *preserving* `periodVec`), `exists_monodromyLiftFamily` (:1821 —
  continuous fibre lifts off branch points), permutation orbit loops
  (`exists_orbitLoops_of_monodromyLiftFamily` :2390), packaged as
  `structure PreimageCycle` (:303) with fields
  `pullback_eq : Tᵀ·periodVec δ = ∑ coeffs·periodVec loopsᵢ` (driven by the trace
  identity `lineIntegral_traceFormTotal_eq_sum_periodVec` :2050) and
  `pushforward_eq : ∑ coeffs·periodVec(f∘loopsᵢ) = sheets·periodVec δ`.
* **#34 (projection formula)** — `ambientPhi_ambientPullback_eq`
  (`Jacobians.lean:590`, `f_* ∘ f^* = deg f • id` in ambient coordinates):
  (a) on a single `periodVec δ` from the cycle's two identities + **sheets =
  degree** (`exists_preimageCycle_sheets_eq_degree`, using degree
  well-definedness ported from Bryan Sanchez's `jacobian-lean-challenge` —
  third-repo prior art worth recording); (b) ℤ-extension to the lattice;
  (c) **off-lattice extension via the real period basis** (item 5's
  `exists_periodLattice_realBasis`): the composite is ℂ-linear and agrees with
  `deg • id` on an ℝ-basis. Then `ZLatticeQuotient.pushforward_pullback_of_ambient`
  (:630, in our port) descends to the torus.

### Our independent implementation

* **#30** can proceed **now** (consistent with `docs/CHALLENGE_AXIOM_CLOSURE.md`):
  span-induction over our lattice's generators + a `periodVec_pushforward`-analogue
  over our arc periods. In our basis-pinned lattice model, the image period is a
  general loop period of `Y`, whose membership in the pinned span is exactly the
  `loops_to_basis` completeness field of `AX_PeriodCycleBasis` — so #30 discharges
  *relative to the bundle*, cleanly. ~0.5–1k LoC, **about a week**.
* **#31**: audit whether the port's `TracePullback` preimage-cycle chain compiled
  into our build (the trace trio #26–28 bridged `traceFormTotal` already); if yes,
  this is bridge work (`Bridge/KirovDolbeaultTrace.lean` pattern) + the same
  span-induction; if the §3 lift chain was pruned from the port build, it is
  ~2.6k LoC of reimplementation. **1–3 weeks** accordingly.
* **#34**: assembly after #30/#31 — the keystone two-identity lemma is ~40 LoC of
  algebra; the off-lattice extension can run against the basis already supplied by
  `AX_PeriodCycleBasis` **today** (and silently upgrades when Cluster A is
  discharged). **Days** after #31.

### Estimate & verdict

**Verdict: ADOPT-ROUTE for all three** — and note this is mostly *activation of
machinery we already vendor* rather than new mathematics. Ordering: #30 now,
#31 after the port audit, #34 last.

---

## Cross-cutting observations

1. **Dependency re-wiring is the single biggest idea.** Forster's order — Abel
   sufficiency FIRST (∂̄/weak solutions), lattice SECOND (21.4 consumes the
   engine), bilinear relations NEVER (not challenge-needed) — inverts our Cluster-A
   plan, where the dissection/R1/R2 bundle gates everything. Adopting it removes
   the two items our closure doc calls hardest (R2 Hodge positivity; dissection
   topology) from the critical path.
2. **The shared atoms.** Three towers are consumed by 5 of the 7 items and should
   be built once, in order: (i) planar residue–Stokes atoms (~2.5–3.5k), (ii)
   Laurent-tail duality/RR (~4–5k), (iii) the Abel engine (~4–6k). Items 2b, 4, 5,
   and the RR-consumers then fall in days each.
3. **His misformalization lesson** (retro: "statements, not proofs" was the
   recurring failure) matches our axiom-vetting discipline; every adopted route
   should land statement-frozen against OUR signatures with non-vacuity witnesses,
   as both repos' conventions already demand.
4. **Provenance hygiene.** This doc cites `rkirov/jacobian-claude@88b113e`
   (Apache 2.0). Independent reimplementation = fresh Lean from the cited
   textbook sections (Forster §§19–21, 10.5, 16; Miranda Ch. VI, X §2) against our
   substrate; where instead a *re-vendor* of post-base files would be cheaper
   (e.g. the Laurent-tail tower), that is an owner decision to take explicitly,
   with attribution headers per our vendoring convention — not part of this pass.
   Note `4437c2b` is no longer reachable in the upstream clone's history (likely a
   submission-branch history rewrite); our `vendor/kirov-dolbeault-port/PROVENANCE.md`
   retains the full hash and snapshot.

## Verdict table

| # | Item (ours) | His resolution | Verdict | Our estimate (post-shared-atoms) |
|---|---|---|---|---|
| 1 | `AX_AbelTheorem` ⊆ (#14) | Forster §20 weak-solution ∂̄ engine (no polygon, no Jacobi inversion) | **adopt-route** (⊆); keep our Liouville ⊇ | 3–6 wk incl. shared atoms |
| 2 | `AX_genus_eq_zero_iff_homeo` backward (#15) | van Kampen S² + discrete monodromy primitives + Liouville | **adopt-route** (backward now; forward after RR decision) | 1–2 wk backward |
| 3 | `UnwindRegularity` (R6D2 §2) | §17 program deleted; Laurent-tail Lemma 3.6 single-monomial witness | **adopt-route** = retire the lane, re-point keystone at tails | 2–4 wk (tail tower) |
| 4 | `hga` h¹(𝒪)=0 at g=0 (G0) | `h1Dim 0 = genus` uniformly: cup-kill + tail duality + RR subtraction | **adopt-route** | days on top of 1/3 |
| 5 | Period lattice / Cluster A | Forster 21.4 B-1…B-5, dissection-free, consumes the engine | **hybrid** (adopt engine; model restructuring → Discussion) | 1–2 wk post-engine |
| 6 | Homotopy invariance (Fork 1) | full endpoint-fixed HI, discrete continuation + tube + Abel summation | **adopt-route** | < 1 wk |
| 7 | #30/#31/#34 functoriality | span-induction naturality + preimage cycle + basis extension (machinery already in our port) | **adopt-route** | #30 ~1 wk now; #31 1–3 wk; #34 days |
