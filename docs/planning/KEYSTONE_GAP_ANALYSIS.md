# Keystone gap analysis — `exists_serreDualityData` (Forster §17.5 + §17.9)

*2026-06-10. Analysis of the single remaining Serre-duality sorry in the verbatim Kirov
snapshot `vendor/kirov-jacobian-claude-dolbeault/` (4 sorries total in the snapshot, zero
custom axioms; the other three — `CutSurfaceRelations.lean:161`, `Abel.lean:671`,
`DegreeOneSphere.lean:678` — are outside the Serre tower). All paths below are relative to
`vendor/kirov-jacobian-claude-dolbeault/` unless prefixed otherwise.*

---

## 1. The statement

`Jacobians/Dolbeault/SerreDualityPairing.lean:125-127`:

```lean
theorem exists_serreDualityData (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    Nonempty (SerreDualityData 𝔘) :=
  sorry
```

`SerreDualityData 𝔘` (`SerreDualityPairing.lean:68-80`) bundles five fields:

| Field | Content | Forster |
|---|---|---|
| `K : Divisor X` | canonical divisor | — |
| `hKgenus : lDim K = genus X` | `𝒪_K ≅ Ω` at `D = 0` | 17.4 |
| `ι : ∀ D, lSysModule (K−D) →ₗ[ℂ] Dual ℂ (𝔘.cechH1 D)` | residue pairing `⟨f,ξ⟩ = Res((f·ω₀)·ξ)` | 17.5 |
| `ι_inj : ∀ D, Injective (ι D)` | residue-1 witness | 17.6 |
| `ι_surj : ∀ D, Surjective (ι D)` | dimension count | 17.9 |
| `finH1 : ∀ D, FiniteDimensional ℂ (𝔘.cechH1 D)` | Čech finiteness | §14 |

Everything downstream of the bundle is already proved inside the same file: `serre_eq`
(17.11, `:89`), `lDim_le_h1Dim` (`:104`), `arithmeticGenus` (17.10 at `D=0`, `:110`),
`serreH1` (`:114`).

**Assembly chain already built.** The snapshot contains a complete reduction ladder, so the
sorry is NOT "produce all six fields from scratch" but "inhabit the smallest interface at the
bottom of this chain":

```
MeromorphicCousinSolutions 𝔘 ω₀ K        (MeromorphicCousinSolve.lean:448; fields lift+vanish)
  --(+ nondeg)--> CousinResidueData 𝔘 K  (MeromorphicCousinSolve.lean:541 toCousinResidueData)
  --> GlobalResidue 𝔘 K                  (GlobalResidueConstruct.lean:180 toGlobalResidue)
  --> SerreResidueRealization 𝔘 K        (SerreResidueRealizationAssembly.lean:109)
  --(+ hKgenus, ι_surj, finH1)--> SerreDualityData 𝔘
                                         (SerreResiduePairing.lean:228 toSerreDualityData;
                                          end-to-end: MeromorphicCousinSolve.lean:578)
```

So the keystone = construct, for a suitable `ω₀` / `K = div ω₀`:
**(a)** `lift` (the meromorphic Cousin solve, §17.5 connecting map),
**(b)** `vanish` (Gate-A residue descent at cover level),
**(c)** `nondeg` (§17.6 `dz/z` witness transported through the lift),
**(d)** `ι_surj` (§17.9 count), and align **(e)** `hKgenus`'s `K` with the pairing's `K`.
(`finH1` is unconditional, see below.)

---

## 2. Proved substrate beneath the keystone (all sorry-free in the snapshot)

| Piece | Declaration | File:Line | How it feeds the keystone |
|---|---|---|---|
| §17.6 abstract core | `finrank_le_of_injective_to_dual` | `Jacobians/Dolbeault/SerreDuality.lean:87` | easy-half dim bound engine |
| §17.9 abstract core | `serre_surjectivity_dim_core` + `subspaces_inf_ne_bot_of_finrank_add_gt` | `SerreDuality.lean:59,38` | the pigeonhole count, parametric in the RR bounds |
| §17.6 reduction | `injective_of_residueOne_witness`, `finrank_le_of_residueOne_witness` | `SerreResiduePairing.lean:146,163` | residue-1 witness ⇒ `ι_inj` (consumed at `:209-219`) |
| Res well-definedness | `MittagLefflerForm.res_eq_zero_of_globalMeromorphic`, `res_eq_of_globalMeromorphic_diff` | `SerreResiduePairing.lean:95,119` | representative-independence of `Res`; conclusion of `∑Res = 0` |
| (cover-level variant) | `GeneralMittagLeffler.res_eq_zero_of_globalMeromorphic` | `GeneralMittagLeffler.lean:203` | same, on `GeneralMLDistribution` (consumed by `vanish`, cf. `MeromorphicCousinSolve.lean:437`) |
| 1-form residue theorem (Gate A) | `residueTheorem_unconditional` | `SerreResidueRamifiedRealSlitGeometry.lean:1017` | unconditional `∑Res = 0` for `α = ω₀·g`, `ω₀ : HolomorphicOneForms X` |
| Cup product (§17.5 product) | `cup D K : lSysModule (K−D) →ₗ (cechH1 D →ₗ cechH1 K)` | `SerreCupProduct.lean:387` (complete file) | the pairing is `res ∘ cup` (`SerreResidueRealizationAssembly.lean:93-97`) |
| Čech finiteness (`finH1`) | `finiteDimensional_cechH1_wired` (via `exists_cechModel`, `exists_cechModel_general`) | `CechFinitenessWiring.lean:85,53`; `CechFinitenessDtwist.lean:429` | discharges `finH1` **unconditionally** |
| Skyscraper LES | `exists_skyscraperLES` (now a theorem, via the cone construction) | `CohomologicalRR.lean:156`; engine `SkyscraperConeRealization.lean:99ff` | feeds χ-induction; needs `hR : 𝔘.LocallyRealizable` |
| Cohomological RR | `cohomological_riemannRoch` : `h⁰(D) − h¹(D) = deg D + 1 − h¹(0)` | `CohomologicalRR.lean:216` | the §17.9 dimension bounds; needs `hR` |
| RR inequality | `riemannRoch_inequality` | `SerreOmega0.lean:91` | `deg D + 1 − h¹(0) ≤ lDim D` |
| Realizable Leray cover | `locallyRealizable_chartDiskCover`, `exists_realizableLerayCover` | `SkyscraperProductWitness.lean:236,247` | supplies a cover satisfying `hR` |
| Gate D (ω₀ existence) | `exists_nonconstant_meromorphic` | `SerreOmega0.lean:129` | nonconstant `f` ⇒ nonzero `ω₀ = df` |
| `hKgenus` | `exists_canonicalForm17Data_hKgenus` (unconditional) | `FormRemovableSingularity.lean:583`; datum `CanonicalFormIso.lean:199`, built at `CanonicalFormDifferential.lean:552` | discharges `hKgenus` for the datum's own `K = div ω₀` |
| `h⁰ = l` bridge | `h0Dim_eq_lDim`, `cechRestrictL_surjective` | `CechH0.lean:619,545` | translates Čech `h⁰` to `lDim` in the count |
| Negative-degree vanishing | `lDim_eq_zero_of_deg_neg`, `MeromorphicFunction.deg_div` | `Jacobians/RiemannRoch.lean:90,76` | the `hV` input of the §17.9 count (`h⁰(D−nP) = 0` for large `n`) |
| `dz/z` local witness | `exists_formFnResidue_eq_one_of_localRep_ne_zero` | `FormCoeff.lean:113` | local datum behind `nondeg` |
| Residue-functional algebra | `resCocycle` (linear), `resCocycle_vanish_coboundary`, `resCocycle_connecting` | `MeromorphicCousinSolve.lean:507,521,533` | from `lift`+`vanish`, the descended `Res` and its genuine-Laurent-residue tie are **derived** |
| Cousin split assembly | `CousinSplitData → CoverMLLift`, `(A)`-engine `exists_holoSplit_of_isDiskAcyclic`, `MeromorphicCousinSolutions.ofSplittable` | `MeromorphicCousinLift.lean` (whole file; engine `:287`, apex `:320ff`) | reduces `lift` to per-cocycle `CousinSplitData` |
| Disk acyclicity | `isDiskAcyclic_of_hasGluedDbarDatum` | `CechFinitenessBallSolve.lean:1047`; `SharedChartCover` def `:91` | `H¹ = 0` — but ONLY for single-chart families (see landmine, §4.S3) |
| Per-pole well-definedness | `formFnResidue_eq_of_analyticAt_sub` | `GlobalResidueConstruct.lean:97` | the connecting map's local heart |

---

## 3. Downstream results gated on the keystone

Inside the snapshot:

- `arithmeticGenus_eq_genus_serre` — `SerreDualityPairing.lean:130`
- `serre_h1_eq_serre` — `SerreDualityPairing.lean:136`
- `arithmeticGenus_eq_genus` (`h¹(0) = g`) — `DolbeaultLadder.lean:56`
- `serre_h1_eq` (general Serre `h¹(D) = l(K−D)`) — `DolbeaultLadder.lean:64`
- `riemannRoch_equality_of_ladder` — `DolbeaultLadder.lean:78`
- **`exists_riemannRoch_divisor` (classical RR, the repo headline)** — `Jacobians/RiemannRoch.lean:60`
  (instantiated at the realizable chart-disk cover, `:66-68`)
- `exists_singleSimplePole_of_genus_zero` and everything in `RiemannRoch.lean` downstream of
  the headline — `Jacobians/RiemannRoch.lean:155`

In our repo (Phase D, `docs/planning/PHASE_D_BRIDGE_PLAN.md`): the keystone gates the
`serreDuality_equiv` and `h1coh_zero_finrank` axiom discharges (41 → 34 if it falls); the
cechModel / skyscraperLES bridges are NOT gated (sorry-free already).

Note `CohomologicalRR` is **not** gated on the keystone (it sits *below* it; the keystone's
§17.9 half consumes it).

---

## 4. Sub-lemma decomposition (Forster §17.5 + §17.9)

Severity scale: **M** = mechanical, **HS** = hard-but-standard, **RG** = research-grade.

| # | Sub-lemma (informal) | Existing infrastructure | Gap rating |
|---|---|---|---|
| **S1** | **Canonical datum alignment.** Pick `0 ≠ ω₀` with `K = div ω₀` such that the SAME `K` serves both `hKgenus` and the residue chain. The residue/Cousin machinery is typed over `ω₀ : HolomorphicOneForms X` (`MeromorphicCousinSolve.lean:448`, `residueTheorem_unconditional`), while `CanonicalForm17Data.ω₀ : MeromorphicOneForm X` (`CanonicalFormIso.lean:199-207`). For `g ≥ 1` take `ω₀` holomorphic nonzero (`genus = finrank > 0`) and rebuild a `CanonicalForm17Data` from it (order/divisor bookkeeping as in `CanonicalFormDifferential.lean:552`). | order-divisor machinery, `nonempty_canonicalForm17Data` | **M–HS** |
| **S2** | **`vanish` (Gate-A descent, Forster §17.3).** A `CoverMLLift` with `connectingClass = 0` has `res = 0`: decompose a coboundary lift as (global meromorphic `f`) + (`𝒪_K`-section 0-cochain `σ`); `ω₀·σᵢ` is holomorphic (poles cancelled, `ord ω₀ = K`), contributing residue 0 (`coboundary_lift_holomorphic_res_zero`, `CousinResidueConnecting.lean` — proven); the `f` part vanishes by `res_eq_zero_of_globalMeromorphic` (proven, unconditional). Gap = the gluing/decomposition bookkeeping from `connectingClass = 0`. | `SerreResiduePairing.lean:95,119`; `GeneralMittagLeffler.lean:203`; `CousinResidueConnecting.lean` | **HS** |
| **S3** | **`lift` (the §17.5 connecting map / meromorphic Cousin solve — THE WALL).** Every `𝒪_K`-cocycle `ξ` is `δμ` for a meromorphic `CoverMLLift μ` (with the four analytic fields). The snapshot's residual is `CousinSplittable` (`MeromorphicCousinLift.lean:320`): per-cocycle `CousinSplitData` = (B) principal-part split + (A) clear the holomorphic remainder. **Landmine:** the (A) engine's hypothesis `IsDiskAcyclic 𝔘 0` (`:287`) says `H¹(𝔘,𝒪) = 0`, which for a Leray cover of `X` is FALSE when `g > 0` (`h1Dim 0 = g`); `IsDiskAcyclic` is proven only for single-chart `SharedChartCover` families (`CechFinitenessBallSolve.lean:91,1047`), which cannot cover `X`. For `g > 0` the holomorphic remainder carries a (possibly nonzero) `H¹(𝒪)`-class; killing it requires extra poles, i.e. `ker(H¹(𝒪_K) → H¹(𝒪_{K+nP}))` exhausting — equivalent to eventual vanishing `h¹(K+nP) → 0`, which classically IS a Serre-duality corollary (circularity risk). Forster avoids the wall entirely: his `Res : H¹(X,Ω) → ℂ` is the smooth Dolbeault/PoU integral (fine-sheaf splitting, no global meromorphic lift), and the ML picture is used only for *computing* `Res` on explicit witnesses (Stokes compatibility, 17.3). Alternatives: **(i)** Dolbeault-integral `res` (PoU + global (1,1)-integration + Stokes — Forster-verbatim; heavy but standard infra; `RealForms.lean`/`RealManifold.lean`/Gate-A real-integration machinery partially relevant); **(ii)** Kempf-style PDE-free proof of `h¹(nP) → 0` (research-grade here); **(iii)** restrict `res` to the ML-representable subspace and rework the pairing's target (changes `SerreDualityData`'s interface). | split assembly + descent algebra all proven; only the analytic split itself missing | **RG** (as architected); **HS-but-large** via route (i) |
| **S4** | **`nondeg` (§17.6 witness transport).** For `0 ≠ [f] ∈ L(K−D)` build an explicit single-simple-pole distribution `g` (local `dz/z` at a point where `f`'s local rep is nonzero), set `ξ := [δg] ∈ cechH1 D`; then `res(cup f ξ) = res of the f·g-distribution = formFnResidue = 1` via `resCocycle_connecting` (`MeromorphicCousinSolve.lean:533`) + the local witness (`FormCoeff.lean:113`). Gap = the explicit two-set cocycle construction and the cochain-level identity `cup f (δg) = δ(f·g)` over the `cupCochain*` lemmas (`SerreCupProduct.lean:163-171`). Note: this direction needs no Cousin *solve* — the lift is built by hand. | `FormCoeff.lean:113`; `SerreCupProduct.lean`; `MeromorphicCousinSolve.lean:533` | **HS** |
| **S5** | **Forster 17.7 (restriction compatibility + unwinding).** `ι` commutes with the duals of the restriction maps `H¹(𝒪_{D'}) → H¹(𝒪_D)` (`D' ≤ D`), and the pole-bound regularity step: if `ι_{D_n}(ω) = ψ·λ` then `ω/ψ ∈ L(K−D)` and `ι_D(ω/ψ) = λ` (an order/vanishing argument re-using the residue-1 witnesses). | `h1Map` (`SkyscraperLESBase`), cup, `FormCoeff` witnesses, `orderW` additivity | **HS** |
| **S6** | **Forster 17.8 (the `ψ`-action `Λ_n ≅ H⁰(𝒪_{nP})`).** For `0 ≠ λ ∈ (cechH1 D)*`, `ψ ↦ ψ·λ` is injective `H⁰(𝒪_{nP}) → (cechH1 (D−nP))*`. Key input: mult-by-`ψ` is *surjective* on `H¹` — factor as divisor-shift iso ∘ inclusion `𝒪_{D−nP+div ψ} ↪ 𝒪_D`, whose `H¹`-surjectivity is the iterated skyscraper `surj₄` (the LES machinery already proven for single-point inclusions, `SkyscraperAssembly.lean:508ff`). | skyscraper LES, cup/`mulLeftG`, `cechH1` functoriality | **HS** |
| **S7** | **§17.9 assembly (the dimension-count skeleton).** Instantiate `serre_surjectivity_dim_core` with `V n := Dual(cechH1 (D − nP))`, `Λ n := {ψλ}`, `I n := range(pairing (D−nP))`. Inputs: `hΛ` from S6 + `riemannRoch_inequality` (`SerreOmega0.lean:91`, `h⁰(nP) ≥ n+1−h¹(0)`); `hI` from `ι_inj` (`dim I n = lDim(K−D+nP)`) + RR inequality; `hV` from `cohomological_riemannRoch` + `h0Dim_eq_lDim` + `lDim_eq_zero_of_deg_neg` (`h⁰(D−nP) = 0` for `n > deg D`). Witness extraction: `0 ≠ ψλ = ι_{D_n}(ω)` ⇒ `λ = ι_D(ω/ψ)` via S5. All RR inputs are **already proven** — this skeleton is buildable today against the existing `lDim`/`h1Dim` API, parametric in S5/S6. | `SerreDuality.lean:59`; all RR API above | **M–HS** |
| **S8** | **Cover hypothesis alignment.** The keystone takes only `hL : IsLeray`, but every RR input (S7) needs `hR : LocallyRealizable`. `LocallyRealizable` is proven for `chartDiskCover` only (`SkyscraperProductWitness.lean:236`); arbitrary-Leray would need cover-independence of `h1Dim` (only partial: `LerayCoverIndependence.lean:25-29` documents the limits). The sole downstream consumer instantiates at the realizable cover anyway (`Jacobians/RiemannRoch.lean:66-68`, which has BOTH `hL` and `hR` in scope). Fix: add `(hR : 𝔘.LocallyRealizable)` to `exists_serreDualityData` and thread through `DolbeaultLadder.lean:56,64`. | `exists_realizableLerayCover` | **M** (signature change; upstream coordination) |
| **S9** | **Genus 0.** The residue chain over a holomorphic `ω₀` requires `g ≥ 1` (`HolomorphicOneForms X = 0` and `K = div ω₀` undefined/`deg K = 2g−2 < 0` at `g = 0`). The snapshot carries a separate direct genus-0 route (`SerreResidueDirectGenus0*.lean`, 4 files + `Germ` discharge); whether `exists_serreDualityData` at `g = 0` is closed by that route or needs a case split must be confirmed. | `SerreResidueDirectGenus0Assemble.lean` etc. | **HS** (likely; unverified) |

---

## 5. Recommended attack order

1. **S8 first (days).** Agree with rkirov to add `hR : LocallyRealizable` to the keystone (or
   restate it at `chartDiskCover`). Zero math, unblocks everything in S7; downstream consumers
   already hold `hR`.
2. **S7 — the tractable first reduction (1–2 weeks).** Build the §17.9 count skeleton as an
   axiom-free engine file: a structure `SurjectivityInputs 𝔘 K D` with fields = S5 (unwinding)
   and S6 (ψ-action) statements, plus a proof
   `ι_surj_of_inputs : SurjectivityInputs → Function.Surjective (pairing D)` running
   `serre_surjectivity_dim_core` on the proven RR API (`riemannRoch_inequality`,
   `cohomological_riemannRoch`, `h0Dim_eq_lDim`, `lDim_eq_zero_of_deg_neg`,
   `finiteDimensional_cechH1_wired`). This isolates the *entire* §17.9 half to two named
   geometric lemmas and proves the dimension arithmetic correct now. It exactly matches the
   Phase-C "statement-vetted primitives → axiom-free engine" recipe.
3. **S6 then S5 (2–4 weeks).** The ψ-action surjectivity via iterated skyscraper `surj₄` +
   divisor-shift, then the 17.7 unwinding. Both stay inside proven cup/LES infrastructure.
4. **S4 (1–2 weeks).** The explicit `dz/z` witness lift + `cup`∘`δ` compatibility.
5. **S2 (1–2 weeks).** The `vanish` descent bookkeeping.
6. **S3 last, after an architecture decision with rkirov (the genuine wall).** Do NOT start
   coding the Cousin solve in the current (A)/(B) shape — for `g > 0` the (A) hypothesis is
   unsatisfiable on a covering family and `CousinSplittable` as stated has `h¹-eventual-vanishing`
   strength. Decide between route (i) (Forster-verbatim Dolbeault/PoU integral `res`, our
   recommendation: it removes the circularity risk and reuses the Gate-A real-analytic
   machinery) and route (ii)/(iii). Everything in steps 1–5 is invariant under that choice:
   S4/S5/S6/S7 consume only the `GlobalResidue` interface (`SerreResidueRealizationAssembly.lean:75`),
   not the lift's construction.

With steps 1–5 done, the keystone sorry reduces to inhabiting
`GlobalResidue 𝔘 K` (one linear functional + the already-isolated descent facts) — a single,
sharply-stated analytic object instead of a six-field bundle.

## 6. Open questions for upstream coordination (rkirov)

1. **Signature:** add `hR : 𝔘.LocallyRealizable` to `exists_serreDualityData` (and
   `DolbeaultLadder.arithmeticGenus_eq_genus` / `serre_h1_eq`), or restate at the canonical
   chart-disk cover? (S8; consumers unaffected.)
2. **The S3 architecture call:** does he intend `CousinSplittable` (i.e. `H¹(X,ℳ) = 0`-strength
   splitting) as the real plan for `g > 0`, given `IsDiskAcyclic 𝔘 0` is false for covering
   families at `g > 0` and the divisor-enlargement argument is Serre-adjacent? Or is the
   Dolbeault/PoU-integral `res` (Forster's actual §17.3) acceptable as a deviation from the
   PDE-free constraint? (Forster §17 already uses fine-sheaf/Dolbeault arguments; "PDE-free"
   means no harmonic theory, not no smooth forms.)
3. **Genus 0:** is `exists_serreDualityData` at `g = 0` meant to be discharged by the
   `SerreResidueDirectGenus0*` route, and if so is a genus case split inside the keystone proof
   acceptable?
4. **Division of labor:** the S7 engine + S6/S5 are self-contained against frozen interfaces
   (`GlobalResidue`, skyscraper LES, RR) — good candidates for our side under Phase D while
   upstream owns the `res` construction; coordinate via the planned draft issue
   (`docs/planning/PHASE_D_BRIDGE_PLAN.md`, item B).

## 7. Bottom line

The keystone is far smaller than its statement suggests: `finH1` and `hKgenus` are already
unconditional theorems, `ι_inj` is derived from a witness interface, and the §17.9 count is
abstractly proven with all of its RR inputs available. The remaining content is (a) two
hard-but-standard geometric lemmas (17.7, 17.8), (b) two hard-but-standard bookkeeping
constructions (`vanish`, `nondeg`), and (c) ONE research-grade object: the global residue
functional `res : cechH1 K →ₗ ℂ` — whose difficulty is an artifact of the current
meromorphic-Cousin architecture and drops to hard-but-standard under Forster's own
smooth-integral definition. Estimated: steps 1–5 ≈ 5–9 weeks of standard work; S3 ≈ unknown
until the architecture decision, but bounded by the existing Gate-A slit-geometry precedent if
route (i) is taken.
