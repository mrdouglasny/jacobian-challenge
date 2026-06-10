# S3 scoping — Forster fine-sheaf (Dolbeault/PoU) residue functional `Res : H¹(X,Ω) → ℂ`

*2026-06-10. Implementation scoping for the S3 architecture decision recorded in
`docs/planning/KEYSTONE_GAP_ANALYSIS.md` §4.S3/§5.6: replace the snapshot's
meromorphic-Cousin-lift construction of `GlobalResidue` with Forster's §17.3 smooth
partition-of-unity / surface-integral residue functional. All snapshot paths are relative to
`vendor/kirov-jacobian-claude-dolbeault/`; Mathlib paths/lines verified at the **main repo pin**
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (2026-05-26, `.lake/packages/mathlib`). The snapshot's
own manifest pins mathlib `8e3c9891…` — all decls cited below are years-stable API present at
both; re-verify line numbers when building against the snapshot toolchain
(`lean-toolchain: v4.30.0-rc1`).*

---

## 1. What `GlobalResidue` must provide, and the B1 claim

### 1.1 The interface (the construction target)

`Jacobians/Dolbeault/SerreResidueRealizationAssembly.lean:75-83`:

```lean
structure GlobalResidue (𝔘 : FiniteCover X) (K : Divisor X) where
  res : 𝔘.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ
  nondegenerate : ∀ (D : Divisor X) (v : lSysModule (K - D)), v ≠ 0 →
    ∃ ξ : 𝔘.toFiniteFamily.cechH1 D, res (cup (𝔘 := 𝔘.toFiniteFamily) D K v ξ) = 1
```

Two fields only. Everything else is **derived, sorry-free, in the snapshot**:

| Derived | Where |
|---|---|
| `pairing D := res ∘ cup` (§17.5 pairing into `Dual ℂ (cechH1 D)`) | `SerreResidueRealizationAssembly.lean:93-97` |
| `toSerreResidueRealization` | `:109-114` |
| `pairing_injective` (§17.6 easy half) | `:117-119` (via `SerreResiduePairing.lean:146` `injective_of_residueOne_witness`) |
| `lDim_le_h1Dim` | `:122-125` |
| `toSerreDualityData` (given `hKgenus`, `ι_surj`, `finH1`) | `:134-139` → `SerreResiduePairing.lean:228` |

### 1.2 An important free fact: the cocycle-level wrapper `CousinResidueData` is construction-agnostic

`GlobalResidueConstruct.lean:141-158` defines `CousinResidueData 𝔘 K` with fields

* `resCocycle : ↥(cocycles1 K) →ₗ[ℂ] ℂ`,
* `vanish_coboundary : resCocycle = 0 on B¹ ⊆ Z¹`,
* `nondegenerate` (same `dz/z` statement, phrased via `Submodule.liftQ`),

and **proves** `toGlobalResidue` (`:180-182`, descent via `Submodule.liftQ`, `res_mk` simp at
`:171`). Despite its name and docstrings, **no field of `CousinResidueData` mentions a meromorphic
lift** — it is exactly "a linear functional on Ω-cocycles that kills coboundaries, plus the §17.6
witness". The Forster integral functional inhabits it verbatim. So **the fine-sheaf swap requires
zero interface changes**: we inhabit `CousinResidueData` (or `GlobalResidue` directly) and simply
*retire* the intended feeders upstream of it:

* `MeromorphicCousinSolutions` (`MeromorphicCousinSolve.lean:448-454`, fields `lift` = `H¹(X,ℳ)=0`
  and `vanish`) with its descent `toCousinResidueData` (`:541`) / `toGlobalResidue` (`:552`) /
  end-to-end `toSerreDualityData` (`:578`);
* `CousinSplittable` (`MeromorphicCousinLift.lean:320`) + the `(A)` engine
  `exists_holoSplit_of_isDiskAcyclic` (`:287`) — the path blocked by the g>0 landmine:
  `IsDiskAcyclic` (`CechDiskAcyclic.lean:166`) is proven only for single-chart
  `SharedChartCover` families (`CechFinitenessBallSolve.lean:91`,
  `isDiskAcyclic_of_hasGluedDbarDatum` `:1047`), which cannot cover `X`, and for a covering Leray
  family `IsDiskAcyclic 𝔘 0` is FALSE at `g > 0` (`h1Dim 0 = g`);
* the alternative feeder `MittagLefflerConnection.toGlobalResidue`
  (`CousinResidueConnecting.lean:164-165`) and `MeromorphicCousinSolvable.toGlobalResidue`
  (`MeromorphicCousin.lean:557-559`).

### 1.3 B1 claim — CONFIRMED

Grep over the whole snapshot: the identifiers `GlobalResidue`, `CousinResidueData`,
`MeromorphicCousinSolutions`, `SerreResidueRealization`, `CousinSplittable`,
`resCocycle_connecting` occur **only** in the eight feeder/assembly files
(`GlobalResidueConstruct`, `MeromorphicCousinSolve`, `MeromorphicCousin`,
`MeromorphicCousinLift`, `GeneralMittagLeffler`, `CousinResidueConnecting`,
`SerreResidueRealizationAssembly`, `SerreResiduePairing`). The ladder downstream —
`SerreDualityPairing.lean` (keystone `exists_serreDualityData` `:125-127`, plus `serre_eq:89`,
`lDim_le_h1Dim:104`, `arithmeticGenus:110`, `serreH1:114`), `DolbeaultLadder.lean:56,64,78`,
`Jacobians/RiemannRoch.lean:60,66-68` — consumes **only** `SerreDualityData`, which
`GlobalResidue.toSerreDualityData` produces. The future S4–S7 engines (gap analysis §4) are
likewise specified against `GlobalResidue.pairing` only. Two caveats:

1. `nondegenerate` is a **field** of `GlobalResidue`, so S4 (`dz/z` witness) is part of
   *inhabiting* the interface, not downstream of it — its res-evaluation step changes under the
   Forster architecture (R6/R8 below replace `resCocycle_connecting`,
   `MeromorphicCousinSolve.lean:533`, which only exists for `MeromorphicCousinSolutions`).
2. The Forster construction is chart-local, so it inhabits `GlobalResidue 𝔇.toFiniteCover K` for
   a `ChartDiskCover 𝔇` (`ChartDiskCover.lean:30`, with `subset_chart_source:54`), not an
   arbitrary Leray `𝔘`. This is the same restriction S8 already imposes (every RR input needs
   `LocallyRealizable`, proven only at `chartDiskCover`, `SkyscraperProductWitness.lean:236,247`),
   and the sole keystone instantiation site holds both (`Jacobians/RiemannRoch.lean:66-68`). No
   new constraint.

---

## 2. The Forster §17.3 construction, step by step, mapped to infrastructure

### 2.0 Mathematical shape (Forster GTM 81, §17.2–17.3 + Dolbeault)

Fix `ω₀ : HolomorphicOneForms X`, `ω₀ ≠ 0`, `K = div ω₀` (effective; the S1 alignment of the gap
analysis). A class in `cechH1 K` is, via `ω₀·`, an `H¹(X,Ω)` class. Given a representing cocycle
`c = (c_{ij}) ∈ Z¹(𝔘, 𝒪_K)`:

1. **Ω-cocycle.** `ω_{ij} := c_{ij}·ω₀` is a *holomorphic* 1-form on `U_i ∩ U_j` (poles of
   `c_{ij}` ≤ `K` are cancelled by `ω₀`'s zeros — exactly the §17.4 `𝒪_K ≅ Ω` mechanism).
2. **Smooth PoU split.** With a smooth partition of unity `ρ_k` subordinate to the cover, set
   `σ_i := ∑_k ρ_k·ω_{ki}` — a smooth (1,0)-form on `U_i`; the telescoping identity gives
   `σ_j − σ_i = ω_{ij}` on overlaps.
3. **∂̄ and glue.** `τ := ∂̄σ_i` on `U_i`; since `∂̄ω_{ij} = 0`, the `∂̄σ_i` agree on overlaps and
   glue to a global smooth (1,1)-form `τ` on `X`.
4. **Integrate.** `Res([c]) := (2πi)⁻¹ ∬_X τ`.
5. **Well-defined.** If `c = δh` is a coboundary, `τ = ∂̄β` for the *global* smooth (1,0)-form
   `β := ∑_k ρ_k·(h_k·ω₀)`, and `∬_X ∂̄β = 0` by Stokes on the compact surface.
6. **ML compatibility (Forster 17.3).** If `c = δμ` for a Mittag–Leffler lift `μ = (g_i)`, then
   `Res([c]) = ∑_a Res_a(ω₀·g)` — this is what evaluates `res` on the explicit `dz/z` witness for
   `nondegenerate`.

### 2.1 Step 2 — partition of unity: AVAILABLE (Mathlib + port wrappers, all proven)

* Mathlib at pin: `SmoothPartitionOfUnity.exists_isSubordinate`
  (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean:563`), `IsSubordinate` (`:270`),
  `IsSubordinate.contMDiff_finsum_smul` (`:286`), `SmoothPartitionOfUnity.contMDiff_finsum_smul`
  (`:190`); bump functions `ContDiffBump`
  (`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:70`) for the per-pole cutoffs in R6.
* Port wrappers (proven, in active use): `exists_smoothPartitionOfUnity_subordinate` for an
  arbitrary `FiniteCover` (`DolbeaultComparisonInverse.lean:62`, via the `RealManifold` bridge
  making compact T2 `X` a σ-compact real manifold), the fixed choice `cechPoU`
  (`:77`), complexified `rhoC` (`:86`), `dbarRho := dbarL (rhoC k)` (`:90`), `∑ρ_k = 1`
  (`sum_rhoC:94`), `∑∂̄ρ_k = 0` (`sum_dbarRho_eq_zero:123`).
* Telescoping (step 2's algebra) is **already proven abstractly**:
  `cechCoboundary_telescoping` (`DolbeaultComparisonInverse.lean:50`) and the double-sum variant
  `telescope_sum` (`:653`).
* Smoothness-of-glued-term pattern: `gdTerm` + Leibniz `dbarL_gdTerm_apply`
  (`DolbeaultComparisonEquiv.lean:62,80`) and `cechTerm`
  (`DolbeaultComparisonInverse.lean:392`) are exact precedents for `ρ_k·(local data)` being a
  global smooth object with computed `∂̄`.

### 2.2 Steps 3–4 — what the port does NOT have, and the chart-coefficient workaround

The port's form calculus (`RealForms.lean`: `SmoothCFunctions:34`, `SmoothCOneForms:49`;
`DolbeaultH01.lean`/`DolbeaultComparison.lean`: `dbarL : A⁰ →ₗ[ℝ] A¹`, `proj01L`,
`OneFormsZeroOne`) stops at 1-forms. There is **no `A²` (1,1)-form bundle, no `d`/`∂̄` on
1-forms, and no integration of anything over `X`** anywhere in the snapshot (checked: `GreenBox.lean`
and `SurfacePositivity.lean` are purely planar — Green on the unit box from Mathlib's divergence
theorem, and box-integral positivity; `DbarDisk.lean` is purely planar Wirtinger calculus).

**Recommended representation — skip the bundle, work in chart coefficients.** On a curve a
(1,1)-form is, per chart `j`, one smooth function `t_j : ℂ → ℂ` with the overlap law
`t_j = (t_k ∘ φ)·|φ′|²` for the holomorphic transition `φ`; its integral is patched by exactly the
Lebesgue area Jacobian. So define everything planar:

* local split coefficient `s_j(z) := ∑_k ρ̃_k(z)·w_{kj}(z)` where `w_{kj}` is the chart-`j`
  coefficient of `ω_{kj}` and `ρ̃_k = ρ_k ∘ (chart j)⁻¹`;
* `t_j := DbarDisk.dbar s_j` (`DbarDisk.lean:28`, Wirtinger `∂̄` via `fderiv ℝ`);
* `Res(c) := (2πi)⁻¹ ∑_j ∫_{ℂ} ρ̃_j·t_j ∂volume`, i.e. unfolded,
  `(2πi)⁻¹ ∑_{(j,k)} ∫ ρ̃_j·(∂̄ρ̃_k)·w_{kj}` — every integrand a smooth compactly supported
  planar function (support ⊆ chart image of `tsupport ρ_j ∩ tsupport ρ_k ⊆ U_j ∩ U_k`).

Measure-theory substrate verified at pin: Lebesgue on `ℂ`
(`Complex.volume_preserving_equiv_real_prod`, `measurableEquivRealProd`,
`Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean:60,43`); change of variables
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
(`Mathlib/MeasureTheory/Function/Jacobian.lean:1217`); the ℝ-determinant of a ℂ-linear map
`LinearMap.det_restrictScalars` (`Mathlib/RingTheory/Norm/Transitivity.lean:180`) +
`Algebra.norm_complex_apply : Algebra.norm ℝ z = normSq z`
(`Mathlib/RingTheory/Complex.lean:37`) — together giving `|det_ℝ Dφ| = |φ′|²`, which is exactly
the (1,1) overlap law. Divergence/FTC for the planar Stokes:
`integral2_divergence_prod_of_hasFDerivAt`
(`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:551`; the port's `greenOnUnitBox`,
`Jacobians/GreenBox.lean`, is a worked precedent of driving it) and
`intervalIntegral.integral_deriv_eq_sub`
(`Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1178`).

### 2.3 Step 1 — Ω-cocycle extraction (germs → holomorphic chart functions)

Cocycle entries are germs: `cocycles1` (`CechComplex.lean:159`) over `Cochain1` with entries in
`OmegaDGerm K (U_i ⊓ U_j)` (`CechSection.lean:240`; sections `OmegaD` at `:78`). The proven
representative-extraction machinery is currently `D = 0` only: `holoRep`/`holoFn`
(`HoloRep.lean:44-60`, limit-repair via `Gext`) with the algebra `holoFn_sub/add/smul/congr/
restrict` (`CechFinitenessBallSolve.lean:512-591`). For `K`-germs the ω₀-multiplied coefficient
`coeffAt ω₀ · (mero rep)` has removable singularities at the `K`-points — exactly the content of
`FormRemovableSingularity.lean` (whose `exists_canonicalForm17Data_hKgenus:583` packages the
§17.4 iso; datum `CanonicalForm17Data`, `CanonicalFormIso.lean:199`). R1 below is the `K`-twisted
analogue of `holoFn`: a chosen holomorphic chart-coefficient function `w_{ij}` per overlap with
sub/add/smul/cocycle lemmas. Fiddly germ plumbing with strong precedent
(`holoFn_cocycle_eq_diskValDiff`, `DolbeaultComparisonEquiv.lean:114`).

### 2.4 Can `Res` be pulled back through the Čech↔Dolbeault comparison iso? — NO (directly); YES (its toolkit)

The proven comparison `comparison_linearEquiv : DolbeaultH01 X ≃ₗ[ℝ] 𝔇.cechH1 0` and
`cechH1_dolbeault_comparison_proof` (`DolbeaultComparisonEquiv.lean:648,660`) are (a) `D = 0`
only — there is no `K`-twisted Dolbeault module, and `H¹(Ω)` ≠ `H¹(𝒪)` — and (b) `ℝ`-linear
(the `2·` scalar bookkeeping), while `res` must be `ℂ`-linear. Building a `K`-twisted Dolbeault
module + comparison just to host `Res` would be strictly more work than defining `Res` on Čech
cocycles directly. What we DO take from the comparison files is the entire technology stack:
`cechPoU`/`rhoC`/`dbarRho`, telescoping, `cechTerm`/`gdTerm` smooth-gluing, `diskVal`
(`DolbeaultComparisonEquiv.lean:35`), `planarPrimitive`/`contDiff_planarPrimitive`/
`dbar_diskValue_eq_g` (`DolbeaultComparisonProof.lean:862,866,1026`), and the germ→function
extraction. The construction below is "the inverse-map file's technique, pointed at `Z¹(𝒪_K)`
and finished with an integral instead of a class".

---

## 3. Does `residueTheorem_unconditional` already contain the needed local-to-global integration lemmas? — NO (and it is no longer load-bearing)

`residueTheorem_unconditional` (`SerreResidueRamifiedRealSlitGeometry.lean:1017-1040`) proves
`∑_a Res_a(ω₀·g) = 0` for a **global** `MeromorphicFunction g` via the §5 real-slit route:
`RealCoverSlitSectionGeometry`, cluster sections, symmetric-function descent,
conservation-of-number — all 1-D contour/trace machinery over the trace of a global meromorphic
function. It contains **no** partition-of-unity, **no** area integral, **no** planar Stokes; none
of its lemmas are reusable for steps 3–5. Conversely, under the Forster architecture it stops
being load-bearing for the keystone: well-definedness of `Res` is now step 5 (Stokes), not
`∑Res = 0`. The Gate-A theorem and its Part-1 repackagings
(`MittagLefflerForm.res_eq_zero_of_globalMeromorphic` / `res_eq_of_globalMeromorphic_diff`,
`SerreResiduePairing.lean:95,119`; cover-level `GeneralMittagLeffler.lean:203`) remain proven and
become *consistency corollaries* (indeed `∑Res = 0` follows from R5 + R6 once both exist — a nice
cross-check, not an input). The genuinely reusable proven analytic assets are instead:

* `DbarDisk.cauchyPompeiu` (`DbarDisk.lean:642`): `(∂̄g ⋆ K)(z) = g(z)` for `g ∈ C^∞_c(ℂ)`, i.e.
  `∫ ∂̄g(ζ)/(ζ−z) ∂A = −π·g(z)` (`cauchyPompeiu_area:486`) — **this is the analytic heart of the
  simple-pole residue extraction R6** (see below);
* `DbarDisk` support lemmas: `dbar` (`:28`), `dbar_eq_zero_of_differentiableAt` (`:214`),
  `radial_integral`/`angular_integral`/`exists_radius_fderiv_eq_zero` (`:342,395,425`),
  `integrableOn_target_of_continuous_of_vanishing` (`:443`);
* `resAt` circle-integral residue + `resAt_const_mul_sub_inv` (`Residue.lean:33,55`),
  `resAt_eq_zero_of_differentiableOn_ball` (`:75`), and the `formFnResidue` layer
  (`FormCoeff.lean:52`, witness `exists_formFnResidue_eq_one_of_localRep_ne_zero:113`,
  per-pole invariance `formFnResidue_eq_of_analyticAt_sub`, `GlobalResidueConstruct.lean:97`);
* `Jacobians/GreenBox.lean` (`greenOnUnitBox`) as the worked pattern for Mathlib's divergence
  theorem.

---

## 4. Sub-lemma decomposition

Ratings: **M** mechanical, **HS** hard-but-standard, **RG** research-grade. Target: inhabit
`CousinResidueData 𝔇.toFiniteCover K` (hence `GlobalResidue`, §1.2) at the chart-disk cover, for
`K = div ω₀` from the S1-aligned `CanonicalForm17Data`.

| # | Sub-lemma | Infrastructure | Rating | Est. |
|---|---|---|---|---|
| **R1** | **`K`-germ → holomorphic chart coefficient.** For `c ∈ Z¹(𝒪_K)`, chosen functions `w_{ij} : ℂ → ℂ` holomorphic on the chart-`j` image of `U_i ∩ U_j` representing `ω₀·c_{ij}`, with add/smul/sub/cocycle-identity lemmas (function-level `w_{jk} − w_{ik} + w_{ij} = 0` on triple overlaps, from `cocycles1` membership). Removable-singularity repair at `K`-points = `FormRemovableSingularity` content; `holoFn`-style limit-repair (`HoloRep.lean:58`) + `coeffAt` (`FormCoeff.lean:35`). | `HoloRep`, `FormRemovableSingularity`, `CanonicalFormIso`, `holoFn_*` algebra | HS⁻ | 4–7 d |
| **R2** | **PoU split.** `s_j := ∑_k ρ̃_k·w_{kj}` smooth on chart `j` (support-aware gluing, `gdTerm`/`cechTerm` pattern); telescoping `s_j^φ − s_i = w_{ij}`-law (proven: `cechCoboundary_telescoping`). | `cechPoU/rhoC` (`DolbeaultComparisonInverse.lean:77,86`), `gdTerm` (`DolbeaultComparisonEquiv.lean:62`) | M | 2–4 d |
| **R3** | **Wirtinger chain rule + glue law.** `dbar (f ∘ φ) = ((dbar f) ∘ φ)·conj φ′` for holomorphic `φ` (new planar lemma from `fderiv` composition); hence `t_j = (t_k ∘ φ)·\|φ′\|²` on overlaps (uses `∂̄w = 0`, `dbar_eq_zero_of_differentiableAt`, `DbarDisk.lean:214`). | `DbarDisk.dbar`, Mathlib `fderiv` calculus | HS⁻ | 3–5 d |
| **R4** | **The integral functional + chart relocation.** `I(c) := ∑_j ∫_ℂ ρ̃_j·t_j`; ℂ-linearity in `c` (M, integrand-level). **Chart-relocation lemma**: for a coefficient family supported in `U_j ∩ U_k`, `∫_{chart j} = ∫_{chart k}` — `integral_image_eq_integral_abs_det_fderiv_smul` (`Jacobian.lean:1217`) + `det_restrictScalars` (`Transitivity.lean:180`) + `norm_complex_apply` (`RingTheory/Complex.lean:37`) + R3's law; side conditions (measurability, injectivity of `PartialHomeomorph` transitions on sources, integrability via compact support, `integrableOn_target_of_continuous_of_vanishing`, `DbarDisk.lean:443`). | Mathlib Jacobian CoV stack (all verified §2.2) | **HS** | 1–2 wk |
| **R5** | **Coboundary vanishing (Stokes).** (i) Planar atom: `∫_ℂ ∂̄g = 0` for `g ∈ C^∞_c` (Fubini via `volume_preserving_equiv_real_prod` + FTC `integral_deriv_eq_sub` on lines, or big-box `integral2_divergence_prod_of_hasFDerivAt`). (ii) Assembly: for `c = δh`, `t_j = ∂̄(β_j)` with `β := ∑_k ρ̃_k·(h_k ω₀)`-coefficients; `I(δh) = ∑_j ∫ ∂̄(ρ̃_j β_j) − ∑_j ∫ (∂̄ρ̃_j)·β_j`; first sum = 0 termwise by (i); second sum = 0 by inserting the PoU again + R4 relocation + pointwise `∑_j ∂̄ρ_j = 0` (`sum_dbarRho_eq_zero`). | R4, `sum_dbarRho_eq_zero` (`DolbeaultComparisonInverse.lean:123`), Mathlib FTC/divergence | **HS** | ~1 wk |
| **R6** | **ML-tie at a simple pole (Forster 17.3 — THE HARDEST PIECE).** For the explicit cocycle `e_{ij} = m_i − m_j` of a single-simple-pole lift (pole `a`, `Res_a(ω₀·m) = r`): `I(e) = 2πi·r`. Route: `η := ∑_k ρ̃_k·(ω₀ m_k)`-coefficients; split `η = ψ_a·(r/(z−a)) + (global smooth)` with a `ContDiffBump` `ψ_a ≡ 1` near `a` supported in one chart; smooth part dies by R5(i)+R4; singular part: `∫ ∂̄(ψ_a·r/(z−a)) = r·∫ ∂̄ψ_a(z)/(z−a) = −πr·(−2/…)` — **exactly `cauchyPompeiu` evaluated at `a`** (`ψ_a(a) = 1`), no annulus Stokes, no limits. Then identify `r` with `formFnResidue` via `resAt_const_mul_sub_inv` (`Residue.lean:55`) and the Laurent split of `ω₀·m` at `a` (simple pole: `coeff/(z−a) + analytic`, `formFnResidue_eq_of_analyticAt_sub` pattern, `GlobalResidueConstruct.lean:97`). Sign/normalization audit against `cauchyPompeiu`'s convention is the classic trap — pin it with a `(z−a)⁻¹` end-to-end test. **Scope deliberately to simple poles**: the general higher-order tie (full `resCocycle_connecting` analogue) is NOT needed — S4's witness and S5's 17.7 unwinding use only residue-1 simple-pole data. | `cauchyPompeiu` (`DbarDisk.lean:642`, PROVEN), `ContDiffBump`, R4, R5 | **HS⁺ (large)** | 1.5–3 wk |
| **R7** | **Descent + assembly.** `resCocycle := (2πi)⁻¹·I` (linear, R4); `vanish_coboundary := R5`; package as `CousinResidueData` → `toGlobalResidue` (PROVEN, `GlobalResidueConstruct.lean:180`) → `toSerreDualityData` (PROVEN). | §1.2 chain | M | 1–2 d |
| **R8** | **`nondegenerate` (= gap-analysis S4 under the new architecture).** Two-set `dz/z` cocycle from `exists_formFnResidue_eq_one_of_localRep_ne_zero` (`FormCoeff.lean:113`) + `exists_localRep_self_ne_zero` (`:~95`); cochain identity `cup f (δg) = δ(f·g)` over `cupCochain0/1/2` (`SerreCupProduct.lean:163-171`; `cup` at `:387`); evaluate via **R6**. | `SerreCupProduct`, `FormCoeff`, R6 | HS | 1–2 wk (parallel to R4–R5 except final step) |

**Out of scope for S3** (tracked separately in the gap analysis): S1 canonical-datum alignment
(`K = div ω₀` serving both `hKgenus` and the pairing), S7/S6/S5 (`ι_surj`), S8 (cover-hypothesis
signature), S9 (genus 0 — the Forster construction needs `g ≥ 1` for `ω₀ ≠ 0` holomorphic; `g = 0`
goes through the `SerreResidueDirectGenus0*` route).

### Critical path and estimate

```
R1 (4–7d) → R2 (2–4d) → R3 (3–5d) → R4 (1–2wk) → R5 (~1wk) → R6 (1.5–3wk) → R7 (1–2d)
                                                      R8 final step after R6 (its cocycle/cup
                                                      bookkeeping runs parallel from day 1)
```

≈ **6–9 weeks** of standard (no research-grade) work — consistent with the gap analysis's
"HS-but-large via route (i)" rating. The architecture decision removes the RG item entirely: no
`H¹(X,ℳ) = 0`, no `IsDiskAcyclic` on covering families, no `h¹(K+nP) → 0` circularity.

### Single hardest analytic ingredient

**R6 — the Mittag–Leffler/Stokes compatibility `Res([δμ]) = ∑Res_a(μ)` at a simple pole.** It is
the one step where the global PoU integral must be reconciled with a genuine Laurent residue. Its
classical form needs an excision/annulus-Stokes argument; the `cauchyPompeiu` shortcut above
(bump-cutoff + evaluate the proven convolution identity at the pole) eliminates the limit
arguments and reduces the analytic core to an already-proven theorem, leaving global-to-chart
localization bookkeeping (R4's relocation lemma) and the sign/normalization audit. R4 (the
holomorphic change-of-variables for planar area integrals) is the runner-up and is on R6's
dependency path; everything it needs exists in Mathlib at the pin (§2.2).

### Risk register

1. **Sign/normalization** (`(2πi)⁻¹`, `dbar = ½(∂_x + i∂_y)`, area vs `dz∧dz̄ = −2i dA`): fix by
   an end-to-end concrete test (`resAt_const_mul_sub_inv` ↔ R6 on the model cocycle) before
   building R8 on top.
2. **Germ-representative choice noise in R1** (`Classical.choice` reps must satisfy function-level
   cocycle identities only up-to-germ): state R2–R6 against *germ-eventual* equalities on
   overlaps, as `holoFn_congr`/`holoFn_cocycle_eq_diskValDiff` already do.
3. **Pin drift**: snapshot manifest (mathlib `8e3c9891…`) vs main repo (`c5ea0035…`); all cited
   Mathlib decls are stable API, but re-pin line numbers at build time.
4. **Upstream coordination**: the keystone's `exists_serreDualityData` signature must move to the
   chart-disk cover (or gain `hR`) — already an S8/rkirov question (gap analysis §6.1–6.2); the
   Forster route adds no further interface demand (§1.2).
