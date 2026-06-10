# Abel-wall gap analysis — `abelJacobi_twoPoint_ne_zero` (Forster §§20–21)

*2026-06-10. Third of the port-wall analyses (companions:
[`KEYSTONE_GAP_ANALYSIS.md`](KEYSTONE_GAP_ANALYSIS.md) for
`exists_serreDualityData`, [`CUTSURFACE_GAP_ANALYSIS.md`](CUTSURFACE_GAP_ANALYSIS.md) for
`exists_cutSurface`). Target = one of the 4 sorries in the verbatim Kirov snapshot
`vendor/kirov-jacobian-claude-dolbeault/` (the fourth, `DegreeOneSphere.lean:678`, enters
below as a sub-dependency). All snapshot paths relative to
`vendor/kirov-jacobian-claude-dolbeault/`; "ours" paths relative to repo root.*

---

## 1. The statement and what it asserts

`Jacobians/Abel.lean:668-671`:

```lean
theorem abelJacobi_twoPoint_ne_zero
    (h : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 :=
  sorry
```

Here `abelJacobi` (`Abel.lean:581-586`) is the **real** path-integrated Abel–Jacobi map on
degree-0 divisors: `D ↦ ∑_P D(P) • mk (periodVec (smoothPath P₀ P))` into the Jacobian
`(Fin (genus X) → ℂ) ⧸ truePeriodLattice X`, with `truePeriodLattice = Submodule.span ℤ
(closedLoopPeriods X)` (`PeriodLattice.lean:80-84`) and `twoPointDivisor P Q = (P) − (Q)`
(`Abel.lean:116-117`). Informally: **the Abel–Jacobi image of `P − Q` is nonzero for `P ≠ Q`
on a positive-genus surface** — i.e. injectivity of the point Abel–Jacobi map into the torus.

It is NOT Abel's theorem itself (kernel = principal divisors); it is the *consequence*
obtained by composing the hard half of Abel with the genus obstruction. The classical
proof (docstring, `Abel.lean:657-667`, Forster §21.5 / Miranda V §2.8):

1. If `abelJacobi (P−Q) = 0`, Abel's theorem (**⊆ / "kernel ⇒ principal", the HARD
   direction**) gives a meromorphic `f` with `div f = P − Q`.
2. Such an `f` has a single simple pole, hence is a degree-1 map `X → ℙ¹`, hence a
   biholomorphism (Riemann–Hurwitz / degree-one endgame), so `genus X = genus ℙ¹ = 0` —
   contradicting `0 < genus X`.

### Consumers in the snapshot

Exactly one, and it is **the challenge headline**: `ofCurve_inj`
(`Jacobians.lean:278-295`, wrapped for the conformance interface at `Jacobians.lean:690-691`)
— "Abel ⇒ ofCurve injective (THE main challenge theorem)". The whole chain above it is
proven: `ofCurve_basepoint_change` (`Jacobians.lean:256-259`, via
`smoothPath_basepoint_change`, now real), the connector `abelJacobi_twoPointDivisor`
(`Abel.lean:595-625`, proven), and the contradiction assembly (`Jacobians.lean:280-295`).
**This sorry is the last math gap between the snapshot and its headline `ofCurve_inj`.**
No other file consumes it (`LinearSystem`/`RiemannRoch`/`DegreeOneSphere` etc. import
`Abel.lean` only for the `MeromorphicFunction`/`Divisor` types).

---

## 2. Our side: mapping onto `AX_AbelTheorem` and the G3 obstruction

### What we have

| Ours | Where | Status |
|---|---|---|
| `AX_AbelTheorem` : `(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X` | `Jacobians/Axioms/AbelTheorem.lean:80-83` | **axiom** (DT-re-vetted SATISFIABLE/FAITHFUL 2026-06-09, `AXIOM_AUDIT.md:321`) |
| `AX_ofCurve_inj` (now a theorem) | `Jacobians/Axioms/OfCurveInjective.lean:15-36` | proven FROM `AX_AbelTheorem` + `principal_imp_eq_of_genus_pos` |
| `principal_imp_eq_of_genus_pos` (G3 genus obstruction: `div f = (Q₁)−(Q₂)`, `g>0` ⇒ `Q₁=Q₂`) | `Jacobians/RiemannSurface/DegreeOneGenusZero.lean:480-499` | **proven, axiom-clean** (G3 workstream) |
| — its engine `degreeOne_genus_zero` (degree-1 ⇒ biholo ⇒ genus transport) | `DegreeOneGenusZero.lean:430-451`, using `inverse_contMDiff_of_bijective_order_one` (`:388`) + `genus_eq_of_biholo` (`Jacobians/RiemannSurface/GenusInvariance.lean:56`) + `genus_projectiveLine_eq_zero` (`Jacobians/ProjectiveCurve/Line/Genus.lean:29`, axiom-free per PR #104) | proven |
| Abel **⊇** (principal ⇒ kernel) Liouville/pencil route | `docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md` | **route plan only — NOT landed Lean** (vetted 2026-06-07; ~800–1200 LOC est.) |
| Abel **⊆** (kernel ⇒ principal) Forster route | `docs/planning/ABEL_SUBSET_FORSTER_ROUTE.md` | route plan; explicitly gated on `AX_RiemannRoch` + `AX_SerreDuality` + `AX_RiemannBilinear` |

(Correction to a common shorthand: the ⊇/Liouville direction is a *vetted route*, not yet
proven Lean — the landed, axiom-clean asset on our side is the **genus obstruction**, not
either Abel direction.)

### Which direction is their sorry?

**The ⊆ direction (kernel ⇒ principal) — the hard one — but only its TWO-POINT instance,**
composed with the genus obstruction. The ⊇/Liouville direction does not enter at all: the
proof never needs "principal ⇒ AJ = 0". So per our route map
(`docs/planning/AX_AbelTheorem.md`, split note), their sorry sits squarely on the half that
needs RR + Serre + reciprocity, restricted to `D = (P) − (Q)` (which is the general
elementary case — every third-kind differential question reduces to two-point divisors,
so the restriction buys little on the analytic side; it does skip the induction over
`supp D` and the `D = D⁺ − D⁻` bookkeeping).

### Would discharging their sorry give us `AX_AbelTheorem`?

**No — neither direction in full.** `abelJacobi_twoPoint_ne_zero` is strictly weaker than
`AX_AbelTheorem`:

- It implies nothing about ⊇ (principal ⇒ kernel) for any divisor.
- For ⊆ it yields only the contrapositive consequence at two-point divisors
  ("AJ(P−Q)=0 ⇒ P=Q for g>0"), not "kernel ⇒ principal" for general degree-0 `D`.

What a discharge + Phase-D-style bridge WOULD buy us: `AX_ofCurve_inj` re-derived without
`AX_AbelTheorem`. `AX_AbelTheorem`'s only Lean consumer is
`Jacobians/Axioms/OfCurveInjective.lean:34`; with a bridge identifying their
`abelJacobi`-difference with our `ofCurveImpl` difference (the usual Phase-D type-alignment
problem: their `(Fin (genus X) → ℂ) ⧸ truePeriodLattice` vs our `Jacobian X` model — see
`docs/planning/PHASE_D_TYPE_ALIGNMENT.md`), `AX_AbelTheorem` would become **consumer-free**
(retirable from the challenge-critical cone, kept only if we pursue the full
`Pic⁰ ≃ Jac` program). The arrow also points the other way: **our `AX_AbelTheorem` +
our proven `principal_imp_eq_of_genus_pos` discharge their sorry modulo the same bridge**
— that is exactly the Phase-D pattern "our research axiom maps onto a Kirov sorry"
(`dolbeault-port-program` memory). Either way, the bridge is the same artifact.

---

## 3. Decomposition (Forster §§20–21 route) and what the snapshot already has

Two halves: **(A)** genus obstruction (`principal P−Q, P≠Q ⇒ contradiction`), **(B)** the
two-point ⊆ direction (`AJ(P−Q)=0 ⇒ P−Q principal`).

### Proved substrate in the snapshot

| Piece | Declaration | File:Line | Status |
|---|---|---|---|
| Real divisor `div f` via `orderAtPoint` | `MeromorphicFunction.divViaOrder` / `.div` | `Abel.lean:531-539` (order: `:153`, isolation: `:379`, chart-invariance: `:255`) | proven |
| Single-simple-pole predicate | `HasSingleSimplePole` | `MeromorphicLiouville.lean:56-58` | def |
| Degree-1 ⇒ homeomorphism `X ≃ₜ Y` | `degreeOne_homeo` | `DegreeOneSphere.lean:562-618` | **proven** (homeo only — no inverse-holomorphy) |
| Single simple pole ⇒ `X ≃ₜ S²` | `nonempty_homeo_sphere_of_singleSimplePole` | `DegreeOneSphere.lean:629-642` | **proven** |
| `X ≃ₜ S²` ⇒ `genus X = 0` | `genus_zero_of_nonempty_homeo_sphere` | `DegreeOneSphere.lean:673-678` | **SORRY** (`HasHolomorphicPrimitives X`, the de Rham wall — the snapshot's 4th sorry) |
| Analytic `genus RiemannSphere = 0` | `RiemannSphere.genus_eq_zero` | `ProjectiveLine.lean:614` | proven |
| Pullback of forms + functoriality | `pullbackForm`, `_id`, `_comp` | `HolomorphicForms.lean:110,193,204` | proven |
| Riemann–Roch equality | `exists_riemannRoch_divisor` | `RiemannRoch.lean:60-68` | proven **conditional on the keystone** (`exists_serreDualityData`, via `DolbeaultLadder`) |
| `deg(div f) = 0` | `MeromorphicFunction.deg_div` | `RiemannRoch.lean:76-79` | proven **unconditional** (proper-map-degree route) |
| `l(D)=0` for `deg D<0`; `l(K)=g`; `deg K=2g−2` | `RiemannRoch.lean:90,129,137` | unconditional / RR-conditional | proven |
| 1-form residue theorem (`∑Res = 0` for `ω₀·g`) | `residueTheorem_unconditional` | `Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean:1017` | proven unconditional (`g ≥ 1` shapes) |
| Meromorphic 1-form layer | `MeromorphicOneForm` | `Dolbeault/MeromorphicOneFormSystem.lean:73` | exists (Dolbeault tower) |
| Symplectic loops + R1/R2 bilinear relations | `CutSurface`, `cutSurface_R1/R2`, `toCanonicalDissection` | `CutSurfaceRelations.lean:59-146` | proven **conditional on `exists_cutSurface`** (`:158-161`, the cut-surface wall) |
| Period lattice has the 2g-loop ℝ-basis | `exists_periodLattice_realBasis` | `PeriodLattice.lean:855-860` | conditional on cut surface |
| Endpoint-independence of `mk ∘ periodVec` | `mk_periodVec_eq_of_endpoints` | `PeriodLattice.lean:200` | proven (free, since `truePeriodLattice` spans ALL closed-loop periods) |
| Path integration of forms | `lineIntegral` | `LineIntegral.lean:61` | **holomorphic forms only** — no meromorphic-form path integral |
| Third-kind differentials, reciprocity | — | — | **absent** (zero grep hits for third-kind/reciprocity) |

### Gap table

Severity: **M** = mechanical, **HS** = hard-but-standard, **RG** = research-grade.
Gates: **[K]** = keystone `exists_serreDualityData`, **[C]** = cut-surface
`exists_cutSurface`, **[dR]** = de Rham wall `HasHolomorphicPrimitives`, **[—]** = none.

| # | Sub-lemma | Existing infrastructure | Rating | Gate |
|---|---|---|---|---|
| **A1** | `div f = (P) − (Q)` ⇒ `f.HasSingleSimplePole Q`. Finsupp/`orderAtPoint` bookkeeping. | real `div`, `Abel.lean:531` | **M** | [—] |
| **A2** | Single simple pole ⇒ `X ≃ₜ ℂℙ¹` (and the underlying degree-1 holomorphic `F = f.toSphere Q`). | `DegreeOneSphere.lean:629` | done | [—] |
| **A3** | **Genus transport: conclude `genus X = 0`.** As architected the snapshot routes through `genus_zero_of_nonempty_homeo_sphere` = the de Rham wall [dR]. **Cheaper keystone-free reroute (our G3 pattern):** the degree-1 `F` is bijective holomorphic; prove its inverse `ContMDiff` (our `inverse_contMDiff_of_bijective_order_one`, `DegreeOneGenusZero.lean:388`), then `pullbackForm F` is a `LinearEquiv` via `pullbackForm_id`/`_comp` (`HolomorphicForms.lean:193,204`), so `genus X = genus RiemannSphere = 0` (`ProjectiveLine.lean:614`). Port of an existing proven route, not new math. | our `DegreeOneGenusZero.lean:388-451`, `GenusInvariance.lean:56`; their `HolomorphicForms.lean`, `ProjectiveLine.lean:614` | **HS** (port) | [—] |
| **B1** | **Third-kind differential existence**: `ω_{PQ}` with simple poles at `P, Q`, residues `+1/−1`, holomorphic elsewhere. Via RR at `K+P+Q` (`l(K+P+Q) ≥ g+1 > g = l(K)`) ⇒ a 1-form with at most simple poles at `P,Q`, not holomorphic; residues sum to 0 by `residueTheorem_unconditional` (applies: any meromorphic 1-form is `ω₀·(merom fn)` for `g ≥ 1`); normalize. Needs the `MeromorphicOneForm` ↔ `lSysModule(K+P+Q)` dictionary + a local-residue API at the `X` level. | `RiemannRoch.lean:60` [K]; `MeromorphicOneFormSystem`; `FormCoeff.lean:113` (`dz/z` witness) | **HS** given [K]; RG/axiom without | **[K]** |
| **B2** | **A-normalized holomorphic basis**: from the cut surface, `τ`-normalization `∮_{a_i} cω_j = δ_ij` (period-matrix block invertibility from R1/R2). Mostly present: `Dissection.lean` matrix engine + `periodVec_linearIndependent` + `exists_periodLattice_realBasis`. | `CutSurfaceRelations.lean:126-146`, `Dissection.lean:108-159`, `PeriodLattice.lean:855` | **M–HS** given [C] | **[C]** |
| **B3** | **Third-kind reciprocity** (Forster 20.7 / G–H p.230): for A-normalized `cω_j` and A-period-killed `ω̃_{PQ}`, `∮_{b_j} ω̃_{PQ} = 2πi ∫_Q^P cω_j`. NOT in the snapshot. Same box-Cauchy skeleton as `cutSurface_R1` (`CutSurface.lean:43-63`) but with `F_j · h_{PQ}` where `h_{PQ} = cut^*ω̃_{PQ}` has two log poles inside the box ⇒ needs a **rectangle-residue** variant of the box integral and a `CutSurface` interface extension carrying meromorphic pullback data (the current structure fields `h`,`hh` are holomorphic-on-`U` only, `CutSurfaceRelations.lean:74-80`). Upstream coordination required. | box machinery `CutSurface.lean`; Mathlib rectangle Cauchy | **HS-but-large** | **[C]** (+ interface change) |
| **B4** | **`u(P−Q)=0` ⇒ all periods of `ω̃_{PQ}` ∈ `2πiℤ`.** Translate `abelJacobi(P−Q) = 0` (i.e. `periodVec(sp(P₀,P)) − periodVec(sp(P₀,Q)) ∈ truePeriodLattice`) through B3's RHS: lattice membership decomposes over the 2g loop basis (`exists_periodLattice_realBasis` [C]), A-periods are killed by subtracting `∑(∮_{a_j}ω_{PQ})·cω_j`, B-periods land in `2πi(ℤ + τℤ)`-bookkeeping ⇒ `2πiℤ` after the holomorphic correction. Path-matching `∫_Q^P cω_j` vs `smoothPath` differences via `mk_periodVec_eq_of_endpoints` (`PeriodLattice.lean:200`). Pure linear algebra + lattice bookkeeping over proven interfaces. (Caution from our route doc: the condition is `2πiℤ`, NOT "purely imaginary".) | `PeriodLattice.lean:80-84,200,855` | **HS** | **[C]** |
| **B5** | **Exp recovery**: `f := exp(∫_{P₀}^{·} ω̃_{PQ})` single-valued on `X∖{P,Q}`, extends meromorphically with `div f = P − Q`. Needs (i) a path integral for forms holomorphic on the **open** submanifold `X∖{P,Q}` — the snapshot's `lineIntegral` (`LineIntegral.lean:61`) is typed at `HolomorphicOneForms X` on compact `X` only; (ii) monodromy: closed-loop integrals of `ω̃_{PQ}` ∈ `2πiℤ` for ALL loops in `X∖{P,Q}` — note loops encircling `P` or `Q` pick up residue `±2πi` (∈ `2πiℤ`, fine) on top of the lattice loops, so the generation statement needed is "H₁ of the punctured surface = lattice loops + small circles", an extension of the `generates` field (`CutSurfaceRelations.lean:66-67`); (iii) local `exp(±log z + holo) = z^{±1}·unit` Laurent matching at `P,Q`. Largest single block of genuinely new plumbing. | `SmoothPath` machinery, `mk_periodVec_eq_of_endpoints`; Mathlib `Complex.exp`/log | **HS-but-large** | [C] for (ii); (i),(iii) **[—]** |
| **B6** | Assembly: B1–B5 ⇒ `∃ f, div f = P − Q`; then A1–A3 ⇒ contradiction. | — | **M** | — |

**No new research-grade object.** Unlike the keystone (whose S3 `res` construction is RG as
architected), every Abel-wall piece is M/HS *given the two upstream walls*; the
research-grade content of this wall lives entirely in the walls it sits on.

### Keystone dependency — the explicit verdict

**The Abel wall is only marginally downstream of the keystone.** If
`exists_serreDualityData` falls (our B3 workstream), exactly ONE new piece becomes
available: `exists_riemannRoch_divisor` (`RiemannRoch.lean:60`) and its corollaries
`l(K)=g`, `deg K = 2g−2` — which unlock **B1 only** (third-kind existence). Everything
else is keystone-independent:

- **A1–A3** (the whole genus-obstruction half): independent of both walls; blocked today
  only by the snapshot's own de Rham-wall routing, which the A3 reroute removes.
- **B2–B4**: gated on the **cut-surface wall** (`exists_cutSurface`,
  `CutSurfaceRelations.lean:158`), not the keystone.
- **B5**: mostly wall-independent plumbing (meromorphic path integrals, punctured-surface
  monodromy, local Laurent).

So the honest dependency picture is: **Abel wall = f(keystone, cut-surface, + ~60% own
content)**, with the cut-surface wall the heavier of the two gates (three pieces vs one).
The keystone falling does NOT unlock this wall; it removes one of three gates.

---

## 4. Recommended attack order

1. **A3 reroute first (1–2 weeks, START NOW — keystone- and cut-surface-free).** Port our
   G3 genus-transport route (`inverse_contMDiff_of_bijective_order_one` →
   `pullbackForm` LinearEquiv → `genus X = genus ℂℙ¹ = 0`) onto the snapshot's
   `degreeOne_homeo` output. This (a) closes the genus-obstruction half A1–A3 of THIS wall
   without touching `HasHolomorphicPrimitives`, and (b) as a free by-product discharges the
   snapshot's 4th sorry (`DegreeOneSphere.lean:678` backward headline) by the same
   transport — two walls' worth of `[dR]` dependency deleted with one ported lemma.
   Coordinate with rkirov (it changes the advertised route of his backward headline).
2. **A1 (days).** The `div f = P−Q ⇒ HasSingleSimplePole` Finsupp bookkeeping.
3. **B-half engine (2–3 weeks, parallel, Phase-C recipe).** State-vet two primitives —
   `exists_thirdKind` (B1's statement) and `thirdKind_reciprocity` (B3's statement) — and
   build an axiom-free engine `twoPoint_principal_of_AJ_zero_of_inputs :
   ThirdKindInputs → abelJacobi (P−Q) = 0 → ∃ f, div f = P−Q` running B4+B6 against the
   proven lattice API (`exists_periodLattice_realBasis`, `mk_periodVec_eq_of_endpoints`).
   This isolates the wall to named geometric inputs and proves the bookkeeping correct
   now, exactly as the keystone plan's S7 does for §17.9.
4. **B5 plumbing (3–5 weeks, parallel, wall-independent).** Meromorphic/open-submanifold
   `lineIntegral` extension + the local `exp∘log` Laurent matching; the punctured-surface
   generation statement (B5-ii) designed jointly with the cut-surface wall's `generates`
   interface.
5. **B3 after the cut-surface interface stabilizes.** It is the same box machinery as
   `cutSurface_R1` and must extend the `CutSurface` structure — negotiate the field design
   with rkirov in the same conversation as the cut-surface wall itself (the
   [`CUTSURFACE_GAP_ANALYSIS.md`](CUTSURFACE_GAP_ANALYSIS.md) coordination items).
6. **B1 last, when the keystone falls** (or earlier as a vetted interface axiom on our
   side, matching `AX_RiemannRoch`'s role in `ABEL_SUBSET_FORSTER_ROUTE.md`).

**Worth starting before the keystone falls: items 1–4 — about 70% of the wall.** Only B1
genuinely waits, and even its *statement* should be frozen now (step 3).

### Bridge option (our repo, independent of all of the above)

Since their sorry ≈ (our `AX_AbelTheorem` ⊆-instance) ∘ (our proven
`principal_imp_eq_of_genus_pos`), a Phase-D bridge between their
`abelJacobi`/`truePeriodLattice` Jacobian and ours would let either side's progress flow:
their proof would retire `AX_AbelTheorem` from our challenge-critical cone (its sole
consumer is `OfCurveInjective.lean:34`); until then, our axiom discharges their sorry in
any bridged build. The bridge is the already-scoped type-alignment work
(`PHASE_D_TYPE_ALIGNMENT.md`), not new math.

## 5. Bottom line

The sorry is the snapshot's **headline gap** (sole blocker of `ofCurve_inj`,
`Jacobians.lean:278`). It packages the **hard ⊆ direction of Abel at two-point divisors**
plus the **genus obstruction**. The obstruction half is essentially solved — proven in our
repo axiom-clean, and portable to the snapshot in 1–2 weeks, simultaneously deleting the
snapshot's de Rham-wall sorry. The ⊆ half is hard-but-standard *assembly* with no new
research-grade object, but it sits on BOTH other walls: third-kind existence needs the
keystone (RR), period normalization/reciprocity needs the cut surface, and ~half its bulk
(reciprocity-with-poles, exp recovery, meromorphic path integrals) is wall-independent
plumbing absent from the snapshot. Estimated: A-half 2 weeks; B-half engine + plumbing
5–8 weeks parallelizable now; B1/B3 land only after the keystone / cut-surface walls
respectively.
