# Axioms needed to close Buzzard's challenge

> **★ STATUS (current).**
>
> **(1) Buzzard challenge-critical count = 0** (since 2026-06-14, PR #251). Every Buzzard
> headline is `#print axioms` = standard-3; `AX_PeriodCycleBasis` — the last challenge-critical
> axiom — appears in **no headline closure** (`docs/axiom-report.txt`: 0 mentions). It was
> discharged from the headlines by reproving the global period-lattice instances from the
> unconditional T-GEN theorem (`analyticLoopsGenerateH1`, PR #248) and routing `ofCurve_inj`
> through the basis-free engine, enabled by the ℙ¹-instance unification (PR #250).
> `AX_PeriodCycleBasis` remains a *declared* axiom backing the non-headline Layer-3 R1/R2
> scaffolding and cycle-basis witnesses; deleting it from the repo needs R1/R2 (Riemann
> bilinear relations) in general.
>
> **(2) The Albanese universal-property characterization is now also axiom-free** (beyond the
> challenge). The four legacy Albanese-torus axioms in §ii below were discharged/escaped
> (PRs #232 / #253, 2026-06-14), and the last curve-side axiom **AK
> (`AX_curve_image_subgroup_isOpen`) was discharged 2026-06-16 in PR #255** (@daouid) — so
> `ofCurve_isJacobian` prints standard-3 and `isJacobian_unique` was already axiom-free. The
> one remaining Albanese input, A1 `AX_torus_uniformization`, is *declared but off every
> headline closure*.
>
> **Everything below this banner is the historical discharge record.** The countdown narrative
> and its interim counts ("22 remaining axioms", "the 2", "16 non-critical") are as-of-writing
> snapshots, superseded by this banner. The live, kernel-verified picture is
> `AXIOM_AUDIT.md` + `docs/axiom-report.txt`.

*Authoritative source: `docs/axiom-report.txt` (kernel-verified `#print axioms` for the
challenge property theorems and the concrete-curve headlines). The Jacobian typeclass
instances are now also covered: `scripts/axiom_report.lean` includes wrapper theorems
for all 7 Buzzard instance obligations (T2Space, CompactSpace, ConnectedSpace,
ChartedSpace, IsManifold, LieAddGroup, AddCommGroup). Reconciled 2026-06-11
(post-D1 + the #161 trace-cluster discharge + the #52 `PlaneCurve.instIsManifold`
discharge + the PR #179 `AX_ofCurve_contMDiff` discharge, which dropped the
challenge-critical count 7 → **6** + the PR #183 odd-atlas ∞-chart cluster
discharge, −7 non-critical + the #30 `AX_pushforwardAmbient_preserves_lattice`
discharge, which dropped the challenge-critical count 6 → **5** + the #31
functoriality-cluster completion, 5 → **3** + the genus-0 uniformization flip
(PR #209, parallel account, 2026-06-11), which discharged
`AX_genus_eq_zero_iff_homeo` — the challenge headline
`genus_eq_zero_iff_homeo` now prints standard-3 — dropping the
challenge-critical count 3 → **2**) against the
21-axiom table.*

> **STATUS NOTE — D1 merge + trace discharge (2026-06-10).** The challenge-critical
> count dropped **13 → 7** (D1 merge −3+1 −intersectionForm; #161 trace-cluster
> discharge −3): `AX_AnalyticCycleBasis` + `AX_RBR1` + `AX_RBR2` were merged into
> the single **`AX_PeriodCycleBasis`** (loops + H₁ basis + Hurewicz tie + the two
> Riemann bilinear relations stated arc-level over the bundle's own loops —
> `docs/planning/CYCLEBASIS_ALTERNATIVES.md` §1, owner-approved, DT-vetted), and
> **`intersectionForm` exited every Buzzard closure** (the structure's
> proof-unconsumed `symplectic` field, its only headline route, was dropped;
> the form + its 2 laws are kept as non-critical Part-3 debt per owner decision
> D2). Kernel evidence: `docs/axiom-report.txt` post-D1 regeneration. Cluster
> text below has been updated; A1/A2 are now a single Cluster A.

---

## What "closing the challenge" means

Buzzard's `Challenge.lean` (v0.4) poses 24 `sorry`-obligations in two groups:

**Property theorems** (12): `genus_eq_zero_iff_homeo`, `ofCurve_self`, `ofCurve_inj`,
`ofCurve_contMDiff`, `pushforward_contMDiff`, `pushforward_id_apply`,
`pushforward_comp_apply`, `pullback_contMDiff`, `pullback_id_apply`,
`pullback_comp_apply`, `pushforward_pullback`, `ContMDiff.degree`.

**Typeclass instances** (7 required): `TopologicalSpace`, `T2Space`, `CompactSpace`,
`ChartedSpace`, `IsManifold`, `LieAddGroup`, `AddCommGroup` on `Jacobian X`.
`ConnectedSpace` is also provided but is explicitly **not** one of Buzzard's 7 —
Challenge.lean line 105 marks it as extra, needed for the Albanese universal property.

All 24 are filled; `ChallengeConformance.lean` machine-checks every v0.4 signature
(`lake env lean ChallengeConformance.lean`, exit 0). **But filling a `sorry` with an
`axiom` is not the same as proving it.** This document identifies: which of the 22
remaining axioms must be discharged to produce a fully axiom-free challenge closure?

---

## What filling the 2 does — and does not — claim

Discharging the remaining axiom makes every Buzzard declaration print exactly
`[propext, Classical.choice, Quot.sound]` — the same closure as Mathlib
itself. That is the strongest claim the kernel can express, it is enforced
continuously by the regenerate-and-diff CI gate on `docs/axiom-report.txt`,
and it should be certified at the end by a comparator run (kernel replay +
axiom whitelist, `~/.claude/COMPARATOR.md` protocol) on the headline
declarations. Four boundaries to keep the claim honest:

1. **Kernel trust ≠ review trust.** Post-discharge the solution rests on
   Mathlib *plus this repo's ~50k LOC and the vendored port* — all
   kernel-checked to standard-3, none human-reviewed. The kernel guarantee
   is identical to Mathlib's; the social provenance is not. The README's
   LLM-authorship disclaimer remains load-bearing.
2. **Definitional faithfulness is not an axiom question.** A degenerate
   definition can be standard-3. This is covered by the challenge's own
   design, not by the axiom count: the anti-degeneracy property theorems
   are among the 24 obligations, and `ChallengeConformance.lean`
   machine-checks every signature verbatim against the pinned v0.4 spec —
   a hollow construction provably cannot satisfy both.
3. **2 is the end-state count, not the work count.** Discharge routes pull
   in their own mathematics (e.g. `AX_AbelTheorem` classically routes
   through the RR/Serre tower, so the Serre keystone — not itself in the
   7 — is on the path). The set may grow transiently if a discharge
   introduces a new textbook axiom; the CI guard makes any such step
   visible, and the claim lands only when the challenge cone hits zero.
4. **`AX_ofCurve_contMDiff` — DISCHARGED 2026-06-11 (PR #179, @Deicyde),
   with the conditionality transferred, not settled.** The chart-line
   descent proof makes Abel–Jacobi smoothness a theorem (standard-3 +
   `AX_PeriodCycleBasis` only). But the 2026-06-10 DT flag's
   HI/lattice-completeness condition is NOT settled by this proof — the
   `Classical.choice` path discrepancy is landed in the lattice via the
   cycle-basis `loops_to_basis` pin, so the condition transfers into
   `AX_PeriodCycleBasis`'s discharge obligation (the `loops_to_basis`
   pin), where it belongs. Filling the 2 therefore still includes
   settling X1, now inside the Cluster-A discharge.

## The 2 challenge-critical axioms

> **STATUS NOTE — functoriality-cluster completion (#31, 2026-06-11).** The last
> two Cluster-C axioms — `AX_pullbackAmbient_preserves_lattice` and
> `AX_pushforward_pullback` — are now **theorems** (route per daouid's closed
> PR #191, with the lattice-comparison inclusions proven in
> `Bridge/KirovDolbeaultPeriods.lean` / `Bridge/KirovDolbeaultLattice.lean`).
> Challenge-critical count **5 → 3**: `AX_PeriodCycleBasis`,
> `AX_genus_eq_zero_iff_homeo`, `AX_AbelTheorem` (since 2026-06-12: its split remainder `AX_AbelSupset`). Sections below retain the
> pre-discharge analysis for the record.

> **STATUS NOTE — genus-0 uniformization flip (PR #209, parallel-account
> delivery, 2026-06-11).** `AX_genus_eq_zero_iff_homeo` is now a **theorem**
> (forward: keystone-backed RR pole extraction → degree-one map →
> `degreeOne_equiv_projectiveLine` → stereographic `S²`,
> `RiemannSurface/GenusZeroForward.lean`; backward: S2-lane
> `genus_eq_zero_of_homeo_sphere_unconditional`, #199+#205). The challenge
> headline `genus_eq_zero_iff_homeo` prints standard-3. Challenge-critical
> count **3 → 2**: `AX_PeriodCycleBasis`, `AX_AbelTheorem`.
>
> **ABEL SPLIT-FLIP (2026-06-12, feat/abel-flip lane).** `AX_AbelTheorem` is now a
> **theorem**: ⊆ (the hard half) proven via the unconditional Forster §20
> weak-solution engine + the E6 adapter (`Bridge/AbelEngineAdapter.lean`,
> `abel_subset` standard-3 + `AX_PeriodCycleBasis`); ⊇-degree half proven
> (`deg_divisor_eq_zero`); the ⊇ Abel–Jacobi half survives as the strictly-smaller
> remainder axiom **`AX_AbelSupset`** (`PrincipalDivisors ≤ ker abelJacobiDiv`,
> Liouville route `docs/planning/ABEL_SUPSET_LIOUVILLE_ROUTE.md`). Honest count:
> challenge-critical stays **2** (`AX_PeriodCycleBasis`, `AX_AbelSupset`) — the
> only headline affected is `ofCurve_inj`, whose closure swaps
> `AX_AbelTheorem` → `AX_AbelSupset`. Kernel log:
> `docs/planning/ABEL_FLIP_VERIFICATION.log`.
>
> **ABEL ⊇ FLIP (2026-06-12, SUP lane `feat/abel-supset`).** `AX_AbelSupset` is
> now a **theorem** — the planned Liouville / symmetric-product route executed
> in full (S1–S7 of `docs/planning/SUP_ROUTE.md`): the Jacobi pencil map
> `Φ(y) = AJ(f⁻¹(y))` is `ContMDiffAt` at regular values (local holomorphic
> sections of the pencil, `AbelSupsetSections.lean`), continuous everywhere and
> `MDifferentiable` across the branch values (kfold cluster decomposition +
> manifold-valued removable singularity, `AbelSupsetPencil.lean`), and constant
> by the lattice-covering lift over the simply connected `ℙ¹` + Liouville
> (`AbelSupsetLiouville.lean`); `abel_supset_of_fiberAJConstancy` closes the
> statement verbatim in place. **Challenge-critical count 2 → 1:
> `AX_PeriodCycleBasis` alone.** Every Buzzard headline — including
> `ofCurve_inj` and `AX_AbelTheorem` — now prints standard-3 +
> `AX_PeriodCycleBasis`. Kernel log: `docs/planning/ABEL_FLIP_VERIFICATION.log`
> (SUP section).

Exactly this axiom appears in `#print axioms` for one or more Buzzard declarations
(from `docs/axiom-report.txt`, which now covers both property theorems and instance
obligations). Discharging it gives a challenge closure over only
`[propext, Classical.choice, Quot.sound]`.

### Cluster A — Core Jacobian structure (appears in ALL Buzzard declarations)

Since the D1 merge this is a single axiom. It appears even in the definitional
declarations (`Jacobian`, `ofCurve`) and in the lightweight instances
(`AddCommGroup`, `TopologicalSpace`, `ConnectedSpace`) — they underlie the
construction `Jac X = (HolomorphicOneForm X)* / H₁` — and, through its R1/R2
fields feeding `instPeriodLatticeDiscrete`, also in the smoothness theorems and
the 5 heavier Jacobian instances (`T2Space`, `CompactSpace`, `ChartedSpace`,
`IsManifold`, `LieAddGroup`).

| Axiom | Precise Lean statement | Mathematical content | Discharge path |
|---|---|---|---|
| `AX_PeriodCycleBasis` | `Nonempty (PeriodCycleBasis X x₀)` — 2g analytic loops whose classes are a ℤ-basis of H₁ (with the Hurewicz tie `loops_to_basis`), satisfying the Riemann bilinear relations **arc-level** over their own canonical arc integrals: R1 `Q(P(η),P(ζ)) = 0`, R2 `0 < Re(i·Q(P(η), conj P(η)))` for `η ≠ 0`, where `arcPeriodVec` splits A/B-periods through `αEmbed`/`βEmbed` in exactly `Q`'s layout (simp-pinned) | The canonical homology basis of a compact Riemann surface together with Riemann's bilinear relations. Standard: Griffiths–Harris Ch. 2 §2; Forster §§19–21. D1 merge of the former `AX_AnalyticCycleBasis` + `AX_RBR1` + `AX_RBR2`; strictly weaker-or-equal than that trio (satisfiability inherited from their 2026-06-09 DT vets). | Loops + basis from a dissection (4g-gon, or post-keystone the branched-cover slit-sheet route, `docs/planning/CYCLEBASIS_ALTERNATIVES.md` §2b); R1 by Stokes on the cut surface (the Kirov port's proven `riemann_R1_of_boundaryWord` is the engine); R2 from the Hodge norm (`riemann_R2_posDef_of_boundaryWord`, hardest ingredient — no Lean Hodge theory exists). The genus-comparison gate (`Fin (2·genus X)` rank pin) binds every route. |

**Note on `intersectionForm` (post-D1).** The form and its two law axioms are
**no longer challenge-critical**: the old structure's `symplectic` field — their
only route into the headline closures — had zero proof consumers and was dropped
in the merge. They remain in the build as Part-3 topological-anchoring debt
(owner decision D2; see §Not critical). When `AX_PeriodCycleBasis` is eventually
discharged by a genuine dissection, re-tying the form to that dissection is the
recorded joint obligation.

### Cluster B — ALL DISCHARGED (`AX_AbelSupset` discharged 2026-06-12 SUP lane; uniformization discharged PR #209, smoothness discharged PR #179)

Each appears in exactly one Buzzard declaration and has its own proof path.

| Axiom | Mathematical content | Discharge path |
|---|---|---|
| `AX_genus_eq_zero_iff_homeo` | ✅ **DISCHARGED 2026-06-11** (PR #209, parallel-account delivery) — `genus X = 0 ↔ X ≅ₜ S²` is now a theorem, both directions | Forward: keystone-backed RR pole extraction (`h⁰((p)) = 2` at `g = 0`) → `exists_degreeOne_of_genus_zero` → `degreeOne_equiv_projectiveLine` → stereographic `S²` (`RiemannSurface/GenusZeroForward.lean`). Backward: S2-lane `π₁(S²) = 1` + Liouville developing map (`genus_eq_zero_of_homeo_sphere_unconditional`, #199+#205). The concrete `genus ℙ¹ = 0` was already axiom-free via Liouville. |
| `AX_AbelSupset` | ✅ **DISCHARGED 2026-06-12** (SUP lane) — `PrincipalDivisors ≤ ker abelJacobiDiv` is now a theorem; with it the full `AX_AbelTheorem` is a theorem at standard-3 + `AX_PeriodCycleBasis` | Forster §20.7. The ⊆ direction was PROVEN 2026-06-12 via the Forster §20 weak-solution engine + E6 adapter; the degree half of ⊇ is `deg_divisor_eq_zero`; the AJ half of ⊇ closed on the Liouville / symmetric-product route (`ABEL_SUPSET_LIOUVILLE_ROUTE.md`, executed as `SUP_ROUTE.md` S1–S7: pencil sections → cluster continuity → removable singularity → covering lift → Liouville). |
| `AX_ofCurve_contMDiff` | ✅ **DISCHARGED 2026-06-11** (PR #179, @Deicyde) — Abel–Jacobi smoothness is now a theorem (chart-line descent; standard-3 + `AX_PeriodCycleBasis` only) | **Transfer note:** the 2026-06-10 DT flag's HI/lattice-completeness condition is NOT settled by this proof — it transfers into `AX_PeriodCycleBasis`'s discharge obligation (the `loops_to_basis` pin), where it belongs. |

### Cluster C — Functoriality block

Six entries, ALL now **discharged** (the trace trio; the pushforward
lattice-preservation #30; and `AX_pullbackAmbient_preserves_lattice` +
`AX_pushforward_pullback`, #31/#34, 2026-06-11 — the cluster is fully closed). All appear in the `pushforward`/`pullback` declarations. The dependency structure
within the cluster is more nuanced than "all follow from one root":

| Axiom | Primary dependency | Role |
|---|---|---|
| `pushforwardOneForm` | core trace construction | The fiber-sum trace `Tr_f(ω)` of a 1-form ω along f: needed for `pullback` (defined as `(Tr_f)ᵀ`), `pullback_id`, `pullback_comp`, `pushforward_pullback` |
| `AX_pushforwardOneForm_id` | `pushforwardOneForm` real | `Tr_id = id`; immediate once the trace is real |
| `AX_pushforwardOneForm_comp` | `pushforwardOneForm` real | `Tr_{g∘f} = Tr_g ∘ Tr_f`; functoriality of the fiber sum |
| `AX_pushforwardAmbient_preserves_lattice` | ✅ **DISCHARGED 2026-06-11** (#30) | Now a theorem: `∫_{f_*(γ)} ω = ∫_γ f*ω` realized by the developing-value naturality engine (`DevelopingNaturality.lean` + `LoopLattice.lean`, axiom-free) over the Kirov-backed `pullbackOneForm`; representative-loop induction, the image cycle is the honest loop `f∘γ`. Headlines `pushforward`/`_contMDiff`/`_id_apply`/`_comp_apply` now standard-3 + `AX_PeriodCycleBasis`. |
| `AX_pullbackAmbient_preserves_lattice` | ✅ **DISCHARGED 2026-06-11** (#31) | Now a theorem: lattice vector → port coordinates (polygonal smooth representative of the `H1` class), port `PreimageCycle` monodromy (`ambientPullbackJac_preserves_truePeriodLattice`), back via developing value = moving-chart line integral. Route per daouid's closed PR #191 (credit), inclusions proven. |
| `AX_pushforward_pullback` | ✅ **DISCHARGED 2026-06-11** (#31) | Now a theorem: ambient `Φ ∘ Tᵀ = deg • id` from the port's conservation-of-number over the lattice's ℝ-spanning ℤ-basis + `degreeImpl_eq_degreeFiber`; quotient descent. NOT via a form-level `Tr_f(f*ω) = deg(f)·ω` (the port does not have that law; the identity lives at the period level). |

> **Status 2026-06-10:** the first three rows — `pushforwardOneForm`,
> `AX_pushforwardOneForm_id`, `AX_pushforwardOneForm_comp` — are **DISCHARGED**
> (#26/#27/#28): real def/theorems via the Kirov-Dolbeault port's fibre-sum trace
> `traceFormTotal`, transported across `Bridge/KirovDolbeaultTrace.lean`
> (standard-3). Together with the D1 merge the challenge-critical count is now **7**;
> `AX_pullbackAmbient_preserves_lattice` is no longer trace-gated by an axiom —
> it is the dual of a REAL trace.

With the trace real and the pushforward lattice statement a theorem (#30),
**(historical)** the remaining Cluster-C axioms were
`AX_pullbackAmbient_preserves_lattice` and `AX_pushforward_pullback` — both
**discharged 2026-06-11 (#31)**: rather than the trace-side fibre-sum
coefficient law for `developingValue` (which would have required re-deriving
the monodromy decomposition in our framework), the discharge transports the
whole problem into the Dolbeault port across the proven
`truePeriodLattice ↔ periodLatticeInBasis` correspondence and reuses the
port's `PreimageCycle` machinery. Cluster C is now **fully discharged**.

---

## The 16 non-challenge-critical axioms

### i. Intersection form + laws (3) — out of the challenge cone since D1

| Axiom | Why not critical |
|---|---|
| `intersectionForm` | **Exited every headline closure in D1 (2026-06-10)**: its only route was the old structure's proof-unconsumed `symplectic` field, now dropped. Kept per owner decision D2 as Part-3 topological-anchoring debt. |
| `AX_IntersectionForm_alternating` | Never consumed by any proof; fully orphaned post-D1 |
| `AX_IntersectionForm_perfect` | Period-lattice discreteness is proved from the bundle's R1/R2 fields directly, bypassing this law |

*All three become redundant theorems once `intersectionForm` is discharged to a
real construction that already satisfies them (the #16+#22 joint plan).*

### ii. Albanese universal property — our addition beyond Buzzard (✅ ALL DISCHARGED)

Underlie `ofCurve_isJacobian` (the Albanese `∃!` factorization), our strongest
anti-degeneracy result. Buzzard's v0.4 does not require it. The 2026-06-14 repoint
refactor (PR #253) replaced the four legacy torus axioms below with a smaller, vetted
interface — A1 `AX_torus_uniformization` + AK `AX_curve_image_subgroup_isOpen`. All four
legacy axioms, and then AK itself, are now discharged, so **`ofCurve_isJacobian` is
axiom-free (standard-3)**. A1 remains *declared but off every headline closure*.

| Axiom | Content | Status |
|---|---|---|
| `AX_torus_oneforms_dualCover` | Every complex torus is covered by the dual of its holomorphic 1-forms | ✅ discharged #232 (now a `def`) |
| `AX_torus_self_albanese` | A complex torus is its own Albanese variety | ✅ discharged 2026-06-14 (now theorem `torus_self_albanese`, = A1) |
| `AX_period_functoriality` | Period maps commute with holomorphic maps | ✅ discharged 2026-06-14 (theorem, from A1 + bridge) |
| `AX_curve_generates_jacobian` | The image of the curve generates the Jacobian as a group | ✅ discharged 2026-06-14 (from AK; AK discharged PR #255 ⇒ transitively axiom-free) |
| `AX_curve_image_subgroup_isOpen` (AK) | Abel–Jacobi image generates a subgroup with non-empty interior (local Jacobi inversion) | ✅ **discharged 2026-06-16 PR #255** (@daouid) — std-3 |

### iii. RR/Serre coherence depth (5) — mathematical depth, not Buzzard requirements

Needed to prove RR and Serre as theorems. The challenge's key properties (Jacobian
construction, ofCurve, functoriality) do not depend on RR/Serre.

| Axiom | Content | Status |
|---|---|---|
| `h1coh_zero_finrank` | h¹(𝒪_X) = genus X | Frontier; gates full Serre duality |
| `serreDuality_equiv` | H¹(D) ≃ L(K−D)* as ℂ-spaces | Frontier; needs `canonicalDivisor` real first |
| `LineBundle` | Type stub for line bundles | ✅ **DISCHARGED 2026-06-12** (stub retirement) — real `def`, the divisor-indexed tag structure; RR/Serre statements now fully standard-3 |
| `canonicalDivisor` | The canonical divisor K | ✅ **DISCHARGED 2026-06-11** (keystone flip) — the chosen Serre divisor |
| `LineBundle.ofDivisor` | The line bundle O(D) | ✅ **DISCHARGED 2026-06-12** (stub retirement) — canonical inhabitant of the de-opaqued tag type |

### iv. Plücker formula (1) — plane curve specific, Part 3 only

`AX_PluckerFormula`: `genus(C) = (d−1)(d−2)/2` for a smooth degree-d plane curve.
Follows from Riemann–Hurwitz or the adjunction formula; neither in Mathlib currently.

### v. Concrete curve witnesses (3) — Part 3 vetting only

| Group | Axioms |
|---|---|
| Elliptic | `AX_Elliptic_H1_symplectic` *(DISCHARGED 2026-06-12, PR #228 — now the proven `ellipticPeriodCycleBasis`)* |
| Hyperelliptic | `AX_Hyperelliptic_genus` (the 7-axiom odd-atlas ∞-chart cluster — `infinityChart`, `infinityInverseMap`, `mem_source`, 4 compats — **discharged PR #183**, 2026-06-11, correct analytic branch; `Hyperelliptic.instChartedSpace`/`instIsManifold` now standard-3) |
| Plane curve | `AX_PlaneCurveAffine_connected` (`PlaneCurve.instIsManifold` **discharged #52**, 2026-06-10) |

---

## Summary: the closure picture

```
2 challenge-critical axioms (3 before the PR #209 genus-0 flip, 2026-06-11)
    │
    ├── Cluster A (1) — in EVERY Buzzard declaration
    │      AX_PeriodCycleBasis  (D1 merge: loops + H₁ basis + Hurewicz tie
    │                            + arc-level R1 (Stokes) + R2 (Hodge ≻ 0))
    │      Needs: dissection/branched-cover topology for the basis;
    │      Stokes for R1; Hodge positivity for R2 ← hardest, no Lean proof
    │      Kirov port has the proven boundary-word engine for R1/R2
    │
    ├── Cluster B (1) — one independent classical theorem
    │      AX_AbelSupset
    │      (AX_genus_eq_zero_iff_homeo — discharged PR #209, parallel
    │       account: RR pole extraction forward, S2-lane π₁(S²)=1 backward)
    │      (AX_ofCurve_contMDiff — discharged PR #179, conditionality
    │       transferred to AX_PeriodCycleBasis's loops_to_basis pin)
    │
    └── Cluster C (2) — functoriality over now-real maps
           (trace trio discharged #26/#27/#28 via the Kirov-Dolbeault bridge;
            AX_pushforwardAmbient_preserves_lattice discharged #30 via the
            developing-value naturality engine)
```

### Bottleneck assessment

**Cluster A's R2 field** is the single hardest barrier. Hodge positivity requires
L² theory / harmonic forms on a compact Riemann surface — no Lean proof exists anywhere.

**Cluster A's basis half** needs dissection topology (4g-gon, or the branched-cover
slit-sheet route post-keystone — `docs/planning/CYCLEBASIS_ALTERNATIVES.md`). The
older discharge analysis is in `docs/planning/AX_AnalyticCycleBasis.md`. DT-vetted.

**Cluster B**: Uniformization (`AX_genus_eq_zero_iff_homeo`) — formerly the
deepest single theorem — was **discharged in PR #209** (genus-0 flip: RR pole
extraction forward, S2-lane simple connectedness + Liouville backward).
`AX_AbelSupset` is now DISCHARGED (Liouville pencil route, this PR) (the ⊇/AJ half; the former hard ⊆ half is now a theorem via the §20 engine).
(`AX_ofCurve_contMDiff` was discharged in PR #179; its HI/lattice-completeness
conditionality now lives in Cluster A's discharge obligation.)

**Cluster C**: the trace trio is discharged (#26/#27/#28) and the pushforward
lattice statement is a theorem (#30, developing-value naturality engine), so
nothing in the cluster is gated by an opaque construction: the remaining
lattice-preservation axiom is a period-naturality statement about the dual of
the REAL trace (the #30 engine is the template; the missing piece is the
fibre-sum coefficient law for `pushforwardOneForm`), and push-pull is the
projection formula `Tr_f(f*ω) = deg(f)·ω`.
Miranda (3.1) / Kirov port's `Discharge/Manifold/` machinery are the closest reference.

---

## Relationship to the Layer-3 tower

The Layer-3 tower (Phases B–D) contains two distinct parts with different relationships
to challenge closure:

**Phase C period primitives (formerly `AX_RBR1`, `AX_RBR2`; since D1 the R1/R2
fields of `AX_PeriodCycleBasis`)** — these ARE challenge-critical (Cluster A
above). They were introduced by the tower as primitives for proving the
period-cluster theorems, and sit in the challenge's dependency chain via
`instPeriodLatticeDiscrete` (a theorem over the chosen bundle witness).

**The RR/Serre cohomology branch** (`h1coh_zero_finrank`, `serreDuality_equiv`,
line-bundle stubs) — this IS orthogonal to challenge closure. These axioms do not appear
in any Buzzard `#print axioms`. The tower's RR/Serre discharge deepens mathematical
trust without touching either of the 2 (though the keystone-backed RR it proved
is exactly what powered the PR #209 forward leg).

The tower's indirect contribution to eventual challenge closure: the Kirov port
integrated in Phase D contains `residueTheorem_unconditional` and the proven
boundary-word R1/R2 engine (relevant to the R1/R2 fields of `AX_PeriodCycleBasis`)
and the branched-cover degree machinery (relevant to `pushforwardOneForm`).
