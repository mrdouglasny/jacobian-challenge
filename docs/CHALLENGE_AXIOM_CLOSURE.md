# Axioms needed to close Buzzard's challenge

*Authoritative source: `docs/axiom-report.txt` (kernel-verified `#print axioms` for the
challenge property theorems and the concrete-curve headlines). The Jacobian typeclass
instances are now also covered: `scripts/axiom_report.lean` includes wrapper theorems
for all 7 Buzzard instance obligations (T2Space, CompactSpace, ConnectedSpace,
ChartedSpace, IsManifold, LieAddGroup, AddCommGroup). Reconciled 2026-06-10
(post-D1 + the #161 trace-cluster discharge + the #52 `PlaneCurve.instIsManifold`
discharge) against the 30-axiom table.*

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
`axiom` is not the same as proving it.** This document identifies: which of the 30
remaining axioms must be discharged to produce a fully axiom-free challenge closure?

---

## What filling the 7 does — and does not — claim

Discharging all 7 makes every Buzzard declaration print exactly
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
3. **7 is the end-state count, not the work count.** Discharge routes pull
   in their own mathematics (e.g. `AX_AbelTheorem` classically routes
   through the RR/Serre tower, so the Serre keystone — not itself in the
   7 — is on the path). The set may grow transiently if a discharge
   introduces a new textbook axiom; the CI guard makes any such step
   visible, and the claim lands only when the challenge cone hits zero.
4. **`AX_ofCurve_contMDiff` is the conditional one.** Its 2026-06-10
   deep-think vetting pinned its *truth* to the completeness of the
   `periodMap`/H1 model (homotopy invariance of the arc integral — the
   parked X1 workstream). Filling the 7 therefore includes settling X1;
   it cannot stay parked if axiom-free closure is the goal.

## The 7 challenge-critical axioms

Exactly these axioms appear in `#print axioms` for one or more Buzzard declarations
(from `docs/axiom-report.txt`, which now covers both property theorems and instance
obligations). Discharging all 7 gives a challenge closure over only
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

### Cluster B — Three independent classical theorems

Each appears in exactly one Buzzard declaration and has its own proof path.

| Axiom | Mathematical content | Discharge path |
|---|---|---|
| `AX_genus_eq_zero_iff_homeo` | `genus X = 0 ↔ X ≅ₜ S²` — uniformization for genus 0 | Forster §27. Wallace's GenusZero route (degree-1 cover → biholomorphism to ℙ¹) has the most Lean progress. The concrete `genus ℙ¹ = 0` is already proved axiom-free via Liouville. |
| `AX_AbelTheorem` | Degree-0 kernel of `abelJacobiDiv` = `PrincipalDivisors` — Abel's theorem | Forster §21. The ⊇ direction (principal ⊆ ker) is underway via the Liouville route. The ⊆ direction (ker ⊆ principal, the Jacobi inversion step) is the hard half. |
| `AX_ofCurve_contMDiff` | `ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ⊤ (ofCurve x₀)` — Abel–Jacobi map is smooth | Smooth dependence of the line integral `∫_{x₀}^x ω` on the upper limit. Requires a manifold-level smooth-dependence-on-parameters theorem, absent from Mathlib. |

### Cluster C — Functoriality block

Six entries, of which the trace trio is now **discharged** (status note below) and
**three remain as axioms**. All appear in the `pushforward`/`pullback` declarations. The dependency structure
within the cluster is more nuanced than "all follow from one root":

| Axiom | Primary dependency | Role |
|---|---|---|
| `pushforwardOneForm` | core trace construction | The fiber-sum trace `Tr_f(ω)` of a 1-form ω along f: needed for `pullback` (defined as `(Tr_f)ᵀ`), `pullback_id`, `pullback_comp`, `pushforward_pullback` |
| `AX_pushforwardOneForm_id` | `pushforwardOneForm` real | `Tr_id = id`; immediate once the trace is real |
| `AX_pushforwardOneForm_comp` | `pushforwardOneForm` real | `Tr_{g∘f} = Tr_g ∘ Tr_f`; functoriality of the fiber sum |
| `AX_pushforwardAmbient_preserves_lattice` | `pullbackOneForm` (already real via Kirov) + period naturality | `pushforwardAmbientLinear` is defined as the dual of `pullbackOneForm f` — so `pullbackOneForm` (Kirov-backed) is the dependency, not the trace. Content: `∫_{f_*(γ)} ω = ∫_γ f*ω`. **Not trace-gated; can proceed now.** |
| `AX_pullbackAmbient_preserves_lattice` | `pushforwardOneForm` (trace, axiom) | `pullbackAmbientLinear` is defined as the dual of `pushforwardOneForm f` — so the trace IS the dependency. Content: `∫_γ f*ω = ∫_{f_*(γ)} ω` from the other side. **Trace-gated.** |
| `AX_pushforward_pullback` | trace-norm relation | `pushforward_f ∘ pullback_f = [deg f]` on Jac(Y): follows from `Tr_f(f*ω) = deg(f)·ω`. Forster §12 / Miranda. |

> **Status 2026-06-10:** the first three rows — `pushforwardOneForm`,
> `AX_pushforwardOneForm_id`, `AX_pushforwardOneForm_comp` — are **DISCHARGED**
> (#26/#27/#28): real def/theorems via the Kirov-Dolbeault port's fibre-sum trace
> `traceFormTotal`, transported across `Bridge/KirovDolbeaultTrace.lean`
> (standard-3). Together with the D1 merge the challenge-critical count is now **7**;
> `AX_pullbackAmbient_preserves_lattice` is no longer trace-gated by an axiom —
> it is the dual of a REAL trace.

With the trace real, the remaining Cluster-C axioms are the two
lattice-preservation statements — `AX_pushforwardAmbient_preserves_lattice`
(dual of the real `pullbackOneForm`) and `AX_pullbackAmbient_preserves_lattice`
(dual of the now-real trace) — plus `AX_pushforward_pullback`. All three are
period-naturality / projection-formula content over real maps; none is gated by
an opaque construction any more.

---

## The 23 non-challenge-critical axioms

### i. Intersection form + laws (3) — out of the challenge cone since D1

| Axiom | Why not critical |
|---|---|
| `intersectionForm` | **Exited every headline closure in D1 (2026-06-10)**: its only route was the old structure's proof-unconsumed `symplectic` field, now dropped. Kept per owner decision D2 as Part-3 topological-anchoring debt. |
| `AX_IntersectionForm_alternating` | Never consumed by any proof; fully orphaned post-D1 |
| `AX_IntersectionForm_perfect` | Period-lattice discreteness is proved from the bundle's R1/R2 fields directly, bypassing this law |

*All three become redundant theorems once `intersectionForm` is discharged to a
real construction that already satisfies them (the #16+#22 joint plan).*

### ii. Albanese universal property (4) — our addition beyond Buzzard

Underlie `ofCurve_isJacobian` (the Albanese `∃!` factorization), our strongest
anti-degeneracy result. Buzzard's v0.4 does not require it.

| Axiom | Content |
|---|---|
| `AX_torus_oneforms_dualCover` | Every complex torus is covered by the dual of its holomorphic 1-forms |
| `AX_torus_self_albanese` | A complex torus is its own Albanese variety |
| `AX_period_functoriality` | Period maps commute with holomorphic maps |
| `AX_curve_generates_jacobian` | The image of the curve generates the Jacobian as a group |

### iii. RR/Serre coherence depth (5) — mathematical depth, not Buzzard requirements

Needed to prove RR and Serre as theorems. The challenge's key properties (Jacobian
construction, ofCurve, functoriality) do not depend on RR/Serre.

| Axiom | Content | Status |
|---|---|---|
| `h1coh_zero_finrank` | h¹(𝒪_X) = genus X | Frontier; gates full Serre duality |
| `serreDuality_equiv` | H¹(D) ≃ L(K−D)* as ℂ-spaces | Frontier; needs `canonicalDivisor` real first |
| `LineBundle` | Type stub for line bundles | Needed to state traditional RR/Serre |
| `canonicalDivisor` | The canonical divisor K | **Prerequisite** for discharging `serreDuality_equiv` |
| `LineBundle.ofDivisor` | The line bundle O(D) | Needed to state traditional RR/Serre |

### iv. Plücker formula (1) — plane curve specific, Part 3 only

`AX_PluckerFormula`: `genus(C) = (d−1)(d−2)/2` for a smooth degree-d plane curve.
Follows from Riemann–Hurwitz or the adjunction formula; neither in Mathlib currently.

### v. Concrete curve witnesses (10) — Part 3 vetting only

| Group | Axioms |
|---|---|
| Elliptic | `AX_Elliptic_H1_symplectic` |
| Hyperelliptic | `AX_Hyperelliptic_genus` |
| Odd-atlas ∞-chart (7) | `infinityInverseMap`, `infinityChart`, `infinityChart_mem_source`, 4 compat axioms |
| Plane curve | `AX_PlaneCurveAffine_connected` (`PlaneCurve.instIsManifold` **discharged #52**, 2026-06-10) |

---

## Summary: the closure picture

```
7 challenge-critical axioms
    │
    ├── Cluster A (1) — in EVERY Buzzard declaration
    │      AX_PeriodCycleBasis  (D1 merge: loops + H₁ basis + Hurewicz tie
    │                            + arc-level R1 (Stokes) + R2 (Hodge ≻ 0))
    │      Needs: dissection/branched-cover topology for the basis;
    │      Stokes for R1; Hodge positivity for R2 ← hardest, no Lean proof
    │      Kirov port has the proven boundary-word engine for R1/R2
    │
    ├── Cluster B (3) — three independent classical theorems
    │      AX_genus_eq_zero_iff_homeo  ← Wallace has best Lean progress
    │      AX_AbelTheorem
    │      AX_ofCurve_contMDiff
    │
    └── Cluster C (3) — functoriality over now-real maps
           (trace trio discharged #26/#27/#28 via the Kirov-Dolbeault bridge)
           AX_pushforwardAmbient_preserves_lattice  (dual of real pullbackOneForm)
           AX_pullbackAmbient_preserves_lattice     (dual of the real trace)
           AX_pushforward_pullback                  (projection formula, deg f)
```

### Bottleneck assessment

**Cluster A's R2 field** is the single hardest barrier. Hodge positivity requires
L² theory / harmonic forms on a compact Riemann surface — no Lean proof exists anywhere.

**Cluster A's basis half** needs dissection topology (4g-gon, or the branched-cover
slit-sheet route post-keystone — `docs/planning/CYCLEBASIS_ALTERNATIVES.md`). The
older discharge analysis is in `docs/planning/AX_AnalyticCycleBasis.md`. DT-vetted.

**Cluster B**: Uniformization (`AX_genus_eq_zero_iff_homeo`) is the deepest single
theorem. `AX_ofCurve_contMDiff` needs manifold-level smooth-parameter integral theory.
`AX_AbelTheorem`'s hard half is Jacobi inversion.

**Cluster C**: the trace trio is discharged (#26/#27/#28), so nothing in the
cluster is gated by an opaque construction: both lattice-preservation axioms are
period-naturality statements about duals of REAL maps, and push-pull is the
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
trust without touching any of the 7.

The tower's indirect contribution to eventual challenge closure: the Kirov port
integrated in Phase D contains `residueTheorem_unconditional` and the proven
boundary-word R1/R2 engine (relevant to the R1/R2 fields of `AX_PeriodCycleBasis`)
and the branched-cover degree machinery (relevant to `pushforwardOneForm`).
