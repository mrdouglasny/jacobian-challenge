# Axioms needed to close Buzzard's challenge

*Authoritative source: `docs/axiom-report.txt` (kernel-verified `#print axioms` for the
challenge property theorems and the concrete-curve headlines). The Jacobian typeclass
instances are now also covered: `scripts/axiom_report.lean` includes wrapper theorems
for all 7 Buzzard instance obligations (T2Space, CompactSpace, ConnectedSpace,
ChartedSpace, IsManifold, LieAddGroup, AddCommGroup). Reconciled 2026-06-10 against
the 36-axiom table.*

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
`axiom` is not the same as proving it.** This document identifies: which of the 36
remaining axioms must be discharged to produce a fully axiom-free challenge closure?

---

## The 13 challenge-critical axioms

Exactly these axioms appear in `#print axioms` for one or more Buzzard declarations
(from `docs/axiom-report.txt`, which now covers both property theorems and instance
obligations). Discharging all 13 gives a challenge closure over only
`[propext, Classical.choice, Quot.sound]`.

### Sub-cluster A1 — Core Jacobian structure (appear in ALL Buzzard declarations)

These two appear even in the definitional declarations (`Jacobian`, `ofCurve`) and in
the lightweight instances (`AddCommGroup`, `TopologicalSpace`, `ConnectedSpace`). They underlie the
construction `Jac X = (HolomorphicOneForm X)* / H₁`.

| Axiom | Precise Lean statement | Mathematical content | Discharge path |
|---|---|---|---|
| `AX_AnalyticCycleBasis` | `Nonempty (AnalyticCycleBasis X x₀)` — a symplectic H₁ basis of analytic loops, with the intersection-form values on the basis already pinned: `⟨αᵢ,βⱼ⟩ = δᵢⱼ`, `⟨αᵢ,αⱼ⟩ = 0`, `⟨βᵢ,βⱼ⟩ = 0` | Existence of a piecewise-analytic symplectic basis of H₁(X,ℤ). Standard; follows from the CW structure of a compact oriented surface (4g-gon dissection + the Hurewicz iso). | Forster §§19–21; the 4g-gon construction gives the H₁ basis; symplecticity from the intersection form. DT-vetting (2026-06-09) confirmed satisfiability. Coupled to `intersectionForm` — discharge is one joint obligation. |
| `intersectionForm` | `H1 X x₀ →+ (H1 X x₀ →+ ℤ)` — the opaque H₁ × H₁ → ℤ pairing | The algebraic intersection number (oriented transverse intersection count). From Poincaré duality: `H₁ ≅ H¹` via UCT, cup product gives the form. Non-degeneracy from PD. | Same as `AX_AnalyticCycleBasis`: needs CW homology + Poincaré duality for compact oriented surfaces, neither in Mathlib at our pin. DT-vetting confirmed satisfiability. |

**Note on coupling.** `AX_AnalyticCycleBasis` already pins the values of
`intersectionForm` on the symplectic basis. Their discharge is one proof obligation that
constructs both from the CW topology of the surface. The separate law axioms
`AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` are **not**
challenge-critical (see §Not critical) because the proofs use `intersectionForm` only
via the basis values already pinned by `AX_AnalyticCycleBasis`, never via the general laws.

### Sub-cluster A2 — Period/Hodge primitives (add to smoothness + 5 Jacobian instances)

These appear in `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`,
and in the Jacobian instances for `T2Space`, `CompactSpace`, `ChartedSpace`,
`IsManifold`, `LieAddGroup` — all via `instPeriodLatticeDiscrete` (the proof that the
period lattice is a ℤ-lattice depends on RBR1+RBR2).

| Axiom | Precise Lean statement | Mathematical content | Discharge path |
|---|---|---|---|
| `AX_RBR1` | `∀ η ζ : HolomorphicOneForm X, Q (periodVec b η) (periodVec b ζ) = 0` | The period vectors of any two holomorphic 1-forms are Q-isotropic. Equivalently `∫_X η ∧ ζ = 0` (the wedge of two (1,0)-forms is a (2,0)-form, zero on a complex curve). Forces τ = τᵀ. | Stokes' theorem on the cut surface. The Kirov port's `residueTheorem_unconditional` (∑ Res = 0, sorry-free at our Mathlib) is the closest existing Lean reference for this class of integral identity. Forster §20; Griffiths–Harris Ch. 2 §2. |
| `AX_RBR2` | `∀ η ≠ 0, 0 < (ℂ.I * Q (periodVec b η) (conjPeriodVec b η)).re` | Hodge positivity: `i · Q(period η, conj-period η) > 0` for every nonzero holomorphic 1-form. Equivalently `i ∫_X η ∧ η̄ > 0` (the Hodge norm). Forces Im τ ≻ 0. | Hodge decomposition on compact Riemann surfaces. No Lean proof exists anywhere; the hardest axiom in Cluster A. Griffiths–Harris Ch. 0 §7; Mumford *Tata Lectures* Ch. II §2. |

### Cluster B — Three independent classical theorems

Each appears in exactly one Buzzard declaration and has its own proof path.

| Axiom | Mathematical content | Discharge path |
|---|---|---|
| `AX_genus_eq_zero_iff_homeo` | `genus X = 0 ↔ X ≅ₜ S²` — uniformization for genus 0 | Forster §27. Wallace's GenusZero route (degree-1 cover → biholomorphism to ℙ¹) has the most Lean progress. The concrete `genus ℙ¹ = 0` is already proved axiom-free via Liouville. |
| `AX_AbelTheorem` | Degree-0 kernel of `abelJacobiDiv` = `PrincipalDivisors` — Abel's theorem | Forster §21. The ⊇ direction (principal ⊆ ker) is underway via the Liouville route. The ⊆ direction (ker ⊆ principal, the Jacobi inversion step) is the hard half. |
| `AX_ofCurve_contMDiff` | `ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ⊤ (ofCurve x₀)` — Abel–Jacobi map is smooth | Smooth dependence of the line integral `∫_{x₀}^x ω` on the upper limit. Requires a manifold-level smooth-dependence-on-parameters theorem, absent from Mathlib. |

### Cluster C — Functoriality block

All six appear in the `pushforward`/`pullback` declarations. The dependency structure
within the cluster is more nuanced than "all follow from one root":

| Axiom | Primary dependency | Role |
|---|---|---|
| `pushforwardOneForm` | core trace construction | The fiber-sum trace `Tr_f(ω)` of a 1-form ω along f: needed for `pullback` (defined as `(Tr_f)ᵀ`), `pullback_id`, `pullback_comp`, `pushforward_pullback` |
| `AX_pushforwardOneForm_id` | `pushforwardOneForm` real | `Tr_id = id`; immediate once the trace is real |
| `AX_pushforwardOneForm_comp` | `pushforwardOneForm` real | `Tr_{g∘f} = Tr_g ∘ Tr_f`; functoriality of the fiber sum |
| `AX_pushforwardAmbient_preserves_lattice` | `pullbackOneForm` (already real via Kirov) + period naturality | `pushforwardAmbientLinear` is defined as the dual of `pullbackOneForm f` — so `pullbackOneForm` (Kirov-backed) is the dependency, not the trace. Content: `∫_{f_*(γ)} ω = ∫_γ f*ω`. **Not trace-gated; can proceed now.** |
| `AX_pullbackAmbient_preserves_lattice` | `pushforwardOneForm` (trace, axiom) | `pullbackAmbientLinear` is defined as the dual of `pushforwardOneForm f` — so the trace IS the dependency. Content: `∫_γ f*ω = ∫_{f_*(γ)} ω` from the other side. **Trace-gated.** |
| `AX_pushforward_pullback` | trace-norm relation | `pushforward_f ∘ pullback_f = [deg f]` on Jac(Y): follows from `Tr_f(f*ω) = deg(f)·ω`. Forster §12 / Miranda. |

The key discharge order: `pushforwardOneForm` (trace across ramification) gates
`pullback` type, both id/comp laws, `AX_pullbackAmbient_preserves_lattice`, and
push-pull. `AX_pushforwardAmbient_preserves_lattice` is independent of the trace:
it is built from `pullbackOneForm` (real, Kirov-backed) and can proceed independently.
These are the two parallel workstreams in Cluster C.

---

## The 23 non-challenge-critical axioms

### i. Intersection form laws (2) — not yet consumed

| Axiom | Why not yet critical |
|---|---|
| `AX_IntersectionForm_alternating` | Current proofs consume `intersectionForm` only via the basis values pinned by `AX_AnalyticCycleBasis`; this general law is not invoked |
| `AX_IntersectionForm_perfect` | Period-lattice discreteness is proved from `AX_RBR1`/`AX_RBR2` directly, bypassing this law |

*Both become redundant theorems once `intersectionForm` is discharged to a real
construction that already satisfies them.*

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

### v. Concrete curve witnesses (11) — Part 3 vetting only

| Group | Axioms |
|---|---|
| Elliptic | `AX_Elliptic_H1_symplectic` |
| Hyperelliptic | `AX_Hyperelliptic_genus` |
| Odd-atlas ∞-chart (7) | `infinityInverseMap`, `infinityChart`, `infinityChart_mem_source`, 4 compat axioms |
| Plane curve | `AX_PlaneCurveAffine_connected`, `PlaneCurve.instIsManifold` |

---

## Summary: the closure picture

```
13 challenge-critical axioms
    │
    ├── Sub-cluster A1 (2) — in EVERY Buzzard declaration
    │      AX_AnalyticCycleBasis + intersectionForm  [coupled: one proof obligation]
    │      Needs: CW homology + Poincaré duality for surfaces
    │
    ├── Sub-cluster A2 (2) — add to smoothness + 5 of the 7 Jacobian instances
    │      AX_RBR1  (Q-isotropy of period vectors / Stokes)
    │      AX_RBR2  (Hodge positivity / Im τ ≻ 0)    ← hardest; no Lean proof exists
    │      Kirov port has reference proof for RBR1 class of integrals
    │
    ├── Cluster B (3) — three independent classical theorems
    │      AX_genus_eq_zero_iff_homeo  ← Wallace has best Lean progress
    │      AX_AbelTheorem
    │      AX_ofCurve_contMDiff
    │
    └── Cluster C (6) — two parallel workstreams
           Trace workstream: pushforwardOneForm → pullback type + id + comp
                             + AX_pullbackAmbient_preserves_lattice + push-pull
           Kirov-backed workstream: AX_pushforwardAmbient_preserves_lattice
                (built from pullbackOneForm, already real; can start now)
```

### Bottleneck assessment

**Sub-cluster A2 (RBR2)** is the single hardest barrier. Hodge positivity requires
L² theory / harmonic forms on a compact Riemann surface — no Lean proof exists anywhere.

**Sub-cluster A1** needs CW homology + Poincaré duality for surfaces, absent from
Mathlib. The discharge plan is in `docs/planning/AX_AnalyticCycleBasis.md`. DT-vetted.

**Cluster B**: Uniformization (`AX_genus_eq_zero_iff_homeo`) is the deepest single
theorem. `AX_ofCurve_contMDiff` needs manifold-level smooth-parameter integral theory.
`AX_AbelTheorem`'s hard half is Jacobi inversion.

**Cluster C**: `AX_pushforwardAmbient_preserves_lattice` can start now — it uses
`pullbackOneForm` (real, Kirov-backed), not the trace. `pushforwardOneForm` (trace
across ramification) gates `AX_pullbackAmbient_preserves_lattice`, `pullback`, both
id/comp laws, and push-pull.
Miranda (3.1) / Kirov port's `Discharge/Manifold/` machinery are the closest reference.

---

## Relationship to the Layer-3 tower

The Layer-3 tower (Phases B–D) contains two distinct parts with different relationships
to challenge closure:

**Phase C period primitives (`AX_RBR1`, `AX_RBR2`)** — these ARE challenge-critical
(Sub-cluster A2 above). They were introduced by the tower as primitives for proving the
period-cluster theorems, but they ended up in the challenge's dependency chain via
`instPeriodLatticeDiscrete` (which is now a theorem over them).

**The RR/Serre cohomology branch** (`h1coh_zero_finrank`, `serreDuality_equiv`,
line-bundle stubs) — this IS orthogonal to challenge closure. These axioms do not appear
in any Buzzard `#print axioms`. The tower's RR/Serre discharge deepens mathematical
trust without touching any of the 13.

The tower's indirect contribution to eventual challenge closure: the Kirov port
integrated in Phase D contains `residueTheorem_unconditional` (relevant to `AX_RBR1`)
and the branched-cover degree machinery (relevant to `pushforwardOneForm`).
