# Axioms needed to close Buzzard's challenge

*Authoritative source: `docs/axiom-report.txt` (kernel-verified `#print axioms` for every
challenge declaration). Reconciled 2026-06-10 against the 36-axiom table.*

---

## What "closing the challenge" means

Buzzard's `Challenge.lean` (v0.4) poses 24 `sorry`-obligations: a definition of `genus`,
`genus_eq_zero_iff_homeo`, the `Jacobian` type with 7 typeclass instances, `ofCurve` with
properties (`self`, `inj`, `contMDiff`), `pushforward`/`pullback` with smoothness and
functoriality, and `pushforward_pullback`. All 24 are filled; `ChallengeConformance.lean`
machine-checks every v0.4 signature.

**But filling a `sorry` with an `axiom` is not the same as proving it.** This document
identifies: which of the 36 remaining axioms must be discharged to produce a fully
axiom-free challenge closure?

---

## The 13 challenge-critical axioms

Exactly these axioms appear in `#print axioms` for one or more Buzzard declarations
(from `docs/axiom-report.txt`). Discharging all 13 gives a challenge closure resting
only on the three Lean-core axioms `[propext, Classical.choice, Quot.sound]`.

### Cluster A — Jacobian construction (appear in every Buzzard declaration)

These four underlie the construction `Jac X = (HolomorphicOneForm X)* / H₁` itself.
They appear even in the purely definitional declarations (`Jacobian`, `ofCurve`,
`ofCurve_self`), because the Jacobian type is built from the period lattice which uses
the symplectic cycle basis.

| Axiom | Precise Lean statement | Mathematical content | Discharge path |
|---|---|---|---|
| `AX_AnalyticCycleBasis` | `Nonempty (AnalyticCycleBasis X x₀)` — a symplectic H₁ basis of analytic loops, with the intersection-form values pinned: `⟨αᵢ,βⱼ⟩ = δᵢⱼ`, `⟨αᵢ,αⱼ⟩ = 0`, `⟨βᵢ,βⱼ⟩ = 0` | Existence of a symplectic piecewise-analytic basis of H₁(X,ℤ) (standard; follows from the CW structure of a compact oriented surface + the 4g-gon dissection) | Forster §§19–21; the Hurewicz iso + simplicial homology of the polygon model. The DT-vetting (2026-06-09) confirmed satisfiability via the 4g-gon construction. Coupled to `intersectionForm` — their discharge is one proof obligation. |
| `intersectionForm` | `H1 X x₀ →+ (H1 X x₀ →+ ℤ)` — the opaque H₁ × H₁ → ℤ pairing | The algebraic intersection number (counting oriented transverse intersections). Non-degeneracy from Poincaré duality; cup product on H¹ transported via the UCT iso | Same as `AX_AnalyticCycleBasis`: Poincaré duality for compact oriented surfaces. Neither CW homology nor Poincaré duality is in Mathlib at our pin. DT-vetting confirmed satisfiability. |
| `AX_RBR1` | `∀ η ζ : HolomorphicOneForm X, Q (periodVec b η) (periodVec b ζ) = 0` | The period vectors of any two holomorphic 1-forms are Q-isotropic. Equivalently `∫_X η ∧ ζ = 0` (the wedge of two (1,0)-forms is (2,0) and vanishes on a curve). Forces τ = τᵀ (symmetry of the period matrix). | Stokes' theorem on the cut surface. The Kirov port's `residueTheorem_unconditional` (∑ Res = 0, sorry-free) proves this for the relevant class of integrals and is the closest existing Lean reference. Forster §20, Griffiths–Harris Ch. 2 §2. |
| `AX_RBR2` | `∀ η ≠ 0, 0 < (ℂ.I * Q (periodVec b η) (conjPeriodVec b η)).re` | Hodge positivity: `i · Q(period η, conj-period η) > 0` for every nonzero holomorphic 1-form. Equivalently `i ∫_X η ∧ η̄ > 0` (the Hodge norm). Forces Im τ ≻ 0. | Hodge decomposition on compact Riemann surfaces; the Hodge star and L² inner product. No Lean proof exists anywhere; this is the hardest axiom in this cluster. Griffiths–Harris Ch. 0 §7; Mumford *Tata Lectures* Ch. II §2. |

**Note on coupling.** `AX_AnalyticCycleBasis` and `intersectionForm` are not fully
independent: the axiom for the cycle basis already pins the values of the intersection
form on the symplectic basis (`⟨αᵢ,βⱼ⟩ = δᵢⱼ` etc.). Their discharge will be a single
proof that constructs both from the CW topology of the cut surface. The separate law
axioms `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` are **not**
challenge-critical (see §Not critical below) because the current proofs use
`intersectionForm` only via the basis values pinned by `AX_AnalyticCycleBasis`, never
invoking the general laws.

### Cluster B — Three independent classical theorems

Each appears in exactly one Buzzard declaration and has its own proof path.

| Axiom | Lean statement | Mathematical content | Discharge path |
|---|---|---|---|
| `AX_genus_eq_zero_iff_homeo` | `RiemannSurface.genus X = 0 ↔ Nonempty (X ≃ₜ S²)` | Uniformization for genus 0: a compact Riemann surface has genus 0 iff it is homeomorphic to S². Both directions are nontrivial; the ⇒ direction uses a meromorphic function with a simple pole to build a biholomorphism to ℙ¹. | Forster §27; uniformization theorem. Wallace's GenusZero route (degree-1 cover → biholomorphism to ℙ¹, via RR + branched cover theory) has the most progress and is the best available path. Discharged for the concrete `genus ℙ¹ = 0` case already (axiom-free via Liouville). |
| `AX_AbelTheorem` | `(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X` | Abel's theorem: the degree-0 kernel of the Abel–Jacobi map on divisors equals the principal divisors. The ⊇ direction (principal ⊆ ker) is underway via the Liouville route. The ⊆ direction (ker ⊆ principal) is the hard half. | Forster §21, Miranda Ch. VIII. The ⊇ direction: use that a degree-0 principal divisor maps to 0 in (HolomorphicOneForm X)*; provable from smoothness of ofCurve. The ⊆ direction needs the full Abel theorem (the harder Jacobi inversion step). |
| `AX_ofCurve_contMDiff` | `ContMDiff 𝓘(ℂ) (𝓘(ℂ,ℂ^g/Λ)) ω (ofCurve x₀)` | Smoothness of the Abel–Jacobi map `x ↦ ∫_{x₀}^x ω` as a function of the upper limit. Requires smooth dependence of a parametric line integral on its endpoint. | Standard: the line integral `∫_γ ω` is smooth in the endpoint when ω is smooth. Needs a manifold-level smooth-dependence-on-parameters theorem. Not in Mathlib currently; requires proving that the chart of the complex torus composed with the integral defines a smooth chart map. |

### Cluster C — Functoriality block

All six appear in the `pushforward`/`pullback` declarations. They follow once
`pushforwardOneForm` is a real construction.

| Axiom | Role | Discharge path |
|---|---|---|
| `pushforwardOneForm` | The trace `Tr_f(ω)` of a holomorphic 1-form ω along f: a 1-form on Y defined by summing over the fibers of f with multiplicities | The trace construction is the core. The Kirov port already has `pushforwardOneForm` and the degree theorem; the existing Vendor/Kirov bridge provides the algebraic framework. Needs the local analytic construction of the trace across ramification points (Formula (3.1) of Miranda §VIII.3). |
| `AX_pushforwardOneForm_id` | `Tr_id = id` | Immediate from the trace definition once `pushforwardOneForm` is real. |
| `AX_pushforwardOneForm_comp` | `Tr_{g∘f} = Tr_g ∘ Tr_f` | Functoriality of the fiber sum under composition. |
| `AX_pushforwardAmbient_preserves_lattice` | `periodLattice` is natural for pushforward: `Tr_f` maps H₁(X)→periods to H₁(Y)→periods compatibly | Follows from the trace + the fact that integration commutes with the trace: `∫_{f_*(γ)} ω = ∫_γ f*ω`. The degree theorem `deg(div h) = 0` (proved axiom-free) is a prerequisite. |
| `AX_pullbackAmbient_preserves_lattice` | Dual naturality for pullback `f*` | Same naturality argument from the other side. Needs `pushforwardOneForm` real. |
| `AX_pushforward_pullback` | `pushforward_f ∘ pullback_f = [deg f]` on Jac(Y) | The push-pull formula: applying the trace after integrating against the pullback recovers the degree times the identity. Follows from the trace-norm relation `Tr_f(f*ω) = deg(f)·ω`. Forster §12.3 / Miranda. |

---

## The 23 non-challenge-critical axioms

These do **not** appear in `#print axioms` for any Buzzard declaration.

### i. Intersection form laws (2) — not yet consumed by any proof

| Axiom | Lean statement | Why not yet critical |
|---|---|---|
| `AX_IntersectionForm_alternating` | `intersectionForm x₀ a a = 0` for all a | The current proofs use `intersectionForm` as an opaque pairing whose values on the symplectic basis are pinned by `AX_AnalyticCycleBasis`. The alternating law would be needed to prove those basis values imply alternating — but no current proof goes that direction. |
| `AX_IntersectionForm_perfect` | The adjoint map `H₁ → H₁*` is bijective | Would be needed to prove the period lattice is non-degenerate from the intersection form alone. Currently `instPeriodLatticeDiscrete` is proved from `AX_RBR1`/`AX_RBR2` directly, bypassing this law. |

*These become critical when `intersectionForm` is discharged to a real construction —
at that point one would prove these laws from the construction, making them theorems.*

### ii. Albanese universal property (4) — our addition beyond Buzzard

These underlie `ofCurve_isJacobian` (the Albanese `∃!` factorization theorem), our
strongest anti-degeneracy result. Buzzard's v0.4 does not require it, but it pins the
Jacobian up to unique isomorphism.

| Axiom | Content |
|---|---|
| `AX_torus_oneforms_dualCover` | Every complex torus is covered by the dual of its holomorphic 1-forms |
| `AX_torus_self_albanese` | A complex torus is its own Albanese variety |
| `AX_period_functoriality` | Period maps commute with holomorphic maps (covariance of periods) |
| `AX_curve_generates_jacobian` | The image of the curve in its Jacobian generates the Jacobian as a group |

### iii. RR/Serre coherence depth (5) — mathematical depth, not Buzzard requirements

These are needed to prove RR and Serre as theorems via the Layer-3 tower. They are
not on the challenge's critical path because the challenge's key properties (Jacobian
construction, ofCurve, functoriality) do not depend on RR/Serre.

| Axiom | Content | Why it exists |
|---|---|---|
| `h1coh_zero_finrank` | `Module.finrank ℂ (H1coh 0) = genus X`, i.e. h¹(𝒪_X) = g | The Layer-3 tower needs this to prove `AX_RiemannRoch` |
| `serreDuality_equiv` | `Nonempty (H1coh D ≃ₗ[ℂ] Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D)))` | Needed for `AX_SerreDuality` |
| `LineBundle` | Type stub for line bundles on X | Used to state the traditional `H¹(D)` and `H⁰(K-D)` form of Serre duality |
| `canonicalDivisor` | The canonical divisor K (divisor of a holomorphic 1-form) | Appears in `serreDuality_equiv`; will need to be a real construction before `serreDuality_equiv` can be discharged |
| `LineBundle.ofDivisor` | The line bundle O(D) associated to a divisor D | Used in the traditional statement of RR/Serre |

*Note:* `canonicalDivisor` is a PREREQUISITE for discharging `serreDuality_equiv` —
when we eventually prove Serre duality, we need K to be a real construction, not an
axiom. So the non-critical status of these 5 will change as the frontier advances.

### iv. Plücker formula (1) — plane curve specific, Part 3 vetting only

| Axiom | Content |
|---|---|
| `AX_PluckerFormula` | `genus(C) = (d−1)(d−2)/2` for a smooth degree-d plane curve |

This follows from Riemann–Hurwitz applied to the projection ℙ² → ℙ¹, or from the
adjunction formula. Neither is in Mathlib currently. Not in any challenge declaration.

### v. Concrete curve witnesses (11) — Part 3 vetting only

All 11 are in the hyperelliptic/elliptic/plane-curve family — Part 3 of the project
(vetting on real curves). None appear in any Buzzard declaration:

| Group | Axioms |
|---|---|
| Elliptic witness | `AX_Elliptic_H1_symplectic` (the elliptic H₁ symplectic basis witness) |
| Hyperelliptic | `AX_Hyperelliptic_genus` (genus formula for hyperelliptic curves) |
| Odd-atlas ∞-chart (7) | `infinityInverseMap`, `infinityChart`, `infinityChart_mem_source`, `infinityChart_compat_affineLiftProjX`, `affineLiftProjX_compat_infinityChart`, `infinityChart_compat_affineLiftProjY`, `affineLiftProjY_compat_infinityChart` |
| Plane curve | `AX_PlaneCurveAffine_connected` (affine patch is connected); `PlaneCurve.instIsManifold` (atlas done, manifold instance still axiom) |

---

## Summary: the closure picture

```
13 challenge-critical axioms
    │
    ├── Cluster A (4) — one coupled proof obligation
    │      AX_AnalyticCycleBasis + intersectionForm  (symplectic H₁ topology)
    │      AX_RBR1  (Stokes / ∫ η∧ζ = 0)             ← Kirov port has reference proof
    │      AX_RBR2  (Hodge positivity / Im τ ≻ 0)     ← hardest; no Lean proof exists
    │
    ├── Cluster B (3) — three independent classical theorems
    │      AX_genus_eq_zero_iff_homeo  (uniformization) ← Wallace has best progress
    │      AX_AbelTheorem              (Abel's theorem)
    │      AX_ofCurve_contMDiff        (integral smoothness)
    │
    └── Cluster C (6) — all follow once pushforwardOneForm is real
           pushforwardOneForm + id + comp laws          ← trace across ramification
           AX_pushforwardAmbient_preserves_lattice      ← ∫ commutes with trace
           AX_pullbackAmbient_preserves_lattice
           AX_pushforward_pullback                     ← Tr_f(f*ω) = deg(f)·ω
```

### Bottleneck assessment

**Cluster A** is the hardest cluster. `AX_RBR2` (Hodge positivity) requires Hodge
theory for compact Riemann surfaces — no Lean proof exists anywhere, and this is
genuine analytic depth requiring L² theory or harmonic forms. `AX_RBR1` has a closer
existing reference: the Kirov port's `residueTheorem_unconditional` (∑ Res = 0,
sorry-free at our Mathlib version) captures the Stokes-theorem content that RBR1 rests
on.

`AX_AnalyticCycleBasis` + `intersectionForm` together need either (a) CW homology +
Poincaré duality for surfaces (not in Mathlib), or (b) a direct elementary construction
from the surface's polygon model. The DT-vetting confirmed satisfiability via the 4g-gon
construction; the discharge plan is in `docs/planning/AX_AnalyticCycleBasis.md`.

**Cluster B**: `AX_genus_eq_zero_iff_homeo` (uniformization) is the single deepest
axiom — it's the hardest classical theorem here and the furthest from Mathlib.
`AX_ofCurve_contMDiff` needs a manifold-level smooth-parameter theorem for line
integrals, which is also absent from Mathlib. `AX_AbelTheorem`'s ⊆ direction (the
Jacobi inversion step) is the hard half of Abel's theorem.

**Cluster C**: the trace construction for `pushforwardOneForm` is the key. The Kirov
port's degree machinery and branched-cover infrastructure (the `Discharge/Manifold/`
directory) are the closest existing reference.

---

## Relationship to the Layer-3 tower

The Layer-3 tower (Phases B–D) discharged RR and Serre as theorems. This was real
mathematical progress, but it is **orthogonal to challenge closure**:

- The 5 Layer-3 axioms that remain (`h1coh_zero_finrank`, `serreDuality_equiv`, line-bundle
  stubs) are **not** challenge-critical — they don't appear in any Buzzard `#print axioms`.
- The 13 challenge-critical axioms were never the tower's target. Cluster A
  (`AX_AnalyticCycleBasis` etc.) are prerequisites for the Jacobian construction; Clusters
  B and C are classical theorems on independent proof paths.
- The tower **deepens mathematical trust** (RR/Serre are now proved over real Čech
  cohomology) without closing any of the 13.

The tower's contribution to eventual challenge closure is indirect: the Kirov port that
Phase D integrated contains `residueTheorem_unconditional` (relevant to Cluster A /
RBR1), and the branched-cover degree machinery (relevant to Cluster C /
`pushforwardOneForm`).
