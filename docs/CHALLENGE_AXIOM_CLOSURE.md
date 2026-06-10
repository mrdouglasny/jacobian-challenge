# Axioms needed to close Buzzard's challenge

*Authoritative source: `docs/axiom-report.txt` (kernel-verified `#print axioms` for every
challenge declaration). Last reconciled 2026-06-10 against the 36-axiom table.*

---

## What "closing the challenge" means

Buzzard's `Challenge.lean` (v0.4) poses 24 `sorry`-obligations: a definition of `genus`,
a proof of `genus_eq_zero_iff_homeo`, the `Jacobian` type with 7 typeclass instances,
`ofCurve` and its properties (`self`, `inj`, `contMDiff`), `pushforward`/`pullback` and
their properties (smoothness, functoriality, `pushforward_pullback`).

All 24 are filled. The `ChallengeConformance.lean` machine-check verifies every v0.4
signature exactly (`lake env lean ChallengeConformance.lean`, exit 0). **But filling a
`sorry` with an `axiom` is not the same as proving it.** This document asks: which of
the 36 remaining axioms stand between us and a fully axiom-free challenge closure?

---

## The 13 challenge-critical axioms

These are the *only* project axioms that appear in `#print axioms` for any Buzzard
declaration (from `docs/axiom-report.txt`). Discharging all 13 gives a challenge closure
over only the three Lean-core axioms.

### Cluster A — Jacobian construction (appear in every Buzzard declaration)

| Axiom | Role | Discharge path |
|---|---|---|
| `AX_AnalyticCycleBasis` | Supplies the symplectic H₁ basis; the period lattice `H₁ → (HolomorphicOneForm X)*` is built from it | Forster §§19–21; H₁ ≅ ℤ^{2g} from the CW structure of a compact surface, symplecticity from intersection numbers. Likely needs `intersectionForm` discharged jointly. |
| `intersectionForm` | The opaque H₁ × H₁ → ℤ pairing; used alongside the cycle basis in lattice construction | Topological: the algebraic intersection number, cup-product on H₁. Discharge jointly with `AX_AnalyticCycleBasis` (the Hurewicz tie makes them one proof obligation). |
| `AX_RBR1` | Riemann bilinear relation 1 — isotropy: `⟨aᵢ,bᵢ⟩ - ⟨bᵢ,aᵢ⟩ = δᵢⱼ` | Stokes on the cut surface: the bilinear identity ∫_∂Σ ω ∧ η = 0. Now has a sorry-free reference proof (`residueTheorem_unconditional` in the Kirov port). |
| `AX_RBR2` | Riemann bilinear relation 2 — Hodge positivity: `Im τ ≻ 0` | Harmonic theory / Hodge decomposition on a compact Riemann surface. Research-grade; no Lean proof exists yet. |

*Note:* `AX_IntersectionForm_alternating` and `AX_IntersectionForm_perfect` — the laws
about `intersectionForm` — do **not** appear in the challenge's `#print axioms`. The
current proofs consume `intersectionForm` as an opaque value via the symplectic basis
values, never using the alternating or perfect-pairing laws directly.

### Cluster B — Explicit Buzzard anti-degeneracy requirements

| Axiom | Role | Discharge path |
|---|---|---|
| `AX_genus_eq_zero_iff_homeo` | `genus X = 0 ↔ X ≅ₜ S²` — Buzzard's adversarial genus-0 hook | Uniformization theorem (Forster §27). Wallace's repo has the most progress (`GenusZero` route via RR + degree-1 cover). |
| `AX_AbelTheorem` | Kernel of `abelJacobiDiv` = principal divisors (degree-0 restricted) | Abel's theorem, Forster §21. The ⊇ direction is partially underway (Liouville route). |
| `AX_ofCurve_contMDiff` | `ofCurve : X → Jacobian X` is smooth | Differentiability of the period integral as a function of the upper limit; Forster §12 / standard harmonic analysis. |

### Cluster C — Functoriality

| Axiom | Role | Discharge path |
|---|---|---|
| `pushforwardOneForm` | The trace / pushforward of a holomorphic 1-form along a holomorphic map | Forster / Griffiths–Harris trace construction. Needs well-defined local trace across ramification. |
| `AX_pushforwardOneForm_id` | `pushforwardOneForm id = id` | Follows from the trace construction once `pushforwardOneForm` is real. |
| `AX_pushforwardOneForm_comp` | `pushforwardOneForm (g ∘ f) = pushforwardOneForm g ∘ pushforwardOneForm f` | Same. |
| `AX_pushforwardAmbient_preserves_lattice` | Pushforward preserves the period lattice | Naturality of integration: `∫_{f_*(γ)} ω = ∫_γ f*ω`. |
| `AX_pullbackAmbient_preserves_lattice` | Pullback preserves the period lattice | Same naturality argument. |
| `AX_pushforward_pullback` | `pushforward f ∘ pullback f = deg(f) · id` on Jacobians | Riemann-Hurwitz-style counting; the degree theorem `deg(div f) = 0` (proved axiom-free) is a prerequisite. |

---

## The 23 non-challenge-critical axioms

These do **not** appear in `#print axioms` for any Buzzard declaration. They exist for
three distinct reasons:

### i. Intersection form laws (2) — needed eventually but not yet consumed

| Axiom | Why it's not yet critical |
|---|---|
| `AX_IntersectionForm_alternating` | Would be needed to prove the symplectic basis is truly symplectic, but current proofs use `intersectionForm` opaquely via its symplectic-basis values |
| `AX_IntersectionForm_perfect` | Would be needed to prove period-lattice non-degeneracy from the intersection form; currently `instPeriodLatticeDiscrete` is proved from `AX_RBR1`/`AX_RBR2` directly |

*These become critical once `AX_AnalyticCycleBasis` and `intersectionForm` are being
discharged — the two proof obligations are deeply entangled.*

### ii. Albanese universal property (4) — our addition beyond Buzzard

| Axiom | What it gives |
|---|---|
| `AX_torus_oneforms_dualCover` | Every complex torus is a quotient of its 1-forms |
| `AX_torus_self_albanese` | A torus is its own Albanese variety |
| `AX_period_functoriality` | Period maps are natural for holomorphic maps |
| `AX_curve_generates_jacobian` | The image of a curve generates its Jacobian |

These underlie `ofCurve_isJacobian` (the Albanese `∃!` factorization theorem), our
strongest anti-degeneracy result. Buzzard's v0.4 does not require it, but it pins the
Jacobian up to unique isomorphism.

### iii. RR/Serre coherence (5) — mathematical depth, not Buzzard requirements

| Axiom | What it gives | Why it exists |
|---|---|---|
| `h1coh_zero_finrank` | `h¹(𝒪_X) = g` | Needed to prove RR/Serre as theorems; not in any challenge declaration's dependency |
| `serreDuality_equiv` | `H¹(D) ≃ L(K−D)*` | Same |
| `LineBundle` | Type stub for line bundles | Used to state the RR/Serre theorems in the traditional form |
| `canonicalDivisor` | The canonical divisor K | Used in `serreDuality_equiv`'s statement |
| `LineBundle.ofDivisor` | `O(D)` construction | Same |

*`canonicalDivisor` is a prerequisite for discharging `serreDuality_equiv`.*

### iv. Plane-curve / Plücker (2) — Part 3 vetting only

| Axiom | What it gives |
|---|---|
| `AX_PluckerFormula` | `genus(C) = (d−1)(d−2)/2` for degree-d plane curves |
| `AX_PlaneCurveAffine_connected` | The affine patch of a smooth plane curve is connected |
| `PlaneCurve.instIsManifold` | PlaneCurve is a complex manifold (atlas complete, manifold axiom remains) |

### v. Concrete curve witnesses (11) — Part 3 vetting only

All 11 are in the hyperelliptic/elliptic witness cluster: `AX_Elliptic_H1_symplectic`,
`AX_Hyperelliptic_genus`, the 7 odd-atlas ∞-chart axioms, `AX_PlaneCurveAffine_connected`,
`PlaneCurve.instIsManifold`. None appear in any Buzzard declaration.

---

## Summary: what needs to happen to close

```
13 challenge-critical axioms
    │
    ├── Cluster A (4): AX_AnalyticCycleBasis + intersectionForm + AX_RBR1 + AX_RBR2
    │      └── one coupled proof obligation: symplectic H₁ basis + bilinear relations
    │          (RBR1 reference proof exists in Kirov port; RBR2 = Hodge positivity)
    │
    ├── Cluster B (3): AX_genus_eq_zero_iff_homeo + AX_AbelTheorem + AX_ofCurve_contMDiff
    │      └── three independent classical theorems (uniformization, Abel, integral smoothness)
    │
    └── Cluster C (6): the trace/lattice-preservation/degree-counting functoriality block
           └── all follow once pushforwardOneForm is a real construction
```

The tightest bottlenecks:
- **Cluster A** is the hardest: it requires either a Hodge-theory proof (RBR2 = Hodge
  positivity) or a harmonic-analysis proof. No Lean proof exists for RBR2. The Kirov port
  provides the residue theorem (relevant to RBR1 / Stokes side) but not RBR2.
- **`AX_ofCurve_contMDiff`** requires differentiability of `∫_{γ(t)} ω` as t varies — a
  manifold-level smooth dependence on parameters statement, not in Mathlib.
- **`pushforwardOneForm`** requires a real trace construction across ramification — connected
  to Kirov's branched-cover degree machinery.
- **`AX_genus_eq_zero_iff_homeo`** = uniformization, deepest single axiom. Wallace's route
  is the best available progress.

---

## Relationship to the Layer-3 tower

The Layer-3 tower (Phases B–D) discharged **RR and Serre as theorems** — a real
mathematical reduction. But none of the 13 challenge-critical axioms are discharged by
the tower:

- The tower uses `AX_AnalyticCycleBasis`, `intersectionForm`, `AX_RBR1`, `AX_RBR2` as
  inputs (they're in the tower's own dependency chain), not as outputs.
- The tower's remaining frontier (`h1coh_zero_finrank`, `serreDuality_equiv`) is NOT in
  the challenge's dependency chain at all — it's deeper mathematical coherence.

The tower's contribution to challenge closure is indirect: by reducing "we need RR/Serre
proved" to "we need the cohomology LES + h¹(O)=g + Serre iso", and then by discharging
most of that Layer-3 scaffold via the Kirov port (Phase D), the trust floor is lower.
But the 13 challenge-critical axioms require direct discharge on their own terms.
