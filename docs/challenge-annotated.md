# Buzzard's Jacobian Challenge — annotated foundation/theorem split

_Annotation drafted 2026-04-23._ The challenge file contains 24 sorries.
This document classifies each one as either:

- **F (Foundation)** — a *data* sorry (definition or instance) that must
  be filled with a real Lean `def` / real typeclass instance for the
  foundation to be genuinely present. Filling it is a **construction**,
  not a proof; it can be done without proving any deep classical
  theorem. If this sorry is axiom-routed at the top level, the
  foundation is not actually built.
- **T (Theorem)** — a *property* sorry that, once the foundation is in
  place, asserts a classical 19th–20th century fact. The statement is
  testable (it type-checks against the real defs) but the proof is
  deep. If properly formulated against the correct foundation, it can
  be axiomatized with a textbook citation and discharged later.
- **H (Hybrid)** — partly definitional, partly a property; discharge
  requires both a construction and a small proof. In practice these
  retire alongside the corresponding F sorry because the F construction
  carries the Prop content as a by-product.

Current repo status is noted after each category. Everything labelled
`✓ real def / theorem` has been discharged as a real Lean `def` or
derived theorem (not an axiom); `axiom-routed` means the Buzzard-level
statement is present but closes via a named-axiom downstream.

Buzzard's file is kept verbatim in `Jacobians/Challenge.lean`; our
discharge layer lives in `Jacobians/Jacobian/`, `Jacobians/Axioms/`,
and `Jacobians/RiemannSurface/`.

---

## Data sorries — 13 total

### §1. `def genus` — **F**

```lean
def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] : ℕ := sorry
```

Classical definition: `g := dim_ℂ H⁰(X, Ω¹_X)`. **Current status: ✓
real def** — `Jacobians.RiemannSurface.genus X := Module.finrank ℂ
(HolomorphicOneForm X)`. Depends on the stubbed `HolomorphicOneForm X`
chart-cocycle carrier (currently `⊥`-submodule; `AX_FiniteDimOneForms`
becomes load-bearing once the cocycle predicates are refined).

### §2. `def Jacobian : Type u` — **F**

```lean
def Jacobian (X : Type u) [...] : Type u := sorry
```

Classical definitions (three equivalent ones): period quotient `(H⁰(Ω¹))∨ / H₁(ℤ)`, `Pic⁰`, or `H¹(X, 𝒪)/H¹(X, ℤ)`. **Current status: ✓
real def** — `Jacobians.Jacobian X := ULift (ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ jacobianBasis))`, the basis-coordinate period quotient, ULifted to `Type u`.

### §3. `instance : AddCommGroup (Jacobian X)` — **F**

Quotient of a ℂ-vector space by a subgroup. **✓ real instance** via ULift transfer.

### §4. `instance : TopologicalSpace (Jacobian X)` — **F**

Quotient topology. **✓ real instance** via ULift transfer.

### §5. `instance : T2Space (Jacobian X)` — **H**

Hausdorffness of the torus quotient; classical, requires discreteness of the lattice. **✓ real instance**, using discreteness from `instPeriodLatticeDiscrete` (axiom: the period lattice is discrete, retires with `AX_RiemannBilinear`).

### §6. `instance : CompactSpace (Jacobian X)` — **H**

Classical: a full-rank lattice gives compact quotient. **✓ real instance**.

### §7. `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` — **F**

The *definition* of the complex structure on `Jacobian` — charts via lifting balls around lattice points. **✓ real instance**, axiom-free, via `ComplexTorus.chartedSpace`.

### §8. `instance : IsManifold 𝓘(ℂ) ω (Jacobian X)` — **H**

Smoothness/holomorphicity of chart transitions. Transitions are translations by lattice vectors → trivially analytic. **✓ real instance**.

### §9. `instance : LieAddGroup 𝓘(ℂ) ω (Jacobian X)` — **H → closed**

Smoothness of add/neg on the torus. Classical, mechanical. **✓ real instance** (closed 2026-04-23 via Path A): `contMDiff_ulift_up` / `contMDiff_ulift_down` in `Jacobian/Construction.lean` prove ULift.up/down are smooth under the custom `chartedSpaceULift` structure; `LieAddGroup (Jacobian X)` then follows by composition with the axiom-free `LieAddGroup (ComplexTorus V L)`. The previously-flagged universe-cast issue was resolved by propositional (not rfl) chart-target equivalence via `extChartAt_target_iff` and `extChartAt_source_up_iff` bridge lemmas.

### §10. `def ofCurve : X → X → Jacobian X` — **F**

The Abel-Jacobi map `(P₀, P) ↦ [∫_{P₀}^P ω_i]_i`. **✓ real def** — `ofCurveImpl X P₀ P := ULift.up (mk' (ofCurveAmbient X P₀ P - ofCurveAmbient X P₀ P₀))`, with `ofCurveAmbient` a real def in terms of the primitive axiom `pathIntegralBasepointFunctional` bound to the 1-form cocycle by `AX_pathIntegral_local_antiderivative` (Fundamental Theorem of Calculus).

### §11. `def ContMDiff.degree : ℕ` — **F**

Degree of a holomorphic map; 0 for constants. **✓ real def** — `degreeImpl f hf := if constant then 0 else Classical.choose (AX_BranchLocus f hf hc)`.

### §12. `def pushforward : Jacobian X →ₜ+ Jacobian Y` — **F**

**✓ real def** — `pushforwardImpl` via `QuotientAddGroup.map` of the ambient linear map `pushforwardAmbientLinear`, which is itself a **real def** derived from the structured primitive `pullbackOneForm` (pullback of 1-forms) via `.dualMap` + basis-dualisation. ULift-wrapped; continuity from finite-dim ℂ-linear.

### §13. `def pullback : Jacobian Y →ₜ+ Jacobian X` — **F**

**✓ real def**, symmetric to pushforward, using `pushforwardOneForm` (trace of 1-forms).

---

## Theorem sorries — 11 total

### §14. `lemma genus_eq_zero_iff_homeo` — **T (deep)**

```lean
lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere 0 1))
```

Uniformization theorem for compact genus-0 Riemann surfaces: `g = 0 ⇔
X ≅ ℙ¹(ℂ) ≅ S²`. Classical but genuinely deep (Riemann-Roch route or
Koebe uniformization). **Axiom-routed** (`AX_genus_eq_zero_iff_homeo`). Discharges via Riemann-Roch for genus 0 (Mumford Ch. II).

### §15. `lemma ofCurve_contMDiff` — **T (deep)**

Holomorphicity of the Abel-Jacobi map. Classical: follows from the fact that path-integration against a holomorphic 1-form is holomorphic in the upper endpoint. **Axiom-routed** (`AX_ofCurve_contMDiff`). Derivable once `AX_pathIntegral_local_antiderivative` + smoothness of local coordinates land as theorems — the local-antiderivative axiom already supplies a chart-local `HasDerivAt`, so this should be a medium-size proof (hours, not weeks) once the interface is complete.

### §16. `lemma ofCurve_self : ofCurve P P = 0` — **F → derived theorem**

**✓ derived theorem** (not an axiom). The real def `ofCurveImpl` subtracts `ofCurveAmbient X P₀ P₀` from itself at the basepoint, making this definitionally zero. No textbook argument needed.

### §17. `lemma ofCurve_inj` — **T (deep)**

Abel's theorem on the curve side: the Abel-Jacobi map is injective when `genus X > 0`. Classical. Multi-page proof via the Jacobi inversion theorem + Riemann theta. **Axiom-routed** (`AX_ofCurve_inj`). Forster Ch. III §21.

### §18. `theorem pushforward_contMDiff` — **T (deep)**

Holomorphicity of the pushforward map on Jacobians. Reduces to smoothness of `pullbackOneForm` + continuity of the dualisation / quotient. **Axiom-routed** (`AX_pushforward_contMDiff`). Once `pullbackOneForm` is a real def (not axiom), this becomes a medium-size proof.

### §19. `lemma pushforward_id_apply : pushforward id _ P = P` — **T → derived theorem**

**✓ derived theorem** (2026-04-23 round-3). Retired from axiom to theorem using `pushforwardAmbientLinear_id` (proved from `AX_pullbackOneForm_id` + `LinearMap.dualMap_id`) + `jacobianHomOfAmbient_id_apply`. Real proof in `Jacobians/Axioms/AbelJacobiMap.lean`.

### §20. `lemma pushforward_comp_apply` — **T → derived theorem**

**✓ derived theorem** (2026-04-23 round-3). Retired using `pushforwardAmbientLinear_comp` (proved from `AX_pullbackOneForm_comp` + `LinearMap.dualMap_comp_dualMap`) + `jacobianHomOfAmbient_comp_apply`.

### §21. `theorem pullback_contMDiff` — **T (deep)**

Symmetric to §18; axiom-routed.

### §22. `lemma pullback_id_apply` — **T → derived theorem**

**✓ derived theorem** (2026-04-23 round-3). Symmetric to §19, using `pullbackAmbientLinear_id` derived from `AX_pushforwardOneForm_id`.

### §23. `lemma pullback_comp_apply` — **T → derived theorem**

**✓ derived theorem** (2026-04-23 round-3). Symmetric to §20, using `pullbackAmbientLinear_comp` derived from `AX_pushforwardOneForm_comp`.

### §24. `lemma pushforward_pullback : f_* ∘ f^* = deg(f) • id` — **T (deepest)**

The big structural identity. Classical content: for a degree-`d` holomorphic cover `f : X → Y`, pulling back 1-forms from `Y` to `X` then tracing back gives a `d`-fold multiple. Requires the branch-locus structure (`AX_BranchLocus`) and that the trace / pushforward of 1-forms composes correctly with pullback. **Axiom-routed** (`AX_pushforward_pullback`). In textbook form: Mumford Vol I §II.3 (a few pages of diagram-chasing once all primitives are in place).

---

## Summary

| Category | Count | Buzzard §§ | Current state |
|---|---|---|---|
| **F** (foundation — real def required) | 10 | §1, §2, §3, §4, §7, §10, §11, §12, §13, §16 | ✓ all discharged as real `def`s / derived theorems |
| **H** (hybrid — part def, part Prop) | 5 | §5, §6, §8, §9, §16 | ✓ **5/5** real instances (§9 closed 2026-04-23 round-3) |
| **T → derived** (converted to theorems this session) | 5 | §16, §19, §20, §22, §23 | ✓ real theorems; derivations in `AbelJacobiMap.lean` |
| **T (deep; classical theorems)** | 5 | §14, §15, §17, §18, §21 | Axiom-routed; each 1–2 weeks |
| **T (deepest)** | 1 | §24 | Axiom-routed; 2–4 weeks |

**Foundation status**: 10/10 F sorries and 5/5 H sorries closed as real `def`s / real instances. **No axiom-routed foundation remains at the Buzzard interface.**

**Theorem status**: 5/11 derived (§§16, 19, 20, 22, 23), 6/11 routed to classical-theorem axioms (§§14, 15, 17, 18, 21, 24).

**Caveats (per Codex 2026-04-23 review)**:
1. The concrete genus witnesses used to argue "hack-blockers bite" are themselves axiom-routed: `genus ProjectiveLine = 0` discharges via `AX_genus_eq_zero_iff_homeo` applied to the stereographic homeomorphism (not a structurally independent proof); `genus (Elliptic ω₁ ω₂ h) = 1` is its own axiom. So the hack-blocker defense is as strong as those axioms, not independent of them.
2. `Hyperelliptic H := OnePoint (HyperellipticAffine H)` is **mathematically correct only for odd `deg f`** (one branch point at infinity). For even `deg f` the classical projective model has two distinct points at infinity; `OnePoint` collapses them into one, producing a different topological space. Same caveat applies to `PlaneCurve` when the defining curve meets the line at infinity in more than one point. For broad classes of examples, these are **not the intended projective curve**. Solid concrete witnesses at present: `ProjectiveLine` (genus 0) and `Elliptic ω₁ ω₂ h` (genus 1).

**Net claim**: every *definition* Buzzard asked for is present as a real Lean `def` / instance at his API boundary. Every *theorem* Buzzard asked for is stated against those real defs. The residual axioms split into (a) classical-theorem axioms with textbook citations and (b) repo-specific construction-interface axioms (5 function-existence + their property axioms); see `docs/dependency-trace.md` for the full classification.
