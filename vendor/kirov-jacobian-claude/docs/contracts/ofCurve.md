# Object contract — `ofCurve` (Abel–Jacobi map)

_Object contract + experiment record. Authored 2026-05-31. Includes the
result of attempting to discharge the anti-hack lemma `ofCurve_inj` on a
concrete curve (`Elliptic`) — see "Experiment" below._

```yaml
object: Jacobian.ofCurve   # impl: Jacobians.Axioms.ofCurveImpl
informal: >
  The Abel–Jacobi map of a compact Riemann surface X at a basepoint P₀:
  P ↦ (∫_{P₀}^P ω_i)_i ∈ Jacobian X, the period-lattice quotient of the
  dual of holomorphic 1-forms. Sends P₀ to 0 and, in positive genus, is
  injective (Abel's theorem, curve side) — the injectivity is Buzzard's
  deliberate block on the hack Jacobian := 0.
sources:
  - "Forster, Lectures on Riemann Surfaces, §21 (Abel's theorem)"
  - "Miranda, Algebraic Curves and Riemann Surfaces, Ch. VIII"
  - "Mumford, Tata Lectures on Theta I, §III.3"
lean:
  name: "Jacobian.ofCurve  (= Jacobians.Axioms.ofCurveImpl)"
  body: >
    fun P => ULift.up (QuotientAddGroup.mk'
       (ofCurveAmbient X P₀ P − ofCurveAmbient X P₀ P₀))
    where  ofCurveAmbient X P₀ P i = pathIntegralBasepointFunctional X P₀ P (jacobianBasis X i)
characterization:
  - id: C1
    claim: "ofCurve P₀ P₀ = 0  (basepoint to origin)"
  - id: C2   # anti-degeneracy — Buzzard's hack-blocker
    claim: "genus X > 0  ⇒  ofCurve P₀ injective"
  - id: C3
    claim: "ofCurve P₀ is holomorphic (ContMDiff)"
known_properties:
  - property: C1   # ofCurve_self
    theorem: Jacobians.Jacobian.ofCurve_self
    status: PROVEN_STRUCTURAL          # definitional from the subtraction
    axiom_deps: [pathIntegralBasepointFunctional, loopIntegralToH1]  # carried by the def, not the eq
  - property: C2   # ofCurve_inj — the anti-hack
    theorem: Jacobians.Jacobian.ofCurve_inj
    status: ASSERTED_OPAQUE_BLOCKED    # see Experiment
    axiom_deps: [AX_ofCurve_inj, pathIntegralBasepointFunctional, loopIntegralToH1]
  - property: C3   # ofCurve_contMDiff
    theorem: Jacobians.Jacobian.ofCurve_contMDiff
    status: proven_via_axiom
    axiom_deps: [AX_ofCurve_contMDiff, AX_PeriodLattice, instPeriodLatticeDiscrete,
                 pathIntegralBasepointFunctional, loopIntegralToH1]
well_definedness:
  note: >
    ofCurveAmbient lands in Fin(genus X)→ℂ; the lattice quotient makes the
    path-choice irrelevant. But the per-form values come from the OPAQUE
    axiom pathIntegralBasepointFunctional — the map has no concrete value
    on any curve, including Elliptic where the classical Abel–Jacobi map is
    explicitly known (it is the identity on ℂ/Λ).
anti_degeneracy:
  hack_blocked_by: C2 (ofCurve_inj)
  current_guard: >
    C2 is ASSERTED via AX_ofCurve_inj. The only thing that rules out the
    degenerate model "pathIntegralBasepointFunctional := 0" (which makes
    ofCurve constant, hence non-injective) is AX_pathIntegral_local_antiderivative
    (the chart-local FTC) — itself an axiom, not proven on any curve. So
    the anti-hack property is guarded by an axiom that is in turn guarded
    by another axiom; no link to Mathlib yet.
status: C1 structural; C2 asserted & opaque-blocked; C3 asserted.
        Not validatable on a concrete curve until the functional is real.
```

## Experiment — discharge `ofCurve_inj` on `Elliptic` without `AX_ofCurve_inj`

**Goal.** The validation-plan's highest-value target: prove the anti-hack
lemma on a concrete positive-genus curve from the real definition, retiring
`AX_ofCurve_inj` on at least one witness and proving `ofCurve` is not the
degenerate constant map.

**Result: blocked, structurally — and the blocker is the finding.**

`ofCurveImpl X P` unfolds to a quotient class of differences of
`Axioms.pathIntegralBasepointFunctional X P · (jacobianBasis X i)`, which is
an **opaque axiom with no defining equation**. `Elliptic` supplies a
concrete holomorphic 1-form (`ellipticDz`, proven nonzero, with
`eq_smul_ellipticDz` giving `genus = 1`) but **no concrete period integral,
Abel–Jacobi map, or functional value**. The bridge's real
`pathIntegralBasepointFunctional` (`KirovLineIntegral.lean:374`, built as
`lineIntegral ∘ bridgeForm ∘ bridgePath`) is a *separate* definition and is
**not wired into** `ofCurveImpl`; the swap is gated on the still-`sorry`
FTC theorem `kirovBackedFunctional_local_antiderivative`.

Evidence — unfolding the injectivity goal (captured 2026-05-31,
`set_option pp.proofs.withType false`):

```
hab : (QuotientAddGroup.mk' …) ((fun i => pathIntegralBasepointFunctional X P a (jacobianBasis X i)) − …)
    = (QuotientAddGroup.mk' …) ((fun i => pathIntegralBasepointFunctional X P b (jacobianBasis X i)) − …)
⊢ a = b
```

There is no lemma relating `pathIntegralBasepointFunctional X P a` to the
point `a`, so the goal `a = b` cannot be closed. The hypothesis is
consistent with the zero functional (where every class is `0` and `a ≠ b`
is allowed). Local non-degeneracy is recoverable *only* from
`AX_pathIntegral_local_antiderivative`, and global injectivity is the
genuine content of `AX_ofCurve_inj` (= Abel's theorem) — neither is
discharged.

**What this means for validation.** The anti-hack lemma `ofCurve_inj` is in
the most-asserted state in the repo: a property of a map whose definition is
opaque, guarded by an axiom guarded by an axiom. It **cannot be validated on
any concrete curve** by the "prove it on a witness" method until the
underlying functional is made real for that curve. This corrects the
validation-plan backlog: discharging `ofCurve_inj` is *not* a cheap next win
— it is downstream of making `pathIntegralBasepointFunctional` concrete.

**Corrected unblock path (in order):**

1. **Make `pathIntegralBasepointFunctional` concrete on `Elliptic`** — either
   wire in `kirovBackedFunctional` (needs the FTC theorem
   `kirovBackedFunctional_local_antiderivative`, currently `sorry`, in
   `KirovLineIntegral.lean`), or give a bespoke genus-1 period integral.
2. **Prove `ofCurveAmbient` is the universal-cover coordinate on `Elliptic`**
   — i.e. the functional against `ellipticDz` is (locally) the chart
   coordinate `z`, via `AX_pathIntegral_local_antiderivative`.
3. **Conclude injectivity on `ℂ/Λ`** — two points map to the same Jacobian
   point iff their coordinates differ by a period, iff (for the genus-1
   lattice = Λ) they are equal. This is the concrete Abel theorem and needs
   discreteness of `Λ` (have: `AX_PeriodLattice`) + the coordinate identity.

Only after step 1 does any concrete-witness validation of `ofCurve` become
possible. Until then the honest status of C2 is **asserted, opaque-blocked**.

## Reading this card

`ofCurve`'s defining equation C1 is real (structural). But its two
substantive properties — injectivity (the hack-blocker) and holomorphicity —
are asserted, and injectivity is *opaque-blocked*: not merely unproven, but
**unprovable from the current definition** because the definition bottoms out
in an axiom with no value. This is the sharpest example of why the
definition-asserting axioms (validation-plan bucket C) are the real risk:
`AX_ofCurve_inj` could be masking any map at all, including a constant one.
The fix is not "prove the axiom" — it is "make the definition concrete first,
then the property becomes provable."
