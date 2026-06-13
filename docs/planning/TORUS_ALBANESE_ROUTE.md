# TORUS-ALBANESE discharge route

Scoping + discharge log for the 4 complex-torus axioms in
`Jacobians/Axioms/TorusAlbanese.lean` that gate `ofCurve_isJacobian`
(the Albanese universal property / categoricity of the Jacobian).

These are **off the Buzzard critical path** — no challenge declaration uses
them. They are the only inputs (beyond `standard-3` + `AX_PeriodCycleBasis`)
between our proven `ofCurve_isJacobian` and a fully axiom-free Albanese
categoricity result. All four are standard abelian-variety facts
(Birkenhake–Lange Ch.1; Griffiths–Harris Ch.0&2) — torus linear algebra,
not surface theory.

## Status snapshot (2026-06-12, TORUS lane)

| # | Axiom | Status | Difficulty |
|---|-------|--------|------------|
| 1 | `AX_torus_oneforms_dualCover` | **DISCHARGED** (→ `noncomputable def`, `LinearEquiv.refl`) | trivial-given-model |
| 2 | `AX_torus_self_albanese` | scoped, research-grade | hard (construction from abstract torus) |
| 3 | `AX_period_functoriality` | scoped, derivable-from-#2 | medium, coupled to #2 |
| 4 | `AX_curve_generates_jacobian` | scoped, research-grade | hard (Jacobi inversion) |

After this session `#print axioms Jacobians.ofCurve_isJacobian` lists:
`propext, Classical.choice, Quot.sound, AX_PeriodCycleBasis,
AX_curve_generates_jacobian, AX_period_functoriality, AX_torus_self_albanese`
— i.e. **3 torus axioms remain** (down from 4), no `sorryAx`.

---

## Axiom 1 — `AX_torus_oneforms_dualCover` — DISCHARGED

Statement (verbatim, now a `noncomputable def`):
```
TorusHolomorphicOneForm m A ≃ₗ[ℂ] Module.Dual ℂ (Fin m → ℂ)
```
**Key observation.** `TorusHolomorphicOneForm m A` is *defined* in this file as
`Module.Dual ℂ (Fin m → ℂ)` (an `abbrev`). The Birkenhake–Lange analytic
content — a translation-invariant holomorphic 1-form on `A = ℂ^m/Λ` lifts to the
cover, where translation-invariance + Liouville force a constant coefficient, so
it is exactly a constant cover-linear functional — is captured *in that
modelling choice*. Relative to it the equivalence is the identity:
`LinearEquiv.refl ℂ _`.

**Soundness note (per CLAUDE.md "vet STRENGTHENING").** This is the *safe*
direction: the axiom was never stronger than its definitional unfolding, so
collapsing it to `refl` introduces no false content. The real analytic claim
lives one level down, in the decision that the target-torus form space *is* the
constant-functional model — a decision already baked into every downstream use
(`torusInvariantOneFormSection`, `torusAmbientLinear`, …). Discharging here does
not remove that modelling debt; it removes a redundant axiom restating it.

Discharged: in-place `axiom → noncomputable def`, statement verbatim, body
`LinearEquiv.refl ℂ _`. Kernel-verified: `ofCurve_isJacobian` no longer lists
it; no `sorryAx`.

---

## Axiom 2 — `AX_torus_self_albanese` — research-grade

Produces a `TorusSelfAlbanesePresentation m A` for an **abstract** torus `A`
given only `[ChartedSpace (Fin m→ℂ) A] [AddGroup A] [LieAddGroup] [Compact]
[Connected]`. It must **construct from scratch**:
- the period lattice `Λ ⊆ ℂ^m`,
- the universal cover map `fromQuot : ℂ^m/Λ →+ A` (holomorphic group iso),
- the coordinate lift `liftCoord : A → ℂ^m`,
- the **self-Albanese identity** `liftCoord a = ∫₀ᵃ (invariant forms) mod periods`.

**Key obstruction.** This is the uniformization of an abstract compact connected
complex Lie group: `exp : Lie(A) ≅ ℂ^m → A` is a surjective group hom with
kernel a full lattice (`A ≅ ℂ^m/Λ`). In Mathlib terms this needs the complex
`exp`/developing map of `A` as a Lie group, its surjectivity (compact+connected),
and identification of `ker exp` as a `ZLattice` — none of which is currently
available in the repo for an abstract `LieAddGroup` modelled on `Fin m → ℂ`. The
repo's covering machinery (`QuotientCoveringPi1`, `ComplexTorus.instChartedSpace`,
`mdifferentiable_lift_of_mdifferentiable`) is built for *concrete* quotients
`ℂ^g/Λ`, i.e. the **codomain** of uniformization, not the abstract `A` we must
uniformize. Proof path exists (developing map of a flat compact complex Lie
group) but is a multi-week formalization, not a session-scale discharge.

---

## Axiom 3 — `AX_period_functoriality` — derivable from #2, medium

```
(periodLatticeInBasis X x₀ (jacobianBasis X)).toAddSubgroup ≤
  P.lattice.toAddSubgroup.comap (torusAmbientLinear f hf).toAddMonoidHom
```
i.e. the dualized-pullback map `L : ℂ^g → ℂ^m` sends `Λ_X` into `P.lattice`.

**Proof path (the math is in the repo, the wiring is not):**
1. `Λ_X` is the **range of the period map** on `H₁` (`periodLatticeInBasis` =
   `LinearMap.range (periodMapInBasis …)`), and is ℝ-spanned by **loop** periods
   (`span_periodLatticeInBasis_eq_top`, `Layer3/PeriodSpan.lean`). It suffices to
   send each generator `period(γ)` for an analytic loop `γ` into `P.lattice`.
2. For a loop `γ` in `X`, `f∘γ` is a loop in `A`. By the **already-proven**
   line-integral naturality `torusPullback_pathIntegral_naturality`
   (`∮_{f∘γ} ω = ∮_γ f*ω`), the period of `f∘γ` in cover coordinates equals
   `L (period γ)`.
3. The period of a **loop** `f∘γ` lies in `P.lattice`: it is the developing
   ambiguity of a closed path, i.e. `liftCoord` (mod `P.lattice`) of the common
   endpoint minus itself ∈ `ker(mk) = P.lattice`. This uses the self-Albanese
   integration identity of axiom #2 (`liftCoord_eq_albanese`) applied to `γ` and
   to the constant loop.

**Obstruction.** Step 3 routes through axiom #2's `liftCoord_eq_albanese`. As an
*input axiom* `AX_period_functoriality` takes an **arbitrary** `P :
TorusPresentation m A` (not necessarily the self-Albanese one), and a bare
`TorusPresentation` does **not** constrain `P.lattice` to be A's true period
lattice — so the statement-as-written is *not* provable for arbitrary `P` from
naturality alone. It becomes a theorem only when specialized to (or strengthened
to require) the self-Albanese presentation. Two clean options, both downstream of
#2:
- **(A)** restrict the hypothesis to `P` coming from `AX_torus_self_albanese`
  (or take a `TorusSelfAlbanesePresentation`), then run steps 1–3; or
- **(B)** absorb #3 into #2 by having `AX_torus_self_albanese` also emit the
  lattice-containment field.
Either way #3 is *gated on* #2 and cannot land before it. Medium effort once #2
exists.

---

## Axiom 4 — `AX_curve_generates_jacobian` — research-grade (Jacobi inversion)

```
AddSubgroup.closure (Set.range (Jacobian.ofCurve x₀)) = ⊤    (genus > 0)
```
The Abel–Jacobi image of the curve generates `J = ℂ^g/Λ_X` as an abstract group.

**Key obstruction — this is NOT the period-spanning result.** The repo's
spanning theorems (`span_real_loopPeriodLattice_eq_top`,
`span_periodLatticeInBasis_eq_top`) say the **loop period lattice** `Λ_X` spans
`ℝ^{2g}` — that is what makes `J` a genuine `g`-torus. Axiom 4 is the orthogonal
statement that the **curve image** (Abel–Jacobi of single points, *not* loops)
group-generates the quotient. That is **Jacobi inversion**: every point of `J` is
a sum/difference of `g` Abel–Jacobi images (effective divisors of degree `g`).
The standard proof uses Riemann–Roch + the surjectivity of `Symᵍ X → J`
(non-vanishing of a theta-type Jacobian determinant). None of that machinery is
in the repo; it is genuinely research-grade in Lean. (Note: the *closure* form
asked for is weaker than full surjectivity of `Symᵍ`, but the standard route to
it still goes through Jacobi inversion / non-degeneracy of the curve image, which
needs Riemann–Roch.)

---

## Recommended landing order

`#1` (done) → `#2` (uniformization of abstract flat compact complex Lie group;
the linchpin) → `#3` (medium, wire naturality through #2's identity, option A/B)
→ `#4` (independent, Jacobi inversion / Riemann–Roch). `#3` is the only one that
becomes *easy* once its prerequisite (#2) lands; `#2` and `#4` are independent
multi-week analytic formalizations.
