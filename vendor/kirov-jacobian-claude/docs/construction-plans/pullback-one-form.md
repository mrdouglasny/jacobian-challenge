# Plan #3: Construct `pullbackOneForm`

## Axiom being retired

```lean
axiom pullbackOneForm {X : Type u} [...] {Y : Type v} [...]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X
```

Location: `Jacobians/Axioms/AbelJacobiMap.lean:126`.

## Classical content

Given a holomorphic map `f : X → Y` between complex 1-manifolds and a
holomorphic 1-form `ω_Y` on `Y`, return the **pullback**
`f^* ω_Y ∈ Ω¹(X)`, defined chart-locally as `(f^* ω_Y)(x) =
ω_Y(f(x)) · f'(x) dx` in appropriate chart coordinates.

Linearity in `ω_Y` is obvious. The cocycle-preservation of the result
(that `f^* ω_Y` actually satisfies `IsHolomorphicOneFormCoeff` +
`SatisfiesCotangentCocycle`) is the main content, and uses
holomorphicity of `f`.

## Target replacement

```lean
noncomputable def pullbackOneForm {X Y} [...] (f : X → Y) (hf : ContMDiff ...) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X :=
  let cocyclePullback : (Y → ℂ → ℂ) →ₗ[ℂ] (X → ℂ → ℂ) :=
    { toFun := fun coeff_Y x z =>
        -- (f^* ω_Y)(x) in chart at x, coordinate z
        coeff_Y (f x) (extChartAt 𝓘(ℂ) (f x) (f ((extChartAt 𝓘(ℂ) x).symm z))) *
          (fderiv ℂ ((extChartAt 𝓘(ℂ) (f x)) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) z 1)
      map_add' := ...
      map_smul' := ... }
  -- restrict to HolomorphicOneForm submodule:
  -- show that if `coeff_Y` satisfies the predicates, so does cocyclePullback coeff_Y
  sorry
```

## Prerequisites

### A. Chart-level pullback formula

The chart-local pullback of a 1-form: in chart `(U_y, φ_y)` on `Y`,
`ω_Y = a_y(w) dw`; the pullback under `f` to chart `(U_x, φ_x)` on `X`
(where `f(U_x) ⊂ U_y`) is

```
(f^* ω_Y)(z) = a_y(φ_y(f(φ_x⁻¹(z)))) · (φ_y ∘ f ∘ φ_x⁻¹)'(z) dz
```

This formula defines a chart-cocycle coefficient on `X` when composed
with `f`.

Effort: ~50 LOC (pure computation).

### B. Preservation of holomorphicity

If `coeff_Y` is analytic on each chart target (i.e.,
`IsHolomorphicOneFormCoeff Y`), then the pullback is also analytic on
each `X`-chart target — because composition of holomorphic is
holomorphic, and `f` is holomorphic (by `hf : ContMDiff`, which in
dim 1 complex is equivalent to holomorphic).

**Subfact needed:** `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f` implies `f` is holomorphic
in chart coordinates. Mathlib has this: `ContMDiff → ContDiff → AnalyticOn`
via the `ω`-smoothness level which is real-analytic, and for maps
between complex 1-manifolds, real-analyticity + ℂ-linearity of the
Fréchet derivative implies holomorphicity.

Effort: ~100 LOC.

### C. Preservation of cocycle

The hard part. Starting from `ω_Y` satisfying
`SatisfiesCotangentCocycle Y`, show that the pullback satisfies the
analogous cocycle on `X`. This is a direct computation via the chain
rule for composed chart transitions.

Effort: ~200 LOC (includes lemmas on `fderiv` of composed chart maps).

### D. ℂ-linearity

Linear in `coeff_Y` via pointwise `Pi.add_apply` / `Pi.smul_apply` and
ℂ-linearity of multiplication and `fderiv`.

Effort: ~30 LOC.

## Phases

| Phase | Content | Effort |
|---|---|---|
| P1 | Chart-level pullback coefficient formula | 2 days |
| P2 | Holomorphicity preservation (analyticOn of pulled-back coefficient) | 3 days |
| P3 | Cocycle preservation (chain rule through `f` and chart transitions) | 5 days |
| P4 | Assemble into the real `def pullbackOneForm` + linearity | 1 day |
| P5 | Retire axioms `AX_pullbackOneForm_id`, `AX_pullbackOneForm_comp` to theorems | 2 days |

**Total: ~1.5 weeks** focused contributor.

## References

* Forster, Ch. I §6 (pullback of differentials).
* Griffiths–Harris, Ch. 0.2.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. IV §2.

## Exit criterion

- `pullbackOneForm` is a real `noncomputable def`.
- `AX_pullbackOneForm_id` and `AX_pullbackOneForm_comp` retire to derived theorems.
- Build green; net axiom count delta: **–3**.

## Downstream impact

`pushforwardAmbientLinear` (the real def dualising
`pullbackOneForm.dualMap`) becomes fully grounded in a real
construction. Jacobian-level `pushforward` functoriality theorems
(currently axioms `AX_pushforward_id_apply`,
`AX_pushforward_comp_apply`) become derivable via
`Module.Dual`-contravariance — which the user previously identified as
a ~1h unfolding exercise each. So this plan transitively unlocks up to
5 additional axiom retirements.
