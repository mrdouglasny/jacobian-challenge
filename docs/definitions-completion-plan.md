# Definition-completion plan

_Drafted 2026-04-23. Target: turn remaining definition-level axioms into
real `def`s / `structure`s wherever tractable in a single session;
document the ones that require multi-week infrastructure._

## Scope

User request: "get all the definitions complete and correct." Focus on
**type-level** and **def-level** axioms, not Prop-level property
axioms. Property theorems are orthogonal and triaged elsewhere.

## Tractable in this session

### Workstream A: Functoriality derivations (Gemini round-2 follow-up)

The round-2 refactor replaced `pushforwardAmbientLinear` /
`pullbackAmbientLinear` axioms with `def`s derived from
`pullbackOneForm` / `pushforwardOneForm` via `.dualMap`. Gemini noted:
"functoriality is free via contravariance of `Module.Dual`." Cash that
in:

- **A1.** Add form-level functoriality axioms:
  - `AX_pullbackOneForm_id : pullbackOneForm id = LinearMap.id`
  - `AX_pullbackOneForm_comp : pullbackOneForm (g ∘ f) = pullbackOneForm f ∘ pullbackOneForm g`
  - Symmetric for `pushforwardOneForm` (note: pushforward is covariant in maps, so `pushforwardOneForm (g ∘ f) = pushforwardOneForm g ∘ pushforwardOneForm f`).
- **A2.** Convert the four Jacobian-level axioms to **theorems**:
  - `AX_pushforward_id_apply`, `AX_pushforward_comp_apply`
  - `AX_pullback_id_apply`, `AX_pullback_comp_apply`
  
  Derivations unfold through:
  ```
  pushforwardImpl = jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf) _
  pushforwardAmbientLinear = eY ∘ (pullbackOneForm f).dualMap ∘ eX.symm
  ```
  Using `AX_pullbackOneForm_id` + `LinearMap.dualMap_id` +
  basis-equiv cancellation + `QuotientAddGroup.map_id` + ULift trivia.

### Workstream B: Hyperelliptic + PlaneCurve types as real defs

- **B1.** `def Hyperelliptic (H : HyperellipticData) : Type := OnePoint (HyperellipticAffine H)` — real def.
- **B2.** Derive topology / T2 / compact / nonempty instances from `OnePoint` infrastructure + `HyperellipticAffine` instance transfer from ℂ².
  - `HyperellipticAffine H` is a closed subtype of `ℂ × ℂ` via `y² = f(x)`; inherits `TopologicalSpace`, `T2Space`, `LocallyCompactSpace` automatically.
  - `OnePoint` of a locally-compact-Hausdorff-nonempty space is compact + T2 + nonempty.
- **B3.** `ConnectedSpace` requires `ConnectedSpace (HyperellipticAffine H)` — classical fact for squarefree `f` of degree ≥ 3; axiomatize as a small `AX_HyperellipticAffine_connected` subfact.
- **B4.** `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` stay **axioms** — these are the atlas construction, out of scope per `docs/hyperelliptic-atlas-plan.md` (~2–3 weeks).
- **B5.** Same treatment for `PlaneCurve`: real def via `OnePoint` (or `WeightedProjective` if available; start simple), derive 5/7 instances, leave atlas as axioms.

### Net effect (tractable set)

| Before | After |
|---|---|
| 4 Jacobian-level functoriality axioms | 4 form-level axioms + 4 theorems |
| `axiom Hyperelliptic : Type` + 6 instance axioms | `def Hyperelliptic` + 5 real instances + 2 remaining (atlas) axioms + 1 sub-axiom for connectedness |
| `axiom PlaneCurve : Type` + 6 instance axioms | same as Hyperelliptic |

## Out of scope (documented)

### Infrastructure-blocked: needs Mathlib additions or sub-projects

- **`pullbackOneForm`, `pushforwardOneForm`, `pathIntegralBasepointFunctional`** — concrete constructions require manifold-cotangent-bundle API, path-integral API, trace of meromorphic forms. Each is a sub-project of weeks.
- **`localOrder`, `loopIntegralToH1`** — order of zero for manifold maps; homotopy invariance of path integral. Multi-week.
- **`LineBundle`, `H0`, `H1`, `canonicalDivisor`, `LineBundle.ofDivisor`** — sheaf cohomology for complex manifolds is not in Mathlib. Each requires sheaf-theoretic infrastructure.
- **`abelJacobiDiv`, `intersectionForm`** — cup product + abel-jacobi-on-divisors machinery; 1–2 weeks each.
- **`Hyperelliptic.instChartedSpace`, `Hyperelliptic.instIsManifold`** — the atlas construction; 2–3 weeks (see `docs/hyperelliptic-atlas-plan.md`).

### Tractable but cheap: `Divisor`

- `Divisor X := X →₀ ℤ` (finitely-supported ℤ-valued functions on X).
  - AddCommGroup is auto from `Finsupp`.
  - `Divisor.deg := Finsupp.sum (fun _ n => n)`.
- Could be done but has subtle interactions with `LineBundle.ofDivisor` (still axiom), `PrincipalDivisors` (needs meromorphic functions, still axiom), and `abelJacobiDiv` (still axiom). The Divisor def would be clean but its downstream uses remain axiomatized. Worth doing if there's time at the end.

## Execution order

1. B1: `def Hyperelliptic` + 5 instances (likely ~30 min).
2. B5: `def PlaneCurve` + 5 instances (~15 min, parallel structure).
3. A1: form-level functoriality axioms (~10 min).
4. A2: Jacobian-level functoriality theorem derivations (~1 hour, may need iteration).
5. Optional: `Divisor X := X →₀ ℤ` + `Divisor.deg` (~20 min).
6. Update docs (status.md, README).

Build check after each phase.
