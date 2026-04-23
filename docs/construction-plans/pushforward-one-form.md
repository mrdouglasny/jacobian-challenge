# Plan #4: Construct `pushforwardOneForm` (trace)

## Axiom being retired

```lean
axiom pushforwardOneForm {X : Type u} [...] {Y : Type v} [...]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y
```

Location: `Jacobians/Axioms/AbelJacobiMap.lean:139`.

## Classical content

For a non-constant holomorphic map `f : X → Y` between compact Riemann
surfaces (automatically a finite branched cover), and a holomorphic
1-form `ω_X` on `X`, return the **trace** (or "pushforward,"
"transfer") `f_* ω_X ∈ Ω¹(Y)` defined as:

```
(f_* ω_X)(q) = Σ_{p ∈ f⁻¹(q)} (ω_X near p) / f'(p)  ·  (multiplicity if branched)
```

— a sum over the preimages of `q`, weighted by local multiplicities
from `localOrder` (Plan #5).

For constant `f`, `f_* ω_X = 0` by convention.

## Target replacement

```lean
noncomputable def pushforwardOneForm {X Y} [...] (f : X → Y) (hf : ContMDiff ...) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y := by
  by_cases hconst : ∃ c : Y, ∀ x : X, f x = c
  · -- constant case
    exact 0
  · -- non-constant case: f is finite branched cover
    exact -- finiteTraceOneForm f hf hconst (uses localOrder)
    sorry
```

## Prerequisites

### A. Plan #5 (`localOrder`)

Needed to weight preimages by local multiplicity.

### B. Finite-cover structure

For non-constant holomorphic `f : X → Y` between compact Riemann
surfaces, `AX_BranchLocus` (already in project) gives:
- Common fiber degree `d > 0`.
- Each `q ∈ Y` has exactly `d` preimages counted with multiplicity.
- Branch locus is finite.

Use this to define the fiber-sum.

Effort: ~100 LOC.

### C. Chart-local trace formula

In a chart `(V_q, ψ_q)` on `Y` around an unbranched point `q`, the map
`f` is locally invertible in a neighborhood of each preimage `p_i`.
Write `f⁻¹ᵢ : V_q → X` for the local section near `p_i`. Then:

```
(f_* ω_X)(w) = Σᵢ (coeff_X p_i (f⁻¹ᵢ(w)) / f'(f⁻¹ᵢ(w)))  dw
```

At branched points (finitely many), continuity extends the trace by
taking limits.

Effort: ~200 LOC.

### D. Preservation of holomorphicity

The trace of a holomorphic family is holomorphic (sum of holomorphic +
finite-cover analyticity). At branched points, use Riemann's removable
singularities theorem (Mathlib has this).

Effort: ~100 LOC.

### E. Preservation of cocycle

Similar to Plan #3's Phase P3 but in the opposite direction. The trace
on 1-forms is compatible with chart transitions on `Y` because the
preimage structure is natural.

Effort: ~150 LOC.

### F. ℂ-linearity

Pointwise via finite-sum linearity. Easy.

Effort: ~30 LOC.

## Phases

| Phase | Content | Effort | Depends on |
|---|---|---|---|
| P1 | `localOrder` | (Plan #5) | — |
| P2 | Finite-cover structure from `AX_BranchLocus` | 2 days | `AX_BranchLocus` (already axiom-routed) |
| P3 | Chart-local trace formula at unbranched points | 3 days | P1, P2 |
| P4 | Extension over branch points (removable singularities) | 3 days | P3 |
| P5 | Cocycle preservation + ℂ-linearity | 4 days | P4 |
| P6 | Retire `pushforwardOneForm` axiom + functoriality axioms | 2 days | P5 |

**Total: ~2 weeks** focused contributor (after Plan #5 lands).

## References

* Forster, Ch. I §6 (trace of differentials).
* Miranda, Ch. IV §2.
* Mumford, Vol I §II.3.

## Exit criterion

- `pushforwardOneForm` is a real `noncomputable def`.
- `AX_pushforwardOneForm_id` / `AX_pushforwardOneForm_comp` retire to theorems.
- Build green; net axiom count delta: **–3**.

## Downstream impact

- `pullbackAmbientLinear` becomes fully grounded.
- Jacobian-level `pullback` functoriality theorems derivable.
- `AX_pushforward_pullback` (the `f_* ∘ f^* = deg • id` identity)
  becomes **derivable**: with both `pullbackOneForm` and
  `pushforwardOneForm` as real defs, their composition can be computed
  chart-locally and shown to multiply by the degree via a finite-cover
  sum-over-preimages argument. This is the deepest classical fact in
  the challenge file (§24 in `challenge-annotated.md`).
