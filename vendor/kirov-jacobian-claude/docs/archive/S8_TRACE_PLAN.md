# Trace map: fixing S8 + closing S4 §3 (one shared leaf)

**Status:** design record + meet-in-the-middle plan. Created 2026-05-29.

## The one bug behind both S8 and S4 §3

There is **no trace map** (`f₊` on forms) in the codebase. Wherever the math
needs `f₊`, the matrix `M = ambientPsi` (the genuine *pullback* of forms `f*`)
was substituted as a placeholder. This single substitution is wrong in two
places:

| role | should be | code has | consequence |
|------|-----------|----------|-------------|
| Jacobian `pushforward` (Jac X→Y) | `Mᵀ` = `ambientPhi` | `Mᵀ` ✅ | **correct** (proven via `periodVec_pushforward`) |
| Jacobian `pullback` (Jac Y→X) | `Tᵀ` (trace transpose) | `M` = `ambientPsi` ✗ | `pushforward_pullback` claims `MᵀM = deg·I` — **false** (S8) |
| §3 `PreimageCycle.trace_eq` | `Tᵀ·periodVec δ = ∑ periodVec(lifts)` | `M·periodVec δ = …` ✗ | supports the false `ambientPsi_preserves_truePeriodLattice` |

### Why `Tᵀ`, not `M` (projection formula)

For a loop `δ` in `Y` off the branch locus, let `Γ = f⁻¹(δ)` be the preimage
cycle in `X`. Component `i`:

```
periodVec_X(Γ)_i = ∫_Γ ω_i^X = ∫_δ f₊(ω_i^X)        (projection formula)
                 = ∫_δ T(ω_i^X) = ∑_l T_{li} ∫_δ ω_l^Y = (Tᵀ · periodVec_Y δ)_i
```

so the Jacobian pullback on periods is `Tᵀ`, where `T = pushforwardForm` is the
trace of forms. `M = f*` (pullback of forms) is a *different* map; `M ≠ Tᵀ`.

### The trace identity (the leaf, Griffiths–Harris §2.7)

```
T ∘ f*  =  deg • id      on  HOF Y          (pushforwardForm ∘ pullbackForm = deg • id)
```

Equivalently in coordinates `ambientTrace ∘ ambientPsi = deg • id` on `Fin gY → ℂ`.
Transposing: `ambientPhi ∘ ambientPullbackJac = Mᵀ Tᵀ = (T M)ᵀ = deg • id`, which
is exactly the honest `pushforward_pullback`.

## Architecture (mirrors the existing `ambientPsi`/`ambientPhi` pair)

```
forms maps                         coordinate maps (Fin g → ℂ)        Jacobian map
─────────────────────────────────  ────────────────────────────────  ─────────────
f*  = pullbackForm   : HOF Y→HOF X  ambientPsi          : gY→gX (M)    (forms role only)
       (transpose ↓)                ambientPhi = Mᵀ     : gX→gY        pushforward  ✅
f₊  = pushforwardForm: HOF X→HOF Y  ambientTrace        : gX→gY (T)    (forms role only)   ◀ NEW
       (transpose ↓)                ambientPullbackJac=Tᵀ: gY→gX        pullback     ◀ NEW
```

`pushforwardForm` is the canonical leaf object; its three laws are the honest
sorries (G&H §2.7):
- `pushforwardForm_pullbackForm` : `T ∘ f* = deg • id`  (trace identity)
- `pushforwardForm_id`           : `T(id) = id`         (covariant functoriality)
- `pushforwardForm_comp`         : `T(g∘f) = T(g) ∘ T(f)`

Everything downstream is **proven** from these by the same transpose algebra
already used for `ambientPhi_id`/`ambientPhi_comp`:
- `ambientPullbackJac_id`, `ambientPullbackJac_comp` (contravariant)
- `ambientPhi_ambientPullback_eq : ambientPhi (ambientPullbackJac y) = deg • y`
- rewire `pullback := … ambientPullbackJac`, and `pushforward_pullback` follows.

This **removes the false statement** and isolates the content to one leaf.

## Connecting the ends (so §3 is not throwaway)

The downstream interface (`pushforwardForm` + laws) and the upstream geometry
(§3 preimage cycle) meet through the already-**proven** `periodVec_pushforward`
(`periodVec(f∘γ) = ambientPhi(periodVec γ)`):

```
preimage cycle Γ of δ  (§3, upstream)
   f∘Γ = deg·δ   ⟹   ambientPhi(periodVec Γ) = periodVec(f∘Γ) = deg·periodVec δ
   periodVec Γ = ambientPullbackJac(periodVec δ)
   ────────────────────────────────────────────────────────────────────────────
   ⟹  ambientPhi(ambientPullbackJac(periodVec δ)) = deg·periodVec δ   (S8 on periods)
```

With the period lattice full-rank (S3 `IsZLattice`), a ℂ-linear identity true on
the lattice is true everywhere ⟹ the trace identity holds. So:

> **§3 (preimage cycle) + `periodVec_pushforward` + S3 (spanning) ⟹ the trace
> identity ⟹ S8.** One geometric construction discharges the shared leaf.

The §3 `PreimageCycle` is therefore *repointed*, not deleted: its `trace_eq`
becomes the `Tᵀ` statement, and a new `pushforward_eq` field (`f∘Γ = deg·δ`)
carries the connection. The covering bridge
`isCoveringMap_restrictPreimage_compl_branchLocus` (proven) feeds the lift.

## Plan (split derisking, both ends)

1. **Downstream scaffold** (HolomorphicForms): `pushforwardForm` + laws (sorry),
   `ambientTrace`, `ambientPullbackJac`, proven `_id`/`_comp`.  ← start here
2. **Downstream wire** (Jacobians.lean): `ambientPhi_ambientPullback_eq`, rewire
   `pullback`/`pullback_id`/`pullback_comp`/`pushforward_pullback`. Delete the
   false `ambientPhi_ambientPsi_eq`. Build green, misformalization gone.
3. **Upstream build** (PeriodLattice §3): preimage cycle via the covering bridge
   + `liftPath` + monodromy; repoint `PreimageCycle` to `Tᵀ` + `pushforward_eq`.
4. **Connect**: prove the trace identity from §3 + `periodVec_pushforward` + S3,
   discharging the leaf sorries from step 1.

Walls that remain genuinely Mathlib-deficient and stay as cited sorries:
§2 (manifold de Rham/Stokes for period homotopy-invariance), the geometric
trace construction if step 4's lattice route is blocked by S3.

## Phase 3 findings (2026-05-29)

Status: steps 1–2 done; step 3 repoint done; the keystone (step 4 on periods)
proven. Within step 3 (the lift):

- **`fiber_finite_off_branchLocus` PROVEN** (unconditional off-branch): the fibre
  `f⁻¹(y)` for `y ∉ branchLocus f` is finite (isolated points via the proven
  `isLocalHomeoOffCritical` + compact). This is the cover's sheet count, the
  lift's foundation. Bypasses the discharge's identity-theorem-gated version.

- **Key coupling: `pullback_eq` ≡ the trace construction.** `PreimageCycle`'s
  `pullback_eq` (`ambientPullbackJac(periodVec δ) = ∑ coeffs·periodVec loopsᵢ`)
  relates the *opaque* `ambientPullbackJac` (= `Tᵀ`, built on the `sorry`
  `pushforwardForm`) to the concrete preimage-cycle geometry. It is **provable
  only once `pushforwardForm` is constructed** to satisfy the projection formula
  `∫_δ f₊ω = ∫_{f⁻¹(δ)} ω`. So the geometric lift gives `loops` + `pushforward_eq`
  (`f∘Γ = deg·δ`, from `periodVec_pushforward`) but **not** `pullback_eq`.

  ⟹ **The §3 `pullback_eq` and the S8 `pushforwardForm` leaf are the SAME content**
  (sum over the `deg` local sections of the cover + holomorphicity + removable-
  singularity extension = G&H §2.7). This is the single unified hard core.

Refined remaining work (one core, not two):
- **Geometric trace** `pushforwardForm f hf ω := ∑_{sheets} gᵢ^* ω` via the
  proven covering's local sections, holomorphic across branch points. Discharges
  `pushforwardForm`/`_id`/`_comp` AND the lift's `pullback_eq` (projection
  formula) together. ~500–1000 LOC, the analytic heart.
- The monodromy loops (for `loops`/`pushforward_eq`) are independent geometry,
  buildable from the covering bridge + `liftPath` (Mathlib has the API).
- Then `ambientPhi_ambientPullback_eq` off the lattice via S3 spanning.

## Two routes to `pushforward_pullback` (2026-05-29, after deep reuse-analysis)

Both discharge the same goal; they differ in what they reuse vs. build new.

**Route A — geometric trace on forms** (`ambientPullbackJac := Tᵀ`, current arch).
`pullback_eq` needs `pushforwardForm` constructed (sum over local holo sections).
- New: local **holomorphic** section ⇐ manifold IFT (**Mathlib gap**: only the
  chart-level complex IFT `AnalyticAt.analyticAt_localInverse` exists) + "analytic
  injective ⟹ deriv≠0" (not direct in Mathlib; via order theory) + global
  assembly + branch extension. Import-order wrinkle: `pushforwardForm` lives in
  HolomorphicForms (upstream of the covering in PeriodLattice) ⟹ relocate first.
- Reuse: chart machinery; Discharge's `LocalNormalForm`/`MeromorphicExtension`
  are for meromorphic *functions* X→ℂ (divisor theory), not the map X→Y — partial.
- Pro: `ambientPullbackJac` is ℂ-linear *by construction*.

**Route B — period-map pullback** (`ambientPullbackJac(periodVec δ) := periodVec(Γ_δ)`).
Makes `pullback_eq` **definitional**; the degree identity then follows from the
**proven** `periodVec_pushforward` + `f∘Γ = deg·δ`.
- New: the lift `Γ_δ` (monodromy loops via covering bridge + Mathlib `liftPath` +
  orbit-grouping + smoothness); ℂ-linear well-definedness of the period-map.
- Reuse (maximal): `periodVec_pushforward` (proven), the keystone (proven),
  fiber finiteness (proven); **well-definedness ⇐ §2 (Stokes) and spanning ⇐ S3 —
  both already-accepted project sorries, not new frontier deps.**
- Con: redefines `ambientPullbackJac`; ℝ-on-periods → ℂ-linear extension is subtle.

**Caveat (the shared irreducible core).** Route B's "ℂ-linear extension" Con is
*not* lighter than Route A's holomorphicity: the period-map `periodVec δ ↦
periodVec(Γ_δ)` is manifestly ℝ-linear but is ℂ-linear **iff** the pullback is
holomorphic — exactly Route A's content. So both routes share one irreducible
analytic core: **the Jacobian pullback is holomorphic / the trace of forms is a
holomorphic form** (G&H §2.7). There is no algebraic shortcut (the pseudo-inverse
`deg·(MᵀM)⁻¹Mᵀ` gives the degree identity but fails lattice-preservation and
functoriality, so it is *not* the genuine pullback).

**Recommendation.** Route B still reuses more *proven* machinery
(`periodVec_pushforward`, keystone, fiber finiteness) and its concrete first step
— the monodromy lift via the covering bridge + Mathlib `liftPath` — is buildable
now and gives `loops`/`pushforward_eq`. But the holomorphicity/ℂ-linearity core is
genuine analytic heart that Mathlib does not yet support (manifold IFT; analytic
open-mapping multiplicity): a **dedicated multi-session formalization**, not a
quick assembly. The surrounding engineering — architecture, `Tᵀ` rewire, keystone,
§3 repoint, lattice-preservation routing, fiber finiteness — is complete.
