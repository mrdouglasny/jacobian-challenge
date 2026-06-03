/-
`AX_BranchLocus`: properness, discrete fibers, and degree invariance
for non-constant holomorphic maps between compact Riemann surfaces.

**Statement (Lean, refined 2026-04-23).** For `f : X → Y` a non-constant
holomorphic map between compact Riemann surfaces, there exists a
common fiber degree `d > 0` such that:

1. `∀ q : Y, (∑' p : X, localOrder f p q) = d` — the weighted fiber
   count is `d` for every `q`.
2. `{ q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite` —
   only finitely many `q` have branch points above them.

`localOrder f p q : ℕ` is the local multiplicity: `0` if `f p ≠ q`,
otherwise the degree of zero of `f(·) - q` at `p` (≥ 1).

## Consequences

* `ContMDiff.degree f` is well-defined as this common `d`; via
  `Classical.choose` on the existential.
* `pushforward_pullback = deg • id` reduces to fiber-counting using (1).
* The locus `{q : Y | ramified at q}` being finite lets us do "generic
  Hurwitz-style" analyses.

## Why axiomatized

The proof uses: non-constant holomorphic maps are open (Open Mapping
Theorem for 1-dim), combined with compactness of `X` and connectedness
of `Y`. All standard, but Mathlib's open-mapping-for-holomorphic-maps
infrastructure is specific to `ℂ`-valued maps, not maps between
manifolds.

## History

- 2026-04-22 (Gemini review #1): flagged — replace `toFinset`-based
  statement with `tsum` + `¬ ∃ c, ∀ x, f x = c` (non-constant in
  standard form).
- 2026-04-23 (A7 in completion plan): promoted from doc-only to real
  Lean statement via opaque `localOrder`.

See `docs/formalization-plan.md` §7, discharge priority #6;
`docs/completion-plan.md` workstream A7.
Reference: Forster Ch. I §4; Mumford Vol I §II.2.
-/
import Jacobians.RiemannSurface.OneForm
import Jacobians.Vendor.Wallace.HolomorphicForms.HolomorphicMap

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff Classical

open Jacobians.Vendor.Wallace.HolomorphicForms

/-- The local order (ramification multiplicity) of the holomorphic map `f` at
point `p` above `q`:

    localOrder f p q = 0                 if f p ≠ q,
    localOrder f p q = k ≥ 1             if f p = q and f locally looks
                                         like `z ↦ q + c·(z-p)^k` with
                                         `c ≠ 0`.

**Discharged (2026-06-03)** from an opaque axiom to a real definition: when
`f p = q` it is the analytic order of `f` at `p`,
`Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt f p` (the chart-local
`analyticOrderNatAt` of `f`, sorry-free in the adopted Wallace `HolomorphicMap`
module — Forster Ch. I §4, Mumford Vol I §II.2). Well-defined because non-constant
holomorphic maps in dimension 1 have isolated zeros of their Taylor series. -/
noncomputable def localOrder {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (p : X) (q : Y) : ℕ :=
  if f p = q then Jacobians.Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt f p else 0

private theorem analyticOrderNatAt_pow_zero (k : ℕ) :
    analyticOrderNatAt (fun z : ℂ => z ^ k) 0 = k := by
  have heq : ((· - (0 : ℂ)) ^ k) = (fun z : ℂ => z ^ k) := by funext z; simp
  have key : analyticOrderAt (fun z : ℂ => z ^ k) 0 = (k : ℕ∞) :=
    heq ▸ analyticOrderAt_centeredMonomial
  simp [analyticOrderNatAt, key]

/-- **Faithfulness witness for `localOrder`.** The canonical `k`-fold cover
`z ↦ zᵏ` has local order exactly `k` at the origin (`1` for an unramified `k = 1`,
`≥ 2` for genuine ramification). This pins the discharged `def` to the intended
ramification index on a concrete absolute case — the kind of non-vacuity check the
kernel cannot supply for a definition. -/
theorem localOrder_pow {k : ℕ} (hk : 0 < k) :
    localOrder (fun z : ℂ => z ^ k) 0 0 = k := by
  have hf0 : (fun z : ℂ => z ^ k) 0 = 0 := by simp [zero_pow hk.ne']
  rw [localOrder, if_pos hf0]
  have hmap : mapAnalyticOrderAt (fun z : ℂ => z ^ k) 0
      = analyticOrderNatAt (fun z : ℂ => z ^ k) 0 := by
    unfold mapAnalyticOrderAt chartLocalAt
    simp [zero_pow hk.ne']
  rw [hmap, analyticOrderNatAt_pow_zero]

/-- **Axiom (BranchLocus).** For a non-constant holomorphic map between
compact Riemann surfaces, there's a common degree `d` such that
fiber-sums of `localOrder` all equal `d`, and the branch locus is
finite. -/
axiom AX_BranchLocus {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (_hnc : ¬ ∃ c : Y, ∀ x : X, f x = c) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
      { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite

end Jacobians.Axioms
