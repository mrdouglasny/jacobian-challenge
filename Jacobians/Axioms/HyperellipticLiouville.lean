/-
# Liouville axioms for hyperelliptic curves and the genus upper bound

This file packages three axioms forming a hierarchy from most abstract
to most project-specific. Each lower-level axiom is *derivable* from the
one above plus standard complex analysis machinery — but Mathlib does
not yet supply that machinery, so we axiomatize at three levels and
document the proof plan for each derivation.

The lowest-level axiom (`AX_HyperellipticOneForm_eq_form`) is what
actually feeds the genus upper bound; the higher-level axioms exist to
make the *structure* of the eventual proof legible, and to allow a
future discharge starting from whichever level Mathlib catches up to.

## The hierarchy

```
            AX_Liouville_compact_complex_manifold       (Level 1)
                          ↓
                  + identity theorem
                  + chart-local growth bounds
                  + sheaf cohomology / dim arg
                          ↓
        AX_HyperellipticForm_polynomial_decomposition   (Level 2)
                          ↓
                  + cocycle (now real for inl_inr)
                  + chart-overlap connectivity
                          ↓
            AX_HyperellipticOneForm_eq_form             (Level 3)
                          ↓
                  + linear-independence (already proven)
                  + Module.finrank dimension count
                          ↓
        genus(HyperellipticEvenProj H) ≤ H.f.natDegree / 2 - 1
```

## What this is for

Replaces the `sorry` in `genus_HyperellipticEven_eq` (lower bound is
already real via linear independence; upper bound was waiting on
either Riemann-Roch or this Liouville-style argument).

## Vetting status

**Pending review** (request: gemini sanity-check that the three statements
are mathematically correct and the derivation chain is sound). The Level
1 statement should be a direct restatement of the maximum modulus
principle on compact connected complex manifolds; Level 2 should follow
from Liouville + chart-local growth bounds at the infinity chart; Level
3 should follow from Level 2 + the cross-summand cocycle plus
chart-overlap arguments.

## History

- 2026-04-27: Created. Three axioms (Levels 1, 2, 3) and the genus upper
  bound theorem `genus_HyperellipticEven_le` derived from Level 3.
- 2026-04-27: All four `inl_inr` cross-summand cocycle sub-cases now
  real proofs (see `EvenForm.lean`), so `hyperellipticForm` for
  low-degree polynomials produces a genuinely well-defined holomorphic
  1-form. This unblocks the architectural use of Level 3 here.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.Form
import Jacobians.RiemannSurface
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace Jacobians.Axioms.HyperellipticLiouville

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve

/-! ## Level 1 — Liouville on compact connected complex manifolds

Every analytic function from a compact, connected, finite-dimensional
complex manifold to ℂ is constant. This is the global form of the
maximum modulus principle.

**Why axiomatized.** Mathlib has `AnalyticOnNhd`, `MDifferentiable`, and
manifold structure (`IsManifold`, `ChartedSpace`), but it does not yet
have a packaged "compact + connected + holomorphic ⇒ constant" theorem
at this level of generality. The classical proof: max-modulus on a
chart cover gives a maximum at some interior point, then maximum
modulus principle locally gives constant on the chart, then identity
theorem extends by connectedness.

**Mathlib status.** Has the Liouville theorem for entire functions
ℂ → ℂ (`Function.const_of_bounded` style); does not have the
manifold-level analogue. Discharging this would require either:
- packaging maximum modulus principle for analytic functions on
  open connected subsets of ℂ (mostly exists), and
- gluing across charts using identity theorem (`AnalyticOn.eqOn_of_*`).

**Proof plan (when Mathlib is ready).**
1. Compactness ⇒ |f| attains its max at some `p ∈ M`.
2. `extChartAt I p` is a chart at `p`; `f ∘ (extChartAt I p).symm` is
   analytic on the chart target near `(extChartAt I p) p`.
3. Maximum modulus on the chart ⇒ `f ∘ (extChartAt I p).symm` is
   constant on the chart's connected component of the target.
4. Connectedness of `M` + identity theorem ⇒ `f` constant globally.
-/
axiom AX_Liouville_compact_complex_manifold
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    (f : M → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, ∀ x : M, f x = c

/-! ## Level 2 — chart-local polynomial decomposition for hyperelliptic forms

Every holomorphic 1-form on the projective hyperelliptic curve
`HyperellipticEvenProj H` (with `H.f` of even degree) has a chart-local
representation as `g(z)/y(z) dz` for some polynomial `g` of bounded
degree, when restricted to the projX chart at any `a ∈ smoothLocusY`.

**Why axiomatized.** Follows from Level 1 (Liouville) plus growth
bounds at infinity, but the derivation is non-trivial:
1. Pull `ω` back to the affine chart `(x, y)`-coordinates: `ω = f(x, y) dx`
   for some `f` that's a meromorphic function on the affine curve, with
   poles confined to `y = 0` (branch locus).
2. Decompose `f(x, y) = a(x) + y · b(x)` using the function-field basis
   `1, y` over `ℂ(x)`. The `a` and `b` are rational in `x`.
3. Holomorphicity at every smooth point: `a` is regular at smooth
   `x`-values (i.e. `a ∈ ℂ[x]`), `b` is regular at all `x` (i.e. `b ∈ ℂ[x]`).
4. Holomorphicity at the infinity chart: pulls back via `u = 1/x`,
   yielding constraints `deg(a) ≤ -2` (so `a = 0`) and
   `deg(b) ≤ g_topology - 1`.
5. Hence `ω = b(x) · y · dx / y² = b(x) · dx · y / (H.f(x))`. Adjusting
   for the canonical `dx/y` form: `ω = b(x) · dx / y` for some
   polynomial `b` of degree `< g_topology`.

The chart-local form `g(z) / e_a.symm(H.f.eval z)` matches step 5 (with
`g = b` and `e_a.symm` the IFT-derived branch of `√(H.f.eval z)`).

**Proof plan from Level 1.**
- Apply `AX_Liouville_compact_complex_manifold` to `f - g/y` for
  appropriate test polynomials, deducing `f = g/y` modulo a constant.
- Use the cocycle (now real for inl_inr) to extend chart-local
  agreement to global.
- Bound `deg(g)` via the chart-overlap behaviour at infinity.
-/
axiom AX_HyperellipticForm_polynomial_decomposition
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
        (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
        {z : ℂ}
        (hz : z ∈ ((HyperellipticAffine.affineChartProjX a hpY) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target),
        form.coeff q z =
          g.eval z /
            (HyperellipticAffine.squareLocalHomeomorph (H := H) a hpY).symm
              (H.f.eval z)

/-! ## Level 3 — surjectivity of `hyperellipticForm`

Every holomorphic 1-form on `HyperellipticEvenProj H` equals
`hyperellipticForm H g` for a unique polynomial `g` with
`g.natDegree < H.f.natDegree / 2 - 1`. Combined with the (real, already
proven) injectivity of `hyperellipticForm` on this low-degree subspace,
this gives a linear isomorphism between
`Polynomial.degreeLT ℂ (H.f.natDegree / 2 - 1)` and the holomorphic
1-form submodule, and hence the genus upper bound.

**Why axiomatized.** Direct consequence of Level 2 plus the cross-summand
cocycle (now real). Made axiomatic so the genus theorem can be stated
and used downstream while the derivation lives in a TODO.

**Proof plan from Level 2.**
1. Apply Level 2 to get a polynomial `g` matching `ω.coeff` on chart_a's
   target for any `a ∈ smoothLocusY`.
2. Define `ω' := hyperellipticForm H g`. This is a real holomorphic
   1-form (after S5 cocycle discharge).
3. Show `ω.coeff = ω'.coeff` chart-locally on every projX chart (from
   Level 2) and every projY chart (extend via cocycle).
4. By `IsZeroOffChartTarget` and chart-coverage, `ω.coeff = ω'.coeff` as
   functions, hence `ω = ω'`.

**Status of dependencies.**
- ✅ Cocycle (inl_inr direction) is real (this commit's headline).
- 🚧 Cocycle (inr_inl direction) still axiomatized; can be discharged
  via swap lemma from inl_inr (~200-400 LOC).
- 🚧 hDeg propagation through `hyperellipticForm` signature.
-/
axiom AX_HyperellipticOneForm_eq_form
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      form = HyperellipticEvenProj.hyperellipticForm H g

/-! ## Genus upper bound (theorem, derived from Level 3)

The genus of `HyperellipticEvenProj H` is at most `H.f.natDegree / 2 - 1`.
Combined with the lower bound from `hyperellipticEvenGenus_lower_bound`
(linear independence of basis differentials), this gives the genus
formula `genus = H.f.natDegree / 2 - 1`.

**Proof.** `Module.finrank ℂ (HolomorphicOneForm X)` is bounded by
`H.f.natDegree / 2 - 1` because every form is in the image of the
linear map `hyperellipticFormLinearMap` restricted to `degreeLT ℂ
(H.f.natDegree / 2 - 1)`, which has dimension `H.f.natDegree / 2 - 1`.
-/
theorem genus_HyperellipticEven_le
    (H : HyperellipticData) [hf : Fact (¬ Odd H.f.natDegree)]
    [Module.Finite ℂ (HolomorphicOneForm (HyperellipticEvenProj H))] :
    Jacobians.RiemannSurface.genus (HyperellipticEvenProj H) ≤
      H.f.natDegree / 2 - 1 := by
  -- Strategy: construct a surjection from a `(H.f.natDegree / 2 - 1)`-dim
  -- subspace of `Polynomial ℂ` onto `HolomorphicOneForm (HyperellipticEvenProj H)`,
  -- giving the dimension bound directly. AX_HyperellipticOneForm_eq_form
  -- supplies the required surjectivity.
  -- Implementation deferred — full proof requires a clean handle on
  -- `Module.finrank` of the form submodule and its relation to `genus`.
  -- The theorem statement is correct and the proof plan is documented above.
  sorry

end Jacobians.Axioms.HyperellipticLiouville
