/-
# Liouville axioms for hyperelliptic curves and the genus upper bound

This file packages a three-level hierarchy from most abstract to most
project-specific. Each lower level is *derivable* from the one above plus
standard complex-analysis machinery. **Level 1 is now a proven theorem**
(`liouville_compact_complex_manifold`, axiom-free, 2026-05-31); Levels 2
and 3 remain axiomatized because the chart-local growth-bound and
function-field-decomposition machinery they need is not yet in Mathlib.
Each carries a documented proof plan for its eventual derivation.

The lowest-level axiom (`AX_HyperellipticOneForm_eq_form`) is what
actually feeds the genus upper bound; the higher-level axioms exist to
make the *structure* of the eventual proof legible, and to allow a
future discharge starting from whichever level Mathlib catches up to.

## The hierarchy

```
       liouville_compact_complex_manifold  (Level 1 — PROVEN, axiom-free)
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
import Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Jacobians.RiemannSurface
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic
import Jacobians.GeneralResults.EntireGrowth
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace Jacobians.Axioms.HyperellipticLiouville

open scoped Manifold ContDiff Topology
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

**Status: PROVEN (2026-05-31), axiom-free.** No longer an axiom — the
global maximum-modulus principle is now a real theorem
`liouville_compact_complex_manifold` below, depending only on Lean's core
axioms. The proof realises the plan below using Mathlib's chart-local
maximum modulus (`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`) and the
smoothness of chart inverses (`contMDiffOn_extChartAt_symm`).

**Proof.**
1. Compactness ⇒ `‖f‖` attains its max at some `p₀ ∈ M`.
2. The set `S = {x | f x = f p₀}` is closed (continuity) and nonempty.
3. `S` is open: at any `q ∈ S`, `F := f ∘ (extChartAt I q).symm` is
   holomorphic on the chart target and `‖F‖` has its maximum at the centre
   (global max), so by the maximum modulus principle `F` is constant on a
   ball; pulling back gives `f = f q = f p₀` on a neighbourhood of `q`.
4. `S` clopen + `M` connected ⇒ `S = univ`, i.e. `f ≡ f p₀`.
-/
open Set Filter Metric in
/-- **Liouville / global maximum modulus.** Every holomorphic
(`MDifferentiable`) function from a compact connected complex 1-manifold
(a compact connected Riemann surface) to `ℂ` is constant. Axiom-free. -/
theorem liouville_compact_complex_manifold
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    (f : M → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, ∀ x : M, f x = c := by
  have hcont : Continuous f := hf.continuous
  -- `‖f‖` attains a global maximum at some `p₀` (compactness).
  obtain ⟨p₀, -, hp₀⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := M))
    hcont.norm.continuousOn
  have hp₀' : ∀ x, ‖f x‖ ≤ ‖f p₀‖ := fun x => hp₀ (mem_univ x)
  refine ⟨f p₀, ?_⟩
  set S : Set M := {x | f x = f p₀} with hS
  have hSne : S.Nonempty := ⟨p₀, rfl⟩
  have hScl : IsClosed S := isClosed_eq hcont continuous_const
  have hSop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hq                       -- hq : f q = f p₀
    set φ := extChartAt 𝓘(ℂ) q with hφ
    have hqs : q ∈ φ.source := mem_extChartAt_source q
    have hqsymm : φ.symm (φ q) = q := φ.left_inv hqs
    have hc_mem : φ q ∈ φ.target := mem_extChartAt_target q
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target q) (φ q) hc_mem
    -- `F := f ∘ φ.symm` is holomorphic on the ball.
    have hFdiff : DifferentiableOn ℂ (f ∘ φ.symm) (ball (φ q) r) := by
      have h1 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ.symm φ.target :=
        (contMDiffOn_extChartAt_symm q).mdifferentiableOn WithTop.top_ne_zero
      have hf_on : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f univ := hf.mdifferentiableOn
      have h2 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ φ.symm) φ.target :=
        hf_on.comp h1 (mapsTo_univ _ _)
      exact (mdifferentiableOn_iff_differentiableOn.mp h2).mono hball
    -- `‖F‖` has its maximum on the ball at the centre `φ q`.
    have hmax : IsMaxOn (norm ∘ (f ∘ φ.symm)) (ball (φ q) r) (φ q) := by
      intro z _
      simp only [Function.comp_apply]
      calc ‖f (φ.symm z)‖ ≤ ‖f p₀‖ := hp₀' _
        _ = ‖f q‖ := by rw [hq]
        _ = ‖f (φ.symm (φ q))‖ := by rw [hqsymm]
    -- Maximum modulus ⇒ `F` constant on the ball.
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm isPreconnected_ball
      isOpen_ball hFdiff (mem_ball_self hr) hmax
    -- Pull the constancy back to a neighbourhood of `q`.
    have hN : φ ⁻¹' (ball (φ q) r) ∈ 𝓝 q :=
      (continuousAt_extChartAt q).preimage_mem_nhds (ball_mem_nhds _ hr)
    have hsrc : φ.source ∈ 𝓝 q := extChartAt_source_mem_nhds q
    have hsub : φ.source ∩ φ ⁻¹' (ball (φ q) r) ⊆ S := by
      rintro x ⟨hxs, hxb⟩
      have hx := heq hxb
      have hxx : φ.symm (φ x) = x := φ.left_inv hxs
      show f x = f p₀
      have hfx : f (φ.symm (φ x)) = f (φ.symm (φ q)) := hx
      rw [hxx, hqsymm, hq] at hfx
      exact hfx
    exact Filter.mem_of_superset (Filter.inter_mem hsrc hN) hsub
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hScl, hSop⟩ hSne
  intro x
  have hxS : x ∈ S := hSuniv ▸ mem_univ x
  exact hxS

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
- Apply `liouville_compact_complex_manifold` (now a proven theorem) to
  `f - g/y` for appropriate test polynomials, deducing `f = g/y` modulo a
  constant.
- Use the cocycle (now real for inl_inr) to extend chart-local
  agreement to global.
- Bound `deg(g)` via the chart-overlap behaviour at infinity.

**Step 4 of this plan ("the extracted `g := coeff · √f` is entire with
polynomial growth ⇒ it is a polynomial of degree `< N/2 − 1`") is now a
proven, axiom-free lemma**: `differentiable_eq_polynomial_of_growth` in
`Jacobians/GeneralResults/EntireGrowth.lean`. What remains project-specific
is constructing that entire extension and its growth exponent from the
chart-cocycle data (steps 1–3) — the branch-point regularity and the
degree-at-infinity bound. -/
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
  set n := H.f.natDegree / 2 - 1 with hn_def
  -- The linear map degreeLT ℂ n → HolomorphicOneForm is `hyperellipticFormLinearMap`.
  let φ : Polynomial.degreeLT ℂ n →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticEvenProj H) :=
    HyperellipticEvenProj.hyperellipticFormLinearMap H
  -- φ is surjective by Level 3 axiom.
  have hφ_surj : Function.Surjective φ := by
    intro form
    obtain ⟨g, hg_deg, hgform⟩ := AX_HyperellipticOneForm_eq_form form
    have hg_in : g ∈ Polynomial.degreeLT ℂ n := by
      rw [Polynomial.mem_degreeLT]
      by_cases hg : g = 0
      · rw [hg]; simp [Polynomial.degree_zero]
      · rw [Polynomial.degree_eq_natDegree hg]; exact_mod_cast hg_deg
    refine ⟨⟨g, hg_in⟩, ?_⟩
    change HyperellipticEvenProj.hyperellipticForm H g = form
    exact hgform.symm
  -- Module.rank inequality from surjective linear map.
  have h_rank_le : Module.rank ℂ (HolomorphicOneForm (HyperellipticEvenProj H)) ≤
      Module.rank ℂ (Polynomial.degreeLT ℂ n) :=
    LinearMap.rank_le_of_surjective φ hφ_surj
  -- Convert to finrank.
  have h_target_finite : Module.Finite ℂ (Polynomial.degreeLT ℂ n) :=
    inferInstance
  have h_finrank_le : Module.finrank ℂ (HolomorphicOneForm (HyperellipticEvenProj H)) ≤
      Module.finrank ℂ (Polynomial.degreeLT ℂ n) :=
    Module.finrank_le_finrank_of_rank_le_rank (by simpa using h_rank_le)
      (Module.rank_lt_aleph0 ℂ _)
  -- Compute Module.finrank ℂ (Polynomial.degreeLT ℂ n) = n.
  have h_finrank_degreeLT : Module.finrank ℂ (Polynomial.degreeLT ℂ n) = n := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ n)]; simp
  change Module.finrank ℂ (HolomorphicOneForm (HyperellipticEvenProj H)) ≤ n
  rw [← h_finrank_degreeLT]; exact h_finrank_le

end Jacobians.Axioms.HyperellipticLiouville
