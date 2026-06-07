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
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity
open Jacobians.ProjectiveCurve.HyperellipticEvenProj

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
noncomputable def liouvilleGlobalNumerator
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ := by
  classical
  intro z
  by_cases hz : H.f.eval z = 0
  · let p := liouvilleBranchPoint (H := H) z hz
    exact liouvilleProjYNumerator (H := H) form p
      (liouvilleBranchPoint_mem_smoothLocusX (H := H) hz)
      (HyperellipticEvenProj.proj H (Sum.inl p)) 0
  · let y := Classical.choose (IsAlgClosed.exists_eq_mul_self (H.f.eval z))
    have hy : H.f.eval z = y * y :=
      Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (H.f.eval z))
    let a : HyperellipticAffine H := ⟨(z, y), by
      change y ^ 2 = H.f.eval z
      simpa [pow_two] using hy.symm⟩
    have hpY : a ∈ HyperellipticAffine.smoothLocusY H := by
      change y ≠ 0
      intro hy0
      apply hz
      simpa [hy0] using hy
    exact liouvilleProjXNumerator (H := H) form a hpY
      (HyperellipticEvenProj.proj H (Sum.inl a)) z

/-- The sheet-chosen affine numerator away from branch points:
`affCoeff · y`.  It is not used at roots except through punctured limits. -/
noncomputable def liouvilleRawNumerator
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ :=
  fun z =>
    affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z *
      (liouvilleChosenAffinePoint (H := H) z).val.2

/-- The removable global numerator used in the L2 proof.  Away from roots it is
`affCoeff · y`; at roots it is filled by the punctured filter limit. -/
noncomputable def liouvilleRemovableNumerator
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ :=
  fun z =>
    if H.f.eval z = 0 then
      Filter.limUnder (𝓝[≠] z) (liouvilleRawNumerator (H := H) form)
    else
      liouvilleRawNumerator (H := H) form z

@[simp] theorem liouvilleRemovableNumerator_of_eval_ne_zero
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) {z : ℂ}
    (hz : H.f.eval z ≠ 0) :
    liouvilleRemovableNumerator (H := H) form z =
      liouvilleRawNumerator (H := H) form z := by
  simp [liouvilleRemovableNumerator, hz]

/-- A bounded eventual ratio at infinity implies a global polynomial growth
bound.  This is the bounded-ratio variant of
`polynomial_growth_bound_of_tendsto_div_pow`. -/
theorem polynomial_growth_bound_of_eventually_norm_div_pow_le
    (G : ℂ → ℂ) (n : ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hGcont : Continuous G)
    (hBound : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖G z / z ^ n‖ ≤ R) :
    ∃ C : ℝ, ∀ z : ℂ, ‖G z‖ ≤ C * (1 + ‖z‖) ^ n := by
  classical
  rw [Filter.eventually_iff] at hBound
  rw [Filter.mem_cocompact] at hBound
  obtain ⟨K₀, hK₀, hK₀sub⟩ := hBound
  let K : Set ℂ := K₀ ∪ {0}
  have hK : IsCompact K := hK₀.union isCompact_singleton
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGcont.continuousOn
  let C : ℝ := max M R
  have hC_nonneg : 0 ≤ C := le_trans hR (le_max_right M R)
  refine ⟨C, ?_⟩
  intro z
  have hpow_one : (1 : ℝ) ≤ (1 + ‖z‖) ^ n :=
    one_le_pow₀ (by linarith [norm_nonneg z])
  by_cases hzK : z ∈ K
  · calc
      ‖G z‖ ≤ M := hM z hzK
      _ ≤ C := le_max_left M R
      _ ≤ C * (1 + ‖z‖) ^ n := by
        have := mul_le_mul_of_nonneg_left hpow_one hC_nonneg
        simpa using this
  · have hzK₀ : z ∉ K₀ := fun hz => hzK (Or.inl hz)
    have hz0 : z ≠ 0 := by
      intro hz
      apply hzK
      right
      simp [hz]
    have hratio : ‖G z / z ^ n‖ ≤ R := hK₀sub hzK₀
    have hzpow_ne : z ^ n ≠ 0 := pow_ne_zero n hz0
    have hnorm_pow_le : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) n
    calc
      ‖G z‖ = ‖(G z / z ^ n) * z ^ n‖ := by
        rw [div_mul_cancel₀ _ hzpow_ne]
      _ = ‖G z / z ^ n‖ * ‖z ^ n‖ := norm_mul _ _
      _ ≤ R * ‖z ^ n‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
      _ = R * ‖z‖ ^ n := by rw [norm_pow]
      _ ≤ C * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (le_max_right M R) (pow_nonneg (norm_nonneg z) n)
      _ ≤ C * (1 + ‖z‖) ^ n :=
        mul_le_mul_of_nonneg_left hnorm_pow_le hC_nonneg

/-- The raw numerator is analytic away from the branch locus.  Locally it is the
fixed chart numerator `affCoeff a₀ · y₀`; if the arbitrary algebraic sheet
switches, `affCoeff_chosen_anti_invariance` cancels the sign switch. -/
theorem liouvilleRawNumerator_analyticAt_of_eval_ne_zero
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleRawNumerator (H := H) form) z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  let e₀ := affineChartProjX (H := H) a₀ ha₀Y
  let q₀ : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀)
  have ha₀Src : a₀ ∈ e₀.source := by
    simpa [e₀] using affineChartProjX_mem_source (H := H) a₀ ha₀Y
  have hz₀Target : z₀ ∈ e₀.target := by
    have h := e₀.map_source ha₀Src
    simpa [e₀, a₀] using h
  have hSymm₀ : e₀.symm z₀ = a₀ := by
    have hMap : e₀ a₀ = a₀.val.1 := by rfl
    rw [show z₀ = a₀.val.1 by simp [a₀], ← hMap]
    exact e₀.left_inv ha₀Src
  have hProjCont₀ : ContinuousAt
      (fun z : ℂ =>
        Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H))) z₀ :=
    continuous_quotient_mk'.continuousAt.comp
      ((continuous_inl.continuousAt).comp (e₀.continuousAt_symm hz₀Target))
  have hPref₀ : ∀ᶠ z in 𝓝 z₀,
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ q₀ :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    have hqSrc : q₀ ∈ (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source q₀
    have hmem : (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source ∈ 𝓝 q₀ :=
      (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).open_source.mem_nhds hqSrc
    exact hProjCont₀.eventually (by simpa [q₀, hSymm₀] using hmem)
  have hEval : ∀ᶠ z in 𝓝 z₀, H.f.eval z ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz₀
  have hAnaAff : AnalyticAt ℂ (affCoeff (H := H) form a₀) z₀ := by
    simpa [a₀] using affCoeff_analyticAt_basepoint (H := H) form a₀ ha₀Y
  have hAnaY : AnalyticAt ℂ
      (fun z : ℂ =>
        (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) z₀ := by
    exact AnalyticOn.analyticAt (e₀.open_target.mem_nhds hz₀Target)
      (by
        simpa [e₀] using
          squareLocalHomeomorph_symm_eval_analyticOn (H := H) a₀ ha₀Y)
  have hModelAna : AnalyticAt ℂ
      (fun z : ℂ =>
        affCoeff (H := H) form a₀ z *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) z₀ :=
    hAnaAff.mul hAnaY
  have hEq : liouvilleRawNumerator (H := H) form =ᶠ[𝓝 z₀]
      fun z : ℂ =>
        affCoeff (H := H) form a₀ z *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) := by
    filter_upwards [e₀.open_target.mem_nhds hz₀Target, hPref₀, hEval]
      with z hzT hPref hzNZ
    let p₀ : HyperellipticAffine H := e₀.symm z
    have hzT' : z ∈ (affineChartProjX (H := H) a₀ ha₀Y).target := by
      simpa [e₀] using hzT
    have hp₀Fst : p₀.val.1 = z := by
      simpa [p₀, e₀] using affineChartProjX_symm_apply_fst
        (H := H) a₀ ha₀Y hzT'
    have hp₀Snd : p₀.val.2 =
        (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) := by
      simpa [p₀, e₀] using affineChartProjX_symm_apply_snd
        (H := H) a₀ ha₀Y hzT'
    have hFix₀ : affCoeff (H := H) form a₀ z =
        affCoeff (H := H) form p₀ z := by
      simpa [a₀, e₀, p₀, q₀] using
        affCoeff_eq_of_projX_symm (H := H) form a₀ ha₀Y hzT' hPref
    let ach := liouvilleChosenAffinePoint (H := H) z
    have haSq : ach.val.2 ^ 2 = H.f.eval z := by
      simpa [ach] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hp₀Sq : p₀.val.2 ^ 2 = H.f.eval z := by
      have hprop := p₀.property
      simpa [hp₀Fst] using hprop
    rcases eq_or_eq_neg_of_sq_eq_sq ach.val.2 p₀.val.2
        (haSq.trans hp₀Sq.symm) with hSame | hOpp
    · have ha_eq : ach = p₀ := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p₀, hp₀Fst]
        · exact hSame
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      rw [ha_eq, hp₀Snd, ← hFix₀]
    · have ha_eq : ach = p₀.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p₀, hp₀Fst, HyperellipticAffine.invol]
        · simpa [HyperellipticAffine.invol] using hOpp
      have hanti : affCoeff (H := H) form ach z =
          -affCoeff (H := H) form ach.invol z :=
        affCoeff_chosen_anti_invariance (H := H) form hzNZ
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      calc
        affCoeff (H := H) form ach z * ach.val.2 =
            (-affCoeff (H := H) form ach.invol z) * (-p₀.val.2) := by
          rw [hanti, hOpp]
        _ = affCoeff (H := H) form ach.invol z * p₀.val.2 := by ring
        _ = affCoeff (H := H) form a₀ z *
            (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) := by
          rw [ha_eq, HyperellipticAffine.invol_invol, ← hFix₀, hp₀Snd]
  exact hModelAna.congr hEq.symm

/-- Off-root analyticity of the removable numerator. -/
theorem liouvilleRemovableNumerator_analyticAt_off_roots
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleRemovableNumerator (H := H) form) z := by
  intro z hz
  exact (liouvilleRawNumerator_analyticAt_of_eval_ne_zero (H := H) form hz).congr
    (by
      have hEval : ∀ᶠ w in 𝓝 z, H.f.eval w ≠ 0 :=
        (Polynomial.continuous H.f).continuousAt.eventually_ne hz
      filter_upwards [hEval] with w hw
      exact (liouvilleRemovableNumerator_of_eval_ne_zero (H := H) form hw).symm)

/-- Finite branch limit for the raw numerator when `Quotient.out` uses the
affine branch chart. -/
theorem liouvilleRawNumerator_branch_tendsto_of_branch_out_inl
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0)
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀))) =
      Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀)) :
    ∃ L : ℂ,
      Filter.Tendsto (liouvilleRawNumerator (H := H) form) (𝓝[≠] z₀) (𝓝 L) := by
  classical
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let hpYn := liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  let N : ℂ → ℂ := liouvilleProjYNumerator (H := H) form p hpX q
  refine ⟨N 0, ?_⟩
  have hQq : Quotient.out q = Sum.inl p := by
    simpa [q, p] using hQ
  have hNcont : ContinuousAt N 0 := by
    have hAna : AnalyticAt ℂ N 0 := by
      simpa [N, p, hpX, q] using
        liouvilleBranchPoint_numerator_analyticAt_zero (H := H) form hz₀ q hQq
    exact hAna.continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hModel : Filter.Tendsto
      (fun z : ℂ => N (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 (N 0)) :=
    hNcont.tendsto.comp hyTendsto
  have hEq : liouvilleRawNumerator (H := H) form =ᶠ[𝓝[≠] z₀]
      fun z : ℂ => N (liouvilleChosenAffinePoint (H := H) z).val.2 := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in 𝓝 z₀, z ∈ e.source :=
      e.open_source.mem_nhds hz₀Src
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hSrcEv,
      eventually_eval_ne_zero_nhdsWithin (H := H) z₀] with z hzSrc hzNZ
    let y : ℂ := (liouvilleChosenAffinePoint (H := H) z).val.2
    have hySq : y ^ 2 = H.f.eval z := by
      simpa [y] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hyNZ : y ≠ 0 := by
      intro hy0
      apply hzNZ
      simpa [hy0] using hySq.symm
    have hyTarget : y ∈ (affineChartProjY (H := H) p hpX).target := by
      have hmap : H.f.eval z ∈ e.target := by
        have heq : (e : ℂ → ℂ) z = H.f.eval z := by
          simp [e, polynomialLocalHomeomorph]
        simpa [heq] using e.map_source hzSrc
      change y ^ 2 ∈ e.target
      rwa [hySq]
    have hxSymm : (affineChartProjY (H := H) p hpX).symm y =
        liouvilleChosenAffinePoint (H := H) z := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((affineChartProjY (H := H) p hpX).symm y).val.1 =
          (liouvilleChosenAffinePoint (H := H) z).val.1
        rw [hfst, hySq, hleft]
        rfl
      · change ((affineChartProjY (H := H) p hpX).symm y).val.2 =
          (liouvilleChosenAffinePoint (H := H) z).val.2
        simpa [y] using affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
    have hA :
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
          N y / y := by
      have h := affCoeff_eq_liouvilleProjYNumerator_div_of_branch
        (H := H) form p hpX hpYn q hQq hyTarget hyNZ
      simpa [N, y, hxSymm] using h
    unfold liouvilleRawNumerator
    rw [hA]
    change (N y / y) * y = N y
    field_simp [hyNZ]
  exact hModel.congr' hEq.symm

/-- Finite branch limit for the raw numerator when `Quotient.out` uses the
infinity-side branch chart. -/
theorem liouvilleRawNumerator_branch_tendsto_of_branch_out_inr
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀))) =
      Sum.inr b) :
    ∃ L : ℂ,
      Filter.Tendsto (liouvilleRawNumerator (H := H) form) (𝓝[≠] z₀) (𝓝 L) := by
  classical
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  obtain ⟨hz₀NZ, hb, hb0, hbX, hbYn⟩ :=
    liouvilleBranchPoint_out_inr_data (H := H) hz₀ hQ
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  let M : ℂ → ℂ := liouvilleInfinityProjYNumerator (H := H) form b hbX q
  refine ⟨-(z₀⁻¹) ^ 2 * z₀ ^ (H.f.natDegree / 2) * M 0, ?_⟩
  have hQq : Quotient.out q = Sum.inr b := by
    simpa [q, p] using hQ
  have hMcont : ContinuousAt M 0 := by
    have hAna : AnalyticAt ℂ M 0 := by
      simpa [M, q, Hrev] using
        liouvilleInfinityBranchPoint_numerator_analyticAt_zero
          (H := H) form b hbX hbYn hb0 q hQq
    exact hAna.continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hinvTendsto : Filter.Tendsto (fun z : ℂ => z⁻¹)
      (𝓝[≠] z₀) (𝓝 z₀⁻¹) :=
    (continuousAt_inv₀ hz₀NZ).tendsto.mono_left nhdsWithin_le_nhds
  have hvTendsto : Filter.Tendsto
      (fun z : ℂ =>
        (liouvilleChosenAffinePoint (H := H) z).val.2 *
          z⁻¹ ^ (H.f.natDegree / 2))
      (𝓝[≠] z₀) (𝓝 0) := by
    have hpow := hinvTendsto.pow (H.f.natDegree / 2)
    simpa using hyTendsto.mul hpow
  have hFactor : Filter.Tendsto
      (fun z : ℂ => -(z⁻¹) ^ 2 * z ^ (H.f.natDegree / 2))
      (𝓝[≠] z₀) (𝓝 (-(z₀⁻¹) ^ 2 * z₀ ^ (H.f.natDegree / 2))) := by
    exact (hinvTendsto.pow 2).neg.mul
      (((continuousAt_id' z₀).tendsto.mono_left nhdsWithin_le_nhds).pow _)
  have hMmodel : Filter.Tendsto
      (fun z : ℂ =>
        M ((liouvilleChosenAffinePoint (H := H) z).val.2 *
          z⁻¹ ^ (H.f.natDegree / 2)))
      (𝓝[≠] z₀) (𝓝 (M 0)) :=
    hMcont.tendsto.comp hvTendsto
  have hModel : Filter.Tendsto
      (fun z : ℂ =>
        (-(z⁻¹) ^ 2 * z ^ (H.f.natDegree / 2)) *
          M ((liouvilleChosenAffinePoint (H := H) z).val.2 *
            z⁻¹ ^ (H.f.natDegree / 2)))
      (𝓝[≠] z₀) (𝓝 (-(z₀⁻¹) ^ 2 * z₀ ^ (H.f.natDegree / 2) * M 0)) :=
    hFactor.mul hMmodel
  have hEq : liouvilleRawNumerator (H := H) form =ᶠ[𝓝[≠] z₀]
      fun z : ℂ =>
        (-(z⁻¹) ^ 2 * z ^ (H.f.natDegree / 2)) *
          M ((liouvilleChosenAffinePoint (H := H) z).val.2 *
            z⁻¹ ^ (H.f.natDegree / 2)) := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    let eInf := polynomialLocalHomeomorph (H := Hrev) b hbX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in 𝓝 z₀, z ∈ e.source :=
      e.open_source.mem_nhds hz₀Src
    have hu₀Src : z₀⁻¹ ∈ eInf.source := by
      have hbSrc : b ∈ (affineChartProjY (H := Hrev) b hbX).source :=
        affineChartProjY_mem_source (H := Hrev) b hbX
      change b.val.1 ∈ eInf.source at hbSrc
      have hb1 : b.val.1 = z₀⁻¹ := by
        simp [hb, liouvilleBranchPoint, affineGluingImage_val_fst]
      simpa [hb1] using hbSrc
    have hInvSrcEv : ∀ᶠ z in 𝓝 z₀, z⁻¹ ∈ eInf.source :=
      (continuousAt_inv₀ hz₀NZ).eventually (eInf.open_source.mem_nhds hu₀Src)
    have hZneEv : ∀ᶠ z in 𝓝 z₀, z ≠ 0 :=
      continuousAt_id.eventually_ne hz₀NZ
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hSrcEv,
      eventually_nhdsWithin_of_eventually_nhds hInvSrcEv,
      eventually_nhdsWithin_of_eventually_nhds hZneEv,
      eventually_eval_ne_zero_nhdsWithin (H := H) z₀] with z hzSrc hzInvSrc hzNZ hzEval
    let a : HyperellipticAffine H := liouvilleChosenAffinePoint (H := H) z
    let y : ℂ := a.val.2
    let v : ℂ := y * z⁻¹ ^ (H.f.natDegree / 2)
    have haY : a ∈ smoothLocusY H := by
      simpa [a] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzEval
    have hxA : a.val.1 ≠ 0 := by
      simpa [a] using hzNZ
    have hySq : y ^ 2 = H.f.eval z := by
      simpa [a, y] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hyNZ : y ≠ 0 := by
      intro hy0
      apply hzEval
      simpa [hy0] using hySq.symm
    have hvNZ : v ≠ 0 :=
      mul_ne_zero hyNZ (pow_ne_zero _ (inv_ne_zero hzNZ))
    have hvSq : v ^ 2 = (Polynomial.reverse H.f).eval z⁻¹ := by
      change (y * z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = _
      rw [mul_pow, hySq]
      have hpow_eq :
          (z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = z⁻¹ ^ H.f.natDegree := by
        rw [← pow_mul]
        congr 1
        have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
        obtain ⟨m, hm⟩ := heven
        omega
      rw [hpow_eq]
      exact (reverse_eval_inv_eq (H := H) z hzNZ).symm
    have hvTarget : v ∈ (affineChartProjY (H := Hrev) b hbX).target := by
      change v ^ 2 ∈ eInf.target
      rw [hvSq]
      have hmap : (eInf : ℂ → ℂ) z⁻¹ ∈ eInf.target := eInf.map_source hzInvSrc
      have hact : (eInf : ℂ → ℂ) z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹ := by
        change Hrev.f.eval z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹
        rfl
      simpa [hact] using hmap
    have hu_eq : eInf.symm (v ^ 2) = z⁻¹ := by
      have hleft := eInf.left_inv hzInvSrc
      have hact : (eInf : ℂ → ℂ) z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹ := by
        change Hrev.f.eval z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹
        rfl
      rw [hact] at hleft
      simpa [hvSq] using hleft
    have hBranchSymm : (infinityLiftChart H hf.out b).symm v =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) := by
      have hbv_eq : ((affineChartProjY (H := Hrev) b hbX).symm v :
          HyperellipticAffine Hrev) = affineGluingImage a hxA := by
        apply Subtype.ext
        apply Prod.ext
        · change (((affineChartProjY (H := Hrev) b hbX).symm v :
            HyperellipticAffine Hrev).val.1) = (affineGluingImage a hxA).val.1
          rw [affineChartProjY_symm_apply_fst (H := Hrev) b hbX hvTarget, hu_eq]
          simp [affineGluingImage_val_fst, a]
        · change (((affineChartProjY (H := Hrev) b hbX).symm v :
            HyperellipticAffine Hrev).val.2) = (affineGluingImage a hxA).val.2
          rw [affineChartProjY_symm_apply_snd (H := Hrev) b hbX hvTarget]
          simp [affineGluingImage_val_snd, v, y, a]
      change ((affineChartAt (H := Hrev) b).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).symm v =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
      rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn]
      change Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm v)) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
      rw [hbv_eq]
      exact (proj_eq_affineGluingImage (H := H) a hxA).symm
    have hA :
        affCoeff (H := H) form a z =
          - (z⁻¹) ^ 2 * (M v / v) := by
      have h := affCoeff_eq_liouvilleInfinityProjYNumerator_div_of_branch
        (H := H) form b hbX hbYn q hQq a haY hxA hvTarget hvNZ hBranchSymm
        (by simpa [a] using hu_eq)
      simpa [M, a] using h
    unfold liouvilleRawNumerator
    rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl]
    rw [hA]
    change - (z⁻¹) ^ 2 * (M v / v) * y =
      - (z⁻¹) ^ 2 * z ^ (H.f.natDegree / 2) * M v
    have hy_eq : y = v * z ^ (H.f.natDegree / 2) := by
      rw [show v = y * z⁻¹ ^ (H.f.natDegree / 2) from rfl]
      field_simp [hyNZ, hzNZ]
      rw [one_div, inv_pow]
      exact (inv_mul_cancel₀ (pow_ne_zero (H.f.natDegree / 2) hzNZ)).symm
    rw [hy_eq]
    field_simp [hvNZ]
  exact hModel.congr' hEq.symm

/-- Every branch point has a finite punctured limit for the raw numerator. -/
theorem liouvilleRawNumerator_branch_tendsto
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∀ z₀, H.f.eval z₀ = 0 →
      ∃ L, Filter.Tendsto (liouvilleRawNumerator (H := H) form) (𝓝[≠] z₀) (𝓝 L) := by
  intro z₀ hz₀
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  cases hQ : Quotient.out q with
  | inl a =>
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) = q := by
        rw [← hQ]
        exact Quotient.out_eq q
      have ha : a = p := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQp : Quotient.out q = Sum.inl p := by
        simpa [ha] using hQ
      exact liouvilleRawNumerator_branch_tendsto_of_branch_out_inl
        (H := H) form hz₀ (by simpa [q, p] using hQp)
  | inr b =>
      exact liouvilleRawNumerator_branch_tendsto_of_branch_out_inr
        (H := H) form hz₀ (b := b) (by simpa [q, p] using hQ)

/-- Continuity of the removable numerator. -/
theorem liouvilleRemovableNumerator_continuous
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    Continuous (liouvilleRemovableNumerator (H := H) form) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : H.f.eval z = 0
  · obtain ⟨L, hL⟩ := liouvilleRawNumerator_branch_tendsto (H := H) form z hz
    rw [continuousAt_iff_punctured_nhds]
    have hval : liouvilleRemovableNumerator (H := H) form z =
        Filter.limUnder (𝓝[≠] z) (liouvilleRawNumerator (H := H) form) := by
      rw [liouvilleRemovableNumerator, if_pos hz]
    rw [hval]
    have hToLim : Filter.Tendsto (liouvilleRawNumerator (H := H) form)
        (𝓝[≠] z)
        (𝓝 (Filter.limUnder (𝓝[≠] z) (liouvilleRawNumerator (H := H) form))) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    exact hToLim.congr'
      (by
        filter_upwards [eventually_eval_ne_zero_nhdsWithin (H := H) z] with w hw
        exact (liouvilleRemovableNumerator_of_eval_ne_zero (H := H) form hw).symm)
  · exact (liouvilleRemovableNumerator_analyticAt_off_roots
      (H := H) form z hz).continuousAt

/-- Differentiability of the removable global numerator. -/
theorem liouvilleRemovableNumerator_differentiable
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    Differentiable ℂ (liouvilleRemovableNumerator (H := H) form) :=
  differentiable_of_analyticAt_off_roots (H := H)
    (liouvilleRemovableNumerator (H := H) form)
    (liouvilleRemovableNumerator_analyticAt_off_roots (H := H) form)
    (liouvilleRemovableNumerator_continuous (H := H) form)

/-- At infinity, the removable numerator divided by `z^(N/2-2)` is eventually
bounded.  The two possible sheets are handled by the two infinity charts; the
scaled sheet coordinate has bounded norm because its square is
`(reverse H.f)(z⁻¹)`. -/
theorem liouvilleRemovableNumerator_eventually_norm_div_pow_le
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ z : ℂ in Filter.cocompact ℂ,
        ‖liouvilleRemovableNumerator (H := H) form z /
            z ^ (H.f.natDegree / 2 - 2)‖ ≤ R := by
  classical
  let m : ℕ := H.f.natDegree / 2
  let n : ℕ := m - 2
  let bPlus := liouvilleInfinityPointPos H
  let bMinus := liouvilleInfinityPointNeg H
  let qPlus : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bPlus)
  let qMinus : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bMinus)
  have hbPlusY : bPlus ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
    simpa [bPlus] using liouvilleInfinityPointPos_mem_smoothLocusY (H := H)
  have hbMinusY : bMinus ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
    simpa [bMinus] using liouvilleInfinityPointNeg_mem_smoothLocusY (H := H)
  have hQPlus : Quotient.out qPlus = Sum.inr bPlus := by
    simpa [qPlus, bPlus] using quotient_out_liouvilleInfinityPointPos (H := H)
  have hQMinus : Quotient.out qMinus = Sum.inr bMinus := by
    simpa [qMinus, bMinus] using quotient_out_liouvilleInfinityPointNeg (H := H)
  have hPlusAna : AnalyticAt ℂ (form.coeff qPlus) 0 := by
    simpa [qPlus, bPlus] using
      form_coeff_analyticAt_infinity_zero (H := H) form bPlus hbPlusY
        (by simp [bPlus, liouvilleInfinityPointPos]) qPlus hQPlus
  have hMinusAna : AnalyticAt ℂ (form.coeff qMinus) 0 := by
    simpa [qMinus, bMinus] using
      form_coeff_analyticAt_infinity_zero (H := H) form bMinus hbMinusY
        (by simp [bMinus, liouvilleInfinityPointNeg]) qMinus hQMinus
  let B : ℝ := max (‖form.coeff qPlus 0‖ + 1) (‖form.coeff qMinus 0‖ + 1)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hPlusBound : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖form.coeff qPlus z⁻¹‖ ≤ B := by
    have hPlus : Filter.Tendsto (fun z : ℂ => form.coeff qPlus z⁻¹)
        (Filter.cocompact ℂ) (𝓝 (form.coeff qPlus 0)) :=
      hPlusAna.continuousAt.tendsto.comp tendsto_inv_cocompact_zero
    have hmem := hPlus (Metric.closedBall_mem_nhds (form.coeff qPlus 0) zero_lt_one)
    filter_upwards [hmem] with z hz
    have hdist : dist (form.coeff qPlus z⁻¹) (form.coeff qPlus 0) ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    calc
      ‖form.coeff qPlus z⁻¹‖ = dist (form.coeff qPlus z⁻¹) 0 := by
        rw [dist_zero_right]
      _ ≤ dist (form.coeff qPlus z⁻¹) (form.coeff qPlus 0) +
          dist (form.coeff qPlus 0) 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖form.coeff qPlus 0‖ := by
        rw [dist_zero_right]
        linarith
      _ = ‖form.coeff qPlus 0‖ + 1 := by ring
      _ ≤ B := le_max_left _ _
  have hMinusBound : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖form.coeff qMinus z⁻¹‖ ≤ B := by
    have hMinus : Filter.Tendsto (fun z : ℂ => form.coeff qMinus z⁻¹)
        (Filter.cocompact ℂ) (𝓝 (form.coeff qMinus 0)) :=
      hMinusAna.continuousAt.tendsto.comp tendsto_inv_cocompact_zero
    have hmem := hMinus (Metric.closedBall_mem_nhds (form.coeff qMinus 0) zero_lt_one)
    filter_upwards [hmem] with z hz
    have hdist : dist (form.coeff qMinus z⁻¹) (form.coeff qMinus 0) ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    calc
      ‖form.coeff qMinus z⁻¹‖ = dist (form.coeff qMinus z⁻¹) 0 := by
        rw [dist_zero_right]
      _ ≤ dist (form.coeff qMinus z⁻¹) (form.coeff qMinus 0) +
          dist (form.coeff qMinus 0) 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖form.coeff qMinus 0‖ := by
        rw [dist_zero_right]
        linarith
      _ = ‖form.coeff qMinus 0‖ + 1 := by ring
      _ ≤ B := le_max_right _ _
  let c : ℂ := liouvilleInfinitySqrt H
  let V : ℝ := ‖c ^ 2‖ + 2
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hrev : Filter.Tendsto (fun z : ℂ => (Polynomial.reverse H.f).eval z⁻¹)
      (Filter.cocompact ℂ) (𝓝 (c ^ 2)) := by
    have hcont : Filter.Tendsto
        (fun u : ℂ => (Polynomial.reverse H.f).eval u)
        (𝓝 0) (𝓝 ((Polynomial.reverse H.f).eval 0)) :=
      (Polynomial.continuous (Polynomial.reverse H.f)).continuousAt
    have h := hcont.comp tendsto_inv_cocompact_zero
    simpa [c, reverse_eval_zero_eq_leadingCoeff (H := H),
      liouvilleInfinitySqrt_sq H] using h
  have hrevNormBound : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖(Polynomial.reverse H.f).eval z⁻¹‖ ≤ ‖c ^ 2‖ + 1 := by
    have hnorm := hrev.norm
    have hmem := hnorm (Metric.closedBall_mem_nhds ‖c ^ 2‖ zero_lt_one)
    filter_upwards [hmem] with z hz
    have hdist : dist ‖(Polynomial.reverse H.f).eval z⁻¹‖ ‖c ^ 2‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    rw [Real.dist_eq] at hdist
    have habs := abs_le.mp hdist
    linarith
  let R : ℝ := B * V
  refine ⟨R, mul_nonneg hB_nonneg hV_nonneg, ?_⟩
  have hm_ge_two : 2 ≤ m := by
    simpa [m] using even_natDegree_div_two_ge_two (H := H)
  have hm_eq : n + 2 = m := by
    dsimp [n]
    exact Nat.sub_add_cancel hm_ge_two
  filter_upwards [liouvilleChosenAffinePoint_infinity_sources_eventually_cocompact
      (H := H), hPlusBound, hMinusBound, hrevNormBound]
    with z hzPack hPlusB hMinusB hRevB
  rcases hzPack with ⟨hz0, hzEval, hsrcCases⟩
  let a := liouvilleChosenAffinePoint (H := H) z
  let y : ℂ := a.val.2
  let v : ℂ := y * z⁻¹ ^ m
  have haY : a ∈ smoothLocusY H := by
    simpa [a] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzEval
  have hySq : y ^ 2 = H.f.eval z := by
    simpa [a, y] using liouvilleChosenAffinePoint_snd_sq (H := H) z
  have hvSq : v ^ 2 = (Polynomial.reverse H.f).eval z⁻¹ := by
    change (y * z⁻¹ ^ m) ^ 2 = _
    rw [mul_pow, hySq]
    have hpow_eq : (z⁻¹ ^ m) ^ 2 = z⁻¹ ^ H.f.natDegree := by
      rw [← pow_mul]
      congr 1
      dsimp [m]
      have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
      obtain ⟨k, hk⟩ := heven
      omega
    rw [hpow_eq]
    exact (reverse_eval_inv_eq (H := H) z hz0).symm
  have hvBound : ‖v‖ ≤ V := by
    have hvnormsq : ‖v‖ ^ 2 = ‖(Polynomial.reverse H.f).eval z⁻¹‖ := by
      rw [← norm_pow, hvSq]
    have hsqle : ‖v‖ ^ 2 ≤ ‖c ^ 2‖ + 1 := by
      simpa [hvnormsq] using hRevB
    have hvnonneg : 0 ≤ ‖v‖ := norm_nonneg v
    dsimp [V]
    nlinarith [hsqle, hvnonneg, norm_nonneg (c ^ 2)]
  have hRem : liouvilleRemovableNumerator (H := H) form z =
      liouvilleRawNumerator (H := H) form z :=
    liouvilleRemovableNumerator_of_eval_ne_zero (H := H) form hzEval
  rcases hsrcCases with hPlusMinus | hMinusPlus
  · have hA : affCoeff (H := H) form a z =
        form.coeff qPlus z⁻¹ * (-1 / z ^ 2) := by
      have h := affCoeff_eq_fixed_infinity_of_source
        (H := H) form a haY bPlus hbPlusY hQPlus hPlusMinus.1
      simpa [a, qPlus] using h
    have hratio : liouvilleRemovableNumerator (H := H) form z / z ^ n =
        -form.coeff qPlus z⁻¹ * v := by
      rw [hRem]
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl, hA]
      change (form.coeff qPlus z⁻¹ * (-1 / z ^ 2) * y) / z ^ n =
        -form.coeff qPlus z⁻¹ * v
      rw [show v = y * z⁻¹ ^ m from rfl]
      field_simp [hz0]
      have hpow_cancel : z ^ 2 * (z ^ n * (1 / z) ^ m) = 1 := by
        have h2n : 2 + n = m := by omega
        rw [← mul_assoc, ← pow_add, h2n, one_div, inv_pow]
        exact mul_inv_cancel₀ (pow_ne_zero m hz0)
      rw [show z ^ 2 * form.coeff qPlus (1 / z) * y * z ^ n * (1 / z) ^ m =
          form.coeff qPlus (1 / z) * y * (z ^ 2 * (z ^ n * (1 / z) ^ m)) by
        ring]
      rw [hpow_cancel]
      ring
    rw [hratio]
    calc
      ‖-form.coeff qPlus z⁻¹ * v‖ =
          ‖form.coeff qPlus z⁻¹‖ * ‖v‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ B * V := mul_le_mul hPlusB hvBound (norm_nonneg v) hB_nonneg
  · have hA : affCoeff (H := H) form a z =
        form.coeff qMinus z⁻¹ * (-1 / z ^ 2) := by
      have h := affCoeff_eq_fixed_infinity_of_source
        (H := H) form a haY bMinus hbMinusY hQMinus hMinusPlus.1
      simpa [a, qMinus] using h
    have hratio : liouvilleRemovableNumerator (H := H) form z / z ^ n =
        -form.coeff qMinus z⁻¹ * v := by
      rw [hRem]
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl, hA]
      change (form.coeff qMinus z⁻¹ * (-1 / z ^ 2) * y) / z ^ n =
        -form.coeff qMinus z⁻¹ * v
      rw [show v = y * z⁻¹ ^ m from rfl]
      field_simp [hz0]
      have hpow_cancel : z ^ 2 * (z ^ n * (1 / z) ^ m) = 1 := by
        have h2n : 2 + n = m := by omega
        rw [← mul_assoc, ← pow_add, h2n, one_div, inv_pow]
        exact mul_inv_cancel₀ (pow_ne_zero m hz0)
      rw [show z ^ 2 * form.coeff qMinus (1 / z) * y * z ^ n * (1 / z) ^ m =
          form.coeff qMinus (1 / z) * y * (z ^ 2 * (z ^ n * (1 / z) ^ m)) by
        ring]
      rw [hpow_cancel]
      ring
    rw [hratio]
    calc
      ‖-form.coeff qMinus z⁻¹ * v‖ =
          ‖form.coeff qMinus z⁻¹‖ * ‖v‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ B * V := mul_le_mul hMinusB hvBound (norm_nonneg v) hB_nonneg

/-- Read out every smooth-`Y` projX coefficient from the removable global
numerator. -/
theorem liouvilleRemovableNumerator_readout
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        liouvilleRemovableNumerator (H := H) form z /
          (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  classical
  intro a hpY q hQ z hz
  set y := (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) with hy_def
  let p : HyperellipticAffine H := (affineChartProjX (H := H) a hpY).symm z
  have hp_source : p ∈ (affineChartProjX (H := H) a hpY).source := by
    simpa [p] using (affineChartProjX (H := H) a hpY).map_target hz
  have hp_fst : p.val.1 = z := by
    simpa [p] using affineChartProjX_symm_apply_fst (H := H) a hpY hz
  have hp_snd : p.val.2 = y := by
    simpa [p, y, hy_def] using affineChartProjX_symm_apply_snd (H := H) a hpY hz
  have hy_ne : y ≠ 0 := by
    simpa [y] using squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
  have hy_sq : y ^ 2 = H.f.eval z := by
    have hp := p.property
    simpa [hp_fst, hp_snd] using hp
  have hz_eval : H.f.eval z ≠ 0 := by
    intro hzero
    have hy_zero : y = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using hy_sq)
    exact hy_ne hy_zero
  let q0 : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  have hq_eq : q = q0 := by
    have hOut : Quotient.mk (hyperellipticEvenSetoid H) (Quotient.out q) = q :=
      Quotient.out_eq q
    rw [hQ] at hOut
    simpa [q0] using hOut.symm
  have hQ0 : Quotient.out q0 = Sum.inl a := by
    simpa [← hq_eq] using hQ
  have hCoeffAff : affCoeff (H := H) form a z = form.coeff q z := by
    have hAff := affCoeff_of_inl (H := H) form a a hQ0
    have hAffEval : affCoeff (H := H) form a z = form.coeff q0 z := by
      simpa [q0] using congrFun hAff z
    simpa [hq_eq] using hAffEval
  have hPrefSrc :
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p) ∈
        (_root_.chartAt ℂ q0 :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    change Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p) ∈
      (HyperellipticEvenProj.chartAt H hf.out q0).source
    unfold HyperellipticEvenProj.chartAt
    rw [hQ0]
    change Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p) ∈
      (affineLiftChart H hf.out a).source
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨p, ?_, rfl⟩
    simpa [affineChartAt_of_mem_smoothLocusY (H := H) a hpY] using hp_source
  have hAff_a_p : affCoeff (H := H) form a z = affCoeff (H := H) form p z := by
    simpa [p, q0] using affCoeff_eq_of_projX_symm (H := H) form a hpY hz hPrefSrc
  let ach := liouvilleChosenAffinePoint (H := H) z
  have hachY : ach ∈ smoothLocusY H := by
    simpa [ach] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz_eval
  have hach_sq : ach.val.2 ^ 2 = y ^ 2 := by
    rw [liouvilleChosenAffinePoint_snd_sq (H := H) z, hy_sq]
  have hRem : liouvilleRemovableNumerator (H := H) form z =
      liouvilleRawNumerator (H := H) form z :=
    liouvilleRemovableNumerator_of_eval_ne_zero (H := H) form hz_eval
  have hNumerator : liouvilleRemovableNumerator (H := H) form z =
      form.coeff q z * y := by
    rw [hRem]
    rcases eq_or_eq_neg_of_sq_eq_sq ach.val.2 y hach_sq with hsame | hneg
    · have hach_eq : ach = p := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p, hp_fst]
        · simpa [ach, hp_snd] using hsame
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      rw [hach_eq, hp_snd, ← hAff_a_p, hCoeffAff]
    · have hach_eq : ach = p.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p, hp_fst, HyperellipticAffine.invol]
        · simpa [ach, hp_snd, HyperellipticAffine.invol] using hneg
      have hanti : affCoeff (H := H) form ach z =
          -affCoeff (H := H) form ach.invol z :=
        affCoeff_chosen_anti_invariance (H := H) form hz_eval
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      calc
        affCoeff (H := H) form ach z * ach.val.2 =
            (-affCoeff (H := H) form ach.invol z) * (-y) := by
          rw [hanti, hneg]
        _ = affCoeff (H := H) form ach.invol z * y := by ring
        _ = form.coeff q z * y := by
          rw [hach_eq, HyperellipticAffine.invol_invol, ← hAff_a_p, hCoeffAff]
  rw [hNumerator]
  field_simp [hy_ne]

theorem AX_HyperellipticForm_polynomial_decomposition
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
        (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
        {z : ℂ}
        (_hz : z ∈ ((HyperellipticAffine.affineChartProjX a hpY) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target),
        form.coeff q z =
          g.eval z /
            (HyperellipticAffine.squareLocalHomeomorph (H := H) a hpY).symm
              (H.f.eval z) := by
  classical
  obtain ⟨R, hR, hBound⟩ :=
    liouvilleRemovableNumerator_eventually_norm_div_pow_le (H := H) form
  obtain ⟨C, hC⟩ :=
    polynomial_growth_bound_of_eventually_norm_div_pow_le
      (liouvilleRemovableNumerator (H := H) form)
      (H.f.natDegree / 2 - 2) R hR
      (liouvilleRemovableNumerator_differentiable (H := H) form).continuous
      hBound
  exact polynomial_decomposition_of_entire_growth (H := H) form
    (liouvilleRemovableNumerator (H := H) form)
    (liouvilleRemovableNumerator_differentiable (H := H) form)
    C hC
    (liouvilleRemovableNumerator_readout (H := H) form)

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
