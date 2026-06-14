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

import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Form
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Submission.Jacobians.RiemannSurface
import Submission.Jacobians.RiemannSurface.OneForm
import Submission.Jacobians.Bridge.KirovHolomorphic
import Submission.Jacobians.GeneralResults.EntireGrowth
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
      change f x = f p₀
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

/-- Smooth-`Y` chart-target part of L3. The public L2 theorem gives
agreement with the canonical `hyperellipticForm` on projX chart targets;
this wrapper rewrites the preferred `extChartAt` target in the
`Quotient.out = Sum.inl a`, `a ∈ smoothLocusY` case. -/
theorem coeff_eq_hyperellipticForm_on_smoothY_extChartTarget
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (hDecomp : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
    {q : HyperellipticEvenProj H} {z : ℂ}
    {a : HyperellipticAffine H}
    (hQ : Quotient.out q = Sum.inl a) (hpY : a ∈ smoothLocusY H)
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target) :
    form.coeff q z =
      (HyperellipticEvenProj.hyperellipticForm H g).coeff q z := by
  have hzX : z ∈ (affineChartProjX (H := H) a hpY).target := by
    have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
        (affineChartProjX (H := H) a hpY).target := by
      rw [extChartAt_target]
      change ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (affineChartProjX (H := H) a hpY).target
      change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range (id : ℂ → ℂ) =
        (affineChartProjX (H := H) a hpY).target
      rw [Set.range_id, Set.inter_univ]
      unfold HyperellipticEvenProj.chartAt
      rw [hQ]
      simp [HyperellipticEvenProj.affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_target, affineChartAt, hpY]
    rw [hExt] at hz
    exact hz
  exact coeff_eq_hyperellipticForm_on_projX_of_decomposition
    (H := H) form hDeg hDecomp a hpY q hQ hzX

/-- If the removable Liouville numerator of a form is the polynomial `g`,
then the invariant affine `x`-coefficient at every smooth affine point is
`g(x) / y`. This version does not depend on which representative
`Quotient.out` chooses for the affine point. -/
theorem affCoeff_eq_polynomial_div_of_removable_eq
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {g : Polynomial ℂ}
    (hgEval : ∀ z : ℂ, liouvilleRemovableNumerator (H := H) form z = g.eval z)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H) :
    affCoeff (H := H) form a a.val.1 = g.eval a.val.1 / a.val.2 := by
  classical
  have hxEval : H.f.eval a.val.1 ≠ 0 := by
    intro hzero
    have hy_sq : a.val.2 ^ 2 = H.f.eval a.val.1 := by
      simpa using a.property
    have hy_zero : a.val.2 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using hy_sq)
    exact hpY hy_zero
  have hRem : liouvilleRemovableNumerator (H := H) form a.val.1 =
      liouvilleRawNumerator (H := H) form a.val.1 :=
    liouvilleRemovableNumerator_of_eval_ne_zero (H := H) form hxEval
  let ach := liouvilleChosenAffinePoint (H := H) a.val.1
  have hach_sq : ach.val.2 ^ 2 = a.val.2 ^ 2 := by
    rw [liouvilleChosenAffinePoint_snd_sq (H := H) a.val.1]
    simpa using a.property.symm
  have hNumerator :
      liouvilleRemovableNumerator (H := H) form a.val.1 =
        affCoeff (H := H) form a a.val.1 * a.val.2 := by
    rw [hRem]
    rcases eq_or_eq_neg_of_sq_eq_sq ach.val.2 a.val.2 hach_sq with hsame | hneg
    · have hach_eq : ach = a := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach]
        · exact hsame
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) a.val.1 = ach from rfl]
      rw [hach_eq]
    · have hach_eq : ach = a.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, HyperellipticAffine.invol]
        · simpa [HyperellipticAffine.invol] using hneg
      have hanti : affCoeff (H := H) form ach a.val.1 =
          -affCoeff (H := H) form ach.invol a.val.1 :=
        affCoeff_chosen_anti_invariance (H := H) form hxEval
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) a.val.1 = ach from rfl]
      calc
        affCoeff (H := H) form ach a.val.1 * ach.val.2 =
            (-affCoeff (H := H) form ach.invol a.val.1) * (-a.val.2) := by
          rw [hanti, hneg]
        _ = affCoeff (H := H) form ach.invol a.val.1 * a.val.2 := by ring
        _ = affCoeff (H := H) form a a.val.1 * a.val.2 := by
          rw [hach_eq, HyperellipticAffine.invol_invol]
  have hmul : affCoeff (H := H) form a a.val.1 * a.val.2 = g.eval a.val.1 := by
    rw [← hgEval a.val.1, hNumerator]
  rw [eq_div_iff hpY]
  exact hmul

/-- Inverse of the affine-to-infinity gluing map on the overlap `u ≠ 0`.
For an infinity-side point `(u, v)`, this is `(x, y) = (u⁻¹, v u⁻N)`,
where `N = H.f.natDegree / 2`. -/
noncomputable def affineUngluingImage
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (b : HyperellipticAffineInfinity H) (hu : b.val.1 ≠ 0) :
    HyperellipticAffine H :=
  ⟨(b.val.1⁻¹, b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)), by
    classical
    let u : ℂ := b.val.1
    let v : ℂ := b.val.2
    have hu' : u ≠ 0 := by simpa [u] using hu
    have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
    obtain ⟨m, hm⟩ := heven
    have hN : H.f.natDegree / 2 = m := by omega
    have hpow : (u⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = u⁻¹ ^ H.f.natDegree := by
      rw [hN, ← pow_mul]
      congr 1
      omega
    have hrev :
        (Polynomial.reverse H.f).eval u =
          H.f.eval u⁻¹ * u ^ H.f.natDegree := by
      have h := reverse_eval_inv_eq (H := H) u⁻¹ (inv_ne_zero hu')
      simpa [inv_inv] using h
    have hv : v ^ 2 = (Polynomial.reverse H.f).eval u := by
      simpa [u, v] using b.property
    calc
      (v * u⁻¹ ^ (H.f.natDegree / 2)) ^ 2 =
          v ^ 2 * u⁻¹ ^ H.f.natDegree := by
        rw [mul_pow, hpow]
      _ = (Polynomial.reverse H.f).eval u * u⁻¹ ^ H.f.natDegree := by
        rw [hv]
      _ = (H.f.eval u⁻¹ * u ^ H.f.natDegree) * u⁻¹ ^ H.f.natDegree := by
        rw [hrev]
      _ = H.f.eval u⁻¹ := by
        calc
          (H.f.eval u⁻¹ * u ^ H.f.natDegree) * u⁻¹ ^ H.f.natDegree =
              H.f.eval u⁻¹ * (u ^ H.f.natDegree * u⁻¹ ^ H.f.natDegree) := by ring
          _ = H.f.eval u⁻¹ * ((u * u⁻¹) ^ H.f.natDegree) := by
            rw [← mul_pow]
          _ = H.f.eval u⁻¹ := by
            simp [hu']⟩

@[simp] theorem affineUngluingImage_val_fst
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (b : HyperellipticAffineInfinity H) (hu : b.val.1 ≠ 0) :
    (affineUngluingImage (H := H) b hu).val.1 = b.val.1⁻¹ := rfl

@[simp] theorem affineUngluingImage_val_snd
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (b : HyperellipticAffineInfinity H) (hu : b.val.1 ≠ 0) :
    (affineUngluingImage (H := H) b hu).val.2 =
      b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2) := rfl

theorem affineUngluingImage_mem_smoothLocusY
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (b : HyperellipticAffineInfinity H)
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hu : b.val.1 ≠ 0) :
    affineUngluingImage (H := H) b hu ∈ smoothLocusY H := by
  change (affineUngluingImage (H := H) b hu).val.2 ≠ 0
  rw [affineUngluingImage_val_snd]
  exact mul_ne_zero hbY (pow_ne_zero _ (inv_ne_zero hu))

theorem affineGluingImage_affineUngluingImage
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (b : HyperellipticAffineInfinity H) (hu : b.val.1 ≠ 0) :
    affineGluingImage
        (affineUngluingImage (H := H) b hu)
        (by simpa [affineUngluingImage] using inv_ne_zero hu) = b := by
  apply Subtype.ext
  apply Prod.ext
  · simp [affineGluingImage_val_fst]
  · change
      (b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)) *
          ((b.val.1⁻¹)⁻¹) ^ (H.f.natDegree / 2) = b.val.2
    rw [inv_inv]
    calc
      (b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)) *
          b.val.1 ^ (H.f.natDegree / 2) =
          b.val.2 *
            (b.val.1⁻¹ ^ (H.f.natDegree / 2) *
              b.val.1 ^ (H.f.natDegree / 2)) := by ring
      _ = b.val.2 * ((b.val.1⁻¹ * b.val.1) ^ (H.f.natDegree / 2)) := by
        rw [← mul_pow]
      _ = b.val.2 := by
        simp [hu]

/-- Sanity check in the infinity branch coordinate: for the canonical form
`hyperellipticForm H g`, the cancelled reverse-branch numerator is
`(infReverse H g)(u(v))`. -/
theorem liouvilleInfinityProjYNumerator_hyperellipticForm_eq
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    {g : Polynomial ℂ} (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (b : HyperellipticAffineInfinity H)
    (hbX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hbYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b)
    {v : ℂ}
    (hv : v ∈
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).target) :
    liouvilleInfinityProjYNumerator (H := H)
        (HyperellipticEvenProj.hyperellipticForm H g) b hbX q v =
      (infReverse H g).eval
        ((polynomialLocalHomeomorph
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) := by
  unfold liouvilleInfinityProjYNumerator
  rw [HyperellipticEvenProj.hyperellipticForm_coeff_of_lt H hDeg]
  change (hyperellipticEvenCoeff (H := H) g (infReverse H g)) q v *
      ((Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
        2) =
    (infReverse H g).eval
      ((polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2))
  change (match Quotient.out q with
    | Sum.inl a => hyperellipticAffineCoeff (H := H) g a
    | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g) b) v *
      ((Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
        2) =
    (infReverse H g).eval
      ((polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2))
  rw [hQ]
  change hyperellipticAffineInfinityCoeff (H := H) (infReverse H g) b v *
      ((Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
        2) =
    (infReverse H g).eval
      ((polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2))
  change hyperellipticAffineCoeff
      (H := HyperellipticAffineInfinity.reverseData H hf.out) (infReverse H g) b v *
      ((Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
        2) =
    (infReverse H g).eval
      ((polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2))
  rw [hyperellipticAffineCoeff]
  split_ifs with hbY
  · exact False.elim (hbYn hbY)
  · rw [affineProjYCoeff_eq_on_target
      (H := HyperellipticAffineInfinity.reverseData H hf.out) (infReverse H g) b hbX hv]
    change 2 *
          (infReverse H g).eval
            ((polynomialLocalHomeomorph
              (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
          (Polynomial.reverse H.f).derivative.eval
            ((polynomialLocalHomeomorph
              (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) *
          ((Polynomial.reverse H.f).derivative.eval
              ((polynomialLocalHomeomorph
                (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) /
            2) =
        (infReverse H g).eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2))
    have hFne :
        (Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2)) ≠ 0 :=
      polynomialLocalHomeomorph_symm_eval_derivative_ne_zero
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX hv
    field_simp [hFne]

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
theorem AX_HyperellipticOneForm_eq_form
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      form = HyperellipticEvenProj.hyperellipticForm H g := by
  classical
  obtain ⟨R, hR, hBound⟩ :=
    liouvilleRemovableNumerator_eventually_norm_div_pow_le (H := H) form
  obtain ⟨C, hC⟩ :=
    polynomial_growth_bound_of_eventually_norm_div_pow_le
      (liouvilleRemovableNumerator (H := H) form)
      (H.f.natDegree / 2 - 2) R hR
      (liouvilleRemovableNumerator_differentiable (H := H) form).continuous
      hBound
  obtain ⟨g, hgDeg, hgEval⟩ :=
    Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth
      (H.f.natDegree / 2 - 2)
      (liouvilleRemovableNumerator (H := H) form)
      (liouvilleRemovableNumerator_differentiable (H := H) form)
      C hC
  have hDeg : g.natDegree < H.f.natDegree / 2 - 1 := by
    have htwo : 2 ≤ H.f.natDegree / 2 := even_natDegree_div_two_ge_two (H := H)
    omega
  have hDecomp : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
    intro a hpY q hQ z hz
    rw [← hgEval z]
    exact liouvilleRemovableNumerator_readout (H := H) form a hpY q hQ hz
  refine ⟨g, hDeg, ?_⟩
  refine oneForm_eq_hyperellipticForm_of_eqOn_chartTarget (H := H) form g ?_
  intro q z hz
  rcases hQ : Quotient.out q with a | b
  · by_cases hpY : a ∈ smoothLocusY H
    · exact coeff_eq_hyperellipticForm_on_smoothY_extChartTarget
        (H := H) form hDeg hDecomp hQ hpY hz
    · have hpX : a ∈ smoothLocusX H :=
        mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)
      have hzY : z ∈ (affineChartProjY (H := H) a hpX).target := by
        have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
            (affineChartProjY (H := H) a hpX).target := by
          rw [extChartAt_target]
          change ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range ↑𝓘(ℂ, ℂ) =
            (affineChartProjY (H := H) a hpX).target
          change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range (id : ℂ → ℂ) =
            (affineChartProjY (H := H) a hpX).target
          rw [Set.range_id, Set.inter_univ]
          unfold HyperellipticEvenProj.chartAt
          rw [hQ]
          simp [HyperellipticEvenProj.affineLiftChart,
            OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := H) a hpY]
        rwa [hExt] at hz
      have hPunct : ∀ {w : ℂ},
          w ∈ (affineChartProjY (H := H) a hpX).target →
          w ≠ 0 →
          form.coeff q w =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q w := by
        intro w hw hwne
        let p : HyperellipticAffine H := (affineChartProjY (H := H) a hpX).symm w
        have hpYp : p ∈ smoothLocusY H := by
          change p.val.2 ≠ 0
          have hsnd := affineChartProjY_symm_apply_snd (H := H) a hpX hw
          simpa [p, hsnd] using hwne
        have hp_snd : p.val.2 = w := by
          simpa [p] using affineChartProjY_symm_apply_snd (H := H) a hpX hw
        have hp_fst :
            p.val.1 = (polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2) := by
          simpa [p] using affineChartProjY_symm_apply_fst (H := H) a hpX hw
        have hAff :
            affCoeff (H := H) form p p.val.1 = g.eval p.val.1 / p.val.2 :=
          affCoeff_eq_polynomial_div_of_removable_eq
            (H := H) form hgEval p hpYp
        have hBranch :
            affCoeff (H := H) form p p.val.1 =
              liouvilleProjYNumerator (H := H) form a hpX q w / w := by
          simpa [p] using
            affCoeff_eq_liouvilleProjYNumerator_div_of_branch
              (H := H) form a hpX hpY q hQ hw hwne
        have hNum :
            liouvilleProjYNumerator (H := H) form a hpX q w =
              g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) := by
          have hdiv : g.eval p.val.1 / p.val.2 =
              liouvilleProjYNumerator (H := H) form a hpX q w / w :=
            hAff.symm.trans hBranch
          rw [hp_snd, hp_fst] at hdiv
          field_simp [hwne] at hdiv
          exact hdiv.symm
        have hNumCan :
            liouvilleProjYNumerator (H := H)
                (HyperellipticEvenProj.hyperellipticForm H g) a hpX q w =
              g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) :=
          liouvilleProjYNumerator_hyperellipticForm_eq
            (H := H) hDeg a hpX hpY q hQ hw
        have hNumEq :
            liouvilleProjYNumerator (H := H) form a hpX q w =
              liouvilleProjYNumerator (H := H)
                (HyperellipticEvenProj.hyperellipticForm H g) a hpX q w := by
          rw [hNum, hNumCan]
        unfold liouvilleProjYNumerator at hNumEq
        have hFne :
            H.f.derivative.eval
              ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) ≠ 0 :=
          polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) a hpX hw
        field_simp [hFne] at hNumEq
        exact hNumEq
      by_cases hz0 : z = 0
      · have h0Y : (0 : ℂ) ∈ (affineChartProjY (H := H) a hpX).target := by
          simpa [hz0] using hzY
        have hContForm : ContinuousAt (form.coeff q) 0 := by
          exact (AnalyticOn.analyticAt
            ((affineChartProjY (H := H) a hpX).open_target.mem_nhds h0Y)
            (form_coeff_analyticOn_affineProjY_target
              (H := H) form a hpX hpY q hQ)).continuousAt
        have hContCan :
            ContinuousAt ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) 0 := by
          exact (AnalyticOn.analyticAt
            ((affineChartProjY (H := H) a hpX).open_target.mem_nhds h0Y)
            (form_coeff_analyticOn_affineProjY_target
              (H := H) (HyperellipticEvenProj.hyperellipticForm H g) a hpX hpY q hQ)
            ).continuousAt
        have hEqEv : (form.coeff q) =ᶠ[𝓝[≠] (0 : ℂ)]
            ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [((affineChartProjY (H := H) a hpX).open_target.mem_nhds h0Y)]
            with w hw hwne
          exact hPunct hw hwne
        have hEq0 : form.coeff q 0 =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q 0 :=
          tendsto_nhds_unique_of_eventuallyEq
            (hContForm.tendsto.mono_left nhdsWithin_le_nhds)
            (hContCan.tendsto.mono_left nhdsWithin_le_nhds) hEqEv
        simpa [hz0] using hEq0
      · exact hPunct hzY hz0
  · let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
    by_cases hbY : b ∈ smoothLocusY Hrev
    · have hzInf : z ∈ (affineChartProjX (H := Hrev) b hbY).target := by
        have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
            (affineChartProjX (H := Hrev) b hbY).target := by
          rw [extChartAt_target]
          change ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range ↑𝓘(ℂ, ℂ) =
            (affineChartProjX (H := Hrev) b hbY).target
          change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range (id : ℂ → ℂ) =
            (affineChartProjX (H := Hrev) b hbY).target
          rw [Set.range_id, Set.inter_univ]
          unfold HyperellipticEvenProj.chartAt
          rw [hQ]
          simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY, Hrev]
        rwa [hExt] at hz
      have hPunct : ∀ {w : ℂ},
          w ∈ (affineChartProjX (H := Hrev) b hbY).target →
          w ≠ 0 →
          form.coeff q w =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q w := by
        intro w hw hwne
        let bp : HyperellipticAffineInfinity H :=
          (affineChartProjX (H := Hrev) b hbY).symm w
        have hbp_src : bp ∈ (affineChartProjX (H := Hrev) b hbY).source := by
          simpa [bp] using (affineChartProjX (H := Hrev) b hbY).map_target hw
        have hbp_fst : bp.val.1 = w := by
          simpa [bp] using affineChartProjX_symm_apply_fst (H := Hrev) b hbY hw
        have hbp_snd :
            bp.val.2 =
              (squareLocalHomeomorph (H := Hrev) b hbY).symm (Hrev.f.eval w) := by
          simpa [bp] using affineChartProjX_symm_apply_snd (H := Hrev) b hbY hw
        have hbpY : bp ∈ smoothLocusY Hrev := by
          change bp.val.2 ≠ 0
          have hne := squareLocalHomeomorph_symm_ne_zero (H := Hrev) b hbY hw
          simpa [hbp_snd] using hne
        have hbp_u_ne : bp.val.1 ≠ 0 := by
          simpa [hbp_fst] using hwne
        let a : HyperellipticAffine H := affineUngluingImage (H := H) bp hbp_u_ne
        have haY : a ∈ smoothLocusY H :=
          affineUngluingImage_mem_smoothLocusY (H := H) bp hbpY hbp_u_ne
        have hxA : a.val.1 ≠ 0 := by
          simpa [a, affineUngluingImage] using inv_ne_zero hbp_u_ne
        have hxInv : a.val.1⁻¹ = w := by
          simp [a, hbp_fst, affineUngluingImage]
        have hGlue : affineGluingImage (H := H) a hxA = bp := by
          simpa [a] using affineGluingImage_affineUngluingImage (H := H) bp hbp_u_ne
        have hmem :
            affineGluingImage (H := H) a hxA ∈
              (affineChartProjX (H := Hrev) b hbY).source := by
          simpa [hGlue] using hbp_src
        have hSrc :
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) ∈
              (infinityLiftChart H hf.out b).source :=
          quotient_mk_inl_mem_infinityLiftChart_source_of_gluing_mem
            (H := H) a hxA b hbY hmem
        let qInf : HyperellipticEvenProj H :=
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)
        have hq_eq : q = qInf := by
          have hOut : Quotient.mk (hyperellipticEvenSetoid H) (Quotient.out q) = q :=
            Quotient.out_eq q
          rw [hQ] at hOut
          simpa [qInf] using hOut.symm
        have hQInf : Quotient.out qInf = Sum.inr b := by
          simpa [← hq_eq, qInf] using hQ
        have hFix :
            affCoeff (H := H) form a a.val.1 =
              form.coeff qInf (a.val.1⁻¹) * (-1 / a.val.1 ^ 2) :=
          affCoeff_eq_fixed_infinity_of_source
            (H := H) form a haY b hbY hQInf hSrc
        have hAff :
            affCoeff (H := H) form a a.val.1 = g.eval a.val.1 / a.val.2 :=
          affCoeff_eq_polynomial_div_of_removable_eq
            (H := H) form hgEval a haY
        have hglue_coord :
            bp.val.2 = a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := by
          have h := congrArg (fun c : HyperellipticAffineInfinity H => c.val.2) hGlue
          simpa [affineGluingImage_val_snd] using h.symm
        have hCore :
            g.eval a.val.1 / a.val.2 =
              (infReverse H g).eval (a.val.1⁻¹) / bp.val.2 *
                (-1 / a.val.1 ^ 2) := by
          have h := cross_summand_cocycle_coord
            (H := H) (g_aff := g) hDeg hxA haY hglue_coord
          have hfac : (-(a.val.1 ^ 2)⁻¹) = -1 / a.val.1 ^ 2 := by
            ring
          simpa [hfac] using h
        have hfac_ne : (-1 / a.val.1 ^ 2) ≠ 0 := by
          exact div_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) (pow_ne_zero 2 hxA)
        have hCoeffAt :
            form.coeff qInf (a.val.1⁻¹) =
              (infReverse H g).eval (a.val.1⁻¹) / bp.val.2 := by
          have hmul :
              form.coeff qInf (a.val.1⁻¹) * (-1 / a.val.1 ^ 2) =
                ((infReverse H g).eval (a.val.1⁻¹) / bp.val.2) *
                  (-1 / a.val.1 ^ 2) := by
            rw [← hFix, hAff, hCore]
          exact mul_right_cancel₀ hfac_ne hmul
        have htarget : a.val.1⁻¹ ∈ (affineChartProjX (H := Hrev) b hbY).target := by
          simpa [hxInv] using hw
        have hbp_snd_at :
            (squareLocalHomeomorph (H := Hrev) b hbY).symm (Hrev.f.eval (a.val.1⁻¹)) =
              bp.val.2 := by
          have hsnd := affineChartProjX_symm_apply_snd (H := Hrev) b hbY htarget
          simpa [bp, hxInv] using hsnd.symm
        have hCanCoeff :
            (HyperellipticEvenProj.hyperellipticForm H g).coeff qInf (a.val.1⁻¹) =
              (infReverse H g).eval (a.val.1⁻¹) / bp.val.2 := by
          rw [HyperellipticEvenProj.hyperellipticForm_coeff_of_lt H hDeg]
          unfold hyperellipticEvenCoeff
          rw [hQInf]
          change hyperellipticAffineInfinityCoeff (H := H) (infReverse H g) b
              (a.val.1⁻¹) =
            (infReverse H g).eval (a.val.1⁻¹) / bp.val.2
          change hyperellipticAffineCoeff (H := Hrev) (infReverse H g) b
              (a.val.1⁻¹) =
            (infReverse H g).eval (a.val.1⁻¹) / bp.val.2
          rw [hyperellipticAffineCoeff]
          split_ifs with hbY'
          · have htarget' :
                a.val.1⁻¹ ∈ (affineChartProjX (H := Hrev) b hbY').target := by
              simpa using htarget
            rw [affineProjXCoeff_eq_on_target
              (H := Hrev) (infReverse H g) b hbY' htarget']
            have hbp_snd_at' :
                (squareLocalHomeomorph (H := Hrev) b hbY').symm
                    (Hrev.f.eval (a.val.1⁻¹)) = bp.val.2 := by
              simpa using hbp_snd_at
            rw [hbp_snd_at']
          · exact False.elim (hbY' hbY)
        have hAt :
            form.coeff qInf (a.val.1⁻¹) =
              (HyperellipticEvenProj.hyperellipticForm H g).coeff qInf (a.val.1⁻¹) := by
          rw [hCoeffAt, hCanCoeff]
        simpa [hq_eq, hxInv] using hAt
      by_cases hz0 : z = (0 : ℂ)
      · have h0Inf : (0 : ℂ) ∈ (affineChartProjX (H := Hrev) b hbY).target := by
          simpa [hz0] using hzInf
        have hContForm : ContinuousAt (form.coeff q) 0 := by
          have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
            form.2.1 q
          have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
              (affineChartProjX (H := Hrev) b hbY).target := by
            rw [extChartAt_target]
            change ↑𝓘(ℂ, ℂ).symm ⁻¹'
                  (HyperellipticEvenProj.chartAt H hf.out q).target ∩
                Set.range ↑𝓘(ℂ, ℂ) =
              (affineChartProjX (H := Hrev) b hbY).target
            change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
                Set.range (id : ℂ → ℂ) =
              (affineChartProjX (H := Hrev) b hbY).target
            rw [Set.range_id, Set.inter_univ]
            unfold HyperellipticEvenProj.chartAt
            rw [hQ]
            simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
              affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY, Hrev]
          rw [hExt] at hform
          exact (AnalyticOn.analyticAt
            ((affineChartProjX (H := Hrev) b hbY).open_target.mem_nhds h0Inf)
            hform).continuousAt
        have hContCan :
            ContinuousAt ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) 0 := by
          have hform : AnalyticOn ℂ
              ((HyperellipticEvenProj.hyperellipticForm H g).coeff q)
              (extChartAt 𝓘(ℂ, ℂ) q).target :=
            (HyperellipticEvenProj.hyperellipticForm H g).2.1 q
          have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
              (affineChartProjX (H := Hrev) b hbY).target := by
            rw [extChartAt_target]
            change ↑𝓘(ℂ, ℂ).symm ⁻¹'
                  (HyperellipticEvenProj.chartAt H hf.out q).target ∩
                Set.range ↑𝓘(ℂ, ℂ) =
              (affineChartProjX (H := Hrev) b hbY).target
            change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
                Set.range (id : ℂ → ℂ) =
              (affineChartProjX (H := Hrev) b hbY).target
            rw [Set.range_id, Set.inter_univ]
            unfold HyperellipticEvenProj.chartAt
            rw [hQ]
            simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
              affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY, Hrev]
          rw [hExt] at hform
          exact (AnalyticOn.analyticAt
            ((affineChartProjX (H := Hrev) b hbY).open_target.mem_nhds h0Inf)
            hform).continuousAt
        have hEqEv : (form.coeff q) =ᶠ[𝓝[≠] (0 : ℂ)]
            ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [((affineChartProjX (H := Hrev) b hbY).open_target.mem_nhds h0Inf)]
            with w hw hwne
          exact hPunct hw hwne
        have hEq0 : form.coeff q 0 =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q 0 :=
          tendsto_nhds_unique_of_eventuallyEq
            (hContForm.tendsto.mono_left nhdsWithin_le_nhds)
            (hContCan.tendsto.mono_left nhdsWithin_le_nhds) hEqEv
        simpa [hz0] using hEq0
      · exact hPunct hzInf hz0
    · have hb2_zero : b.val.2 = 0 := by
        by_contra hne
        exact hbY (by simpa [smoothLocusY] using hne)
      have hbX : b ∈ smoothLocusX Hrev :=
        mem_smoothLocusX_of_y_eq_zero Hrev hb2_zero
      have hzInf : z ∈ (affineChartProjY (H := Hrev) b hbX).target := by
        have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
            (affineChartProjY (H := Hrev) b hbX).target := by
          rw [extChartAt_target]
          change ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range ↑𝓘(ℂ, ℂ) =
            (affineChartProjY (H := Hrev) b hbX).target
          change (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range (id : ℂ → ℂ) =
            (affineChartProjY (H := Hrev) b hbX).target
          rw [Set.range_id, Set.inter_univ]
          unfold HyperellipticEvenProj.chartAt
          rw [hQ]
          simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbY, Hrev]
        rwa [hExt] at hz
      let e := polynomialLocalHomeomorph (H := Hrev) b hbX
      have hroot : Hrev.f.eval b.val.1 = 0 := by
        have hprop := b.property
        simpa [Hrev, hb2_zero] using hprop.symm
      have hb_u_ne : b.val.1 ≠ 0 := by
        intro h0
        have hroot0 : (Polynomial.reverse H.f).eval 0 = 0 := by
          simpa [Hrev, h0] using hroot
        have hlead : H.f.leadingCoeff = 0 := by
          simpa [reverse_eval_zero_eq_leadingCoeff (H := H)] using hroot0
        exact hyperelliptic_leadingCoeff_ne_zero (H := H) hlead
      have hbSrcChart : b ∈ (affineChartProjY (H := Hrev) b hbX).source :=
        affineChartProjY_mem_source (H := Hrev) b hbX
      have hzeroInf : (0 : ℂ) ∈ (affineChartProjY (H := Hrev) b hbX).target := by
        have hmap := (affineChartProjY (H := Hrev) b hbX).map_source hbSrcChart
        change b.val.2 ∈ (affineChartProjY (H := Hrev) b hbX).target at hmap
        simpa [hb2_zero] using hmap
      have hCoeff_of_eventually {z0 : ℂ}
          (hz0T : z0 ∈ (affineChartProjY (H := Hrev) b hbX).target)
          (hEqEv : (form.coeff q) =ᶠ[𝓝[≠] z0]
              ((HyperellipticEvenProj.hyperellipticForm H g).coeff q)) :
          form.coeff q z0 =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q z0 := by
        have hContForm : ContinuousAt (form.coeff q) z0 := by
          exact (AnalyticOn.analyticAt
            ((affineChartProjY (H := Hrev) b hbX).open_target.mem_nhds hz0T)
            (form_coeff_analyticOn_infinityProjY_target
              (H := H) form b hbX hbY q hQ)).continuousAt
        have hContCan :
            ContinuousAt ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) z0 := by
          exact (AnalyticOn.analyticAt
            ((affineChartProjY (H := Hrev) b hbX).open_target.mem_nhds hz0T)
            (form_coeff_analyticOn_infinityProjY_target
              (H := H) (HyperellipticEvenProj.hyperellipticForm H g) b hbX hbY q hQ)
            ).continuousAt
        exact tendsto_nhds_unique_of_eventuallyEq
          (hContForm.tendsto.mono_left nhdsWithin_le_nhds)
          (hContCan.tendsto.mono_left nhdsWithin_le_nhds) hEqEv
      have hDirect : ∀ {w : ℂ},
          w ∈ (affineChartProjY (H := Hrev) b hbX).target →
          w ≠ 0 →
          e.symm (w ^ 2) ≠ 0 →
          form.coeff q w =
            (HyperellipticEvenProj.hyperellipticForm H g).coeff q w := by
        intro w hw hwne hu
        let bp : HyperellipticAffineInfinity H :=
          (affineChartProjY (H := Hrev) b hbX).symm w
        have hbp_fst : bp.val.1 = e.symm (w ^ 2) := by
          simpa [bp, e] using affineChartProjY_symm_apply_fst (H := Hrev) b hbX hw
        have hbp_snd : bp.val.2 = w := by
          simpa [bp] using affineChartProjY_symm_apply_snd (H := Hrev) b hbX hw
        have hbpY : bp ∈ smoothLocusY Hrev := by
          change bp.val.2 ≠ 0
          simpa [hbp_snd] using hwne
        have hbp_u_ne : bp.val.1 ≠ 0 := by
          simpa [hbp_fst] using hu
        let a : HyperellipticAffine H := affineUngluingImage (H := H) bp hbp_u_ne
        have haY : a ∈ smoothLocusY H :=
          affineUngluingImage_mem_smoothLocusY (H := H) bp hbpY hbp_u_ne
        have hxA : a.val.1 ≠ 0 := by
          simpa [a, affineUngluingImage] using inv_ne_zero hbp_u_ne
        have hu_eq : e.symm (w ^ 2) = a.val.1⁻¹ := by
          simpa [a, affineUngluingImage] using hbp_fst.symm
        have hGlue : affineGluingImage (H := H) a hxA = bp := by
          simpa [a] using affineGluingImage_affineUngluingImage (H := H) bp hbp_u_ne
        have hBranchSymm :
            (infinityLiftChart H hf.out b).symm w =
              Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) := by
          change ((affineChartAt (H := Hrev) b).lift_openEmbedding
              (isOpenEmbedding_proj_inr H hf.out)).symm w =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
          rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbY]
          change Quotient.mk (hyperellipticEvenSetoid H)
              (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm w)) =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
          change Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bp) =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
          rw [← hGlue]
          exact (proj_eq_affineGluingImage (H := H) a hxA).symm
        have hBranch :
            affCoeff (H := H) form a a.val.1 =
              - (a.val.1⁻¹) ^ 2 *
                (liouvilleInfinityProjYNumerator (H := H) form b hbX q w / w) :=
          affCoeff_eq_liouvilleInfinityProjYNumerator_div_of_branch
            (H := H) form b hbX hbY q hQ a haY hxA hw hwne hBranchSymm
            (by simpa [e] using hu_eq)
        have hAff :
            affCoeff (H := H) form a a.val.1 = g.eval a.val.1 / a.val.2 :=
          affCoeff_eq_polynomial_div_of_removable_eq
            (H := H) form hgEval a haY
        have hglue_coord :
            bp.val.2 = a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := by
          have h := congrArg (fun c : HyperellipticAffineInfinity H => c.val.2) hGlue
          simpa [affineGluingImage_val_snd] using h.symm
        have hCore :
            g.eval a.val.1 / a.val.2 =
              (infReverse H g).eval (a.val.1⁻¹) / bp.val.2 *
                (- (a.val.1⁻¹) ^ 2) := by
          have h := cross_summand_cocycle_coord
            (H := H) (g_aff := g) hDeg hxA haY hglue_coord
          have hfac : (-(a.val.1 ^ 2)⁻¹) = - (a.val.1⁻¹) ^ 2 := by
            rw [inv_pow]
          simpa [hfac] using h
        have hfactor_ne : - (a.val.1⁻¹) ^ 2 ≠ 0 := by
          exact neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hxA))
        have hdiv :
            liouvilleInfinityProjYNumerator (H := H) form b hbX q w / w =
              (infReverse H g).eval (a.val.1⁻¹) / bp.val.2 := by
          have hmul :
              - (a.val.1⁻¹) ^ 2 *
                  (liouvilleInfinityProjYNumerator (H := H) form b hbX q w / w) =
                ((infReverse H g).eval (a.val.1⁻¹) / bp.val.2) *
                  (- (a.val.1⁻¹) ^ 2) := by
            rw [← hBranch, hAff, hCore]
          have hmul' :
              (liouvilleInfinityProjYNumerator (H := H) form b hbX q w / w) *
                  (- (a.val.1⁻¹) ^ 2) =
                ((infReverse H g).eval (a.val.1⁻¹) / bp.val.2) *
                  (- (a.val.1⁻¹) ^ 2) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact mul_right_cancel₀ hfactor_ne hmul'
        have hNum :
            liouvilleInfinityProjYNumerator (H := H) form b hbX q w =
              (infReverse H g).eval (e.symm (w ^ 2)) := by
          have hdiv' := hdiv
          rw [hbp_snd] at hdiv'
          rw [← hu_eq] at hdiv'
          field_simp [hwne] at hdiv'
          exact hdiv'
        have hNumCan :
            liouvilleInfinityProjYNumerator (H := H)
                (HyperellipticEvenProj.hyperellipticForm H g) b hbX q w =
              (infReverse H g).eval (e.symm (w ^ 2)) := by
          simpa [e] using
            liouvilleInfinityProjYNumerator_hyperellipticForm_eq
              (H := H) hDeg b hbX hbY q hQ hw
        have hNumEq :
            liouvilleInfinityProjYNumerator (H := H) form b hbX q w =
              liouvilleInfinityProjYNumerator (H := H)
                (HyperellipticEvenProj.hyperellipticForm H g) b hbX q w := by
          rw [hNum, hNumCan]
        unfold liouvilleInfinityProjYNumerator at hNumEq
        have hFne :
            (Polynomial.reverse H.f).derivative.eval (e.symm (w ^ 2)) ≠ 0 := by
          simpa [e, Hrev] using
            polynomialLocalHomeomorph_symm_eval_derivative_ne_zero
              (H := Hrev) b hbX hw
        field_simp [hFne] at hNumEq
        let D : ℂ := (Polynomial.reverse H.f).derivative.eval (e.symm (w ^ 2))
        have hcoeff :
            form.coeff q w * D =
              (HyperellipticEvenProj.hyperellipticForm H g).coeff q w * D := by
          simpa [D, e, mul_comm] using hNumEq
        exact mul_right_cancel₀ (by simpa [D] using hFne) hcoeff
      by_cases hz0 : z = 0
      · have hbase_src : b.val.1 ∈ e.source := by
          have hbSrc := hbSrcChart
          change b.val.1 ∈ e.source at hbSrc
          exact hbSrc
        have hbase_eval : (e : ℂ → ℂ) b.val.1 = 0 := by
          change Hrev.f.eval b.val.1 = 0
          exact hroot
        have hU0_eq : e.symm (0 : ℂ) = b.val.1 := by
          have hleft := e.left_inv hbase_src
          rw [hbase_eval] at hleft
          simpa using hleft
        have hU0_ne : e.symm (0 : ℂ) ≠ 0 := by
          rw [hU0_eq]
          exact hb_u_ne
        have hContU0 : ContinuousAt (fun w : ℂ => e.symm (w ^ 2)) 0 := by
          have h0sq : (0 : ℂ) ^ 2 ∈ e.target := by
            simpa [HyperellipticAffine.affineChartProjY, e] using hzeroInf
          have hsymm : ContinuousAt e.symm (0 : ℂ) := by
            simpa using e.continuousAt_symm h0sq
          have hpow : ContinuousAt (fun w : ℂ => w ^ 2) (0 : ℂ) := by
            simpa using
              ((continuousAt_id : ContinuousAt (fun w : ℂ => w) (0 : ℂ)).pow 2)
          have hcomp :
              ContinuousAt (e.symm ∘ fun w : ℂ => w ^ 2) (0 : ℂ) :=
            ContinuousAt.comp_of_eq (g := e.symm) (f := fun w : ℂ => w ^ 2)
              (x := (0 : ℂ)) (y := (0 : ℂ)) hsymm hpow (by norm_num)
          simpa [Function.comp_def] using hcomp
        have hU0sq_ne : e.symm ((0 : ℂ) ^ 2) ≠ 0 := by
          simpa using hU0_ne
        have hUNE : ∀ᶠ w in 𝓝 (0 : ℂ), e.symm (w ^ 2) ≠ 0 :=
          hContU0.eventually_ne hU0sq_ne
        have hEqEv : (form.coeff q) =ᶠ[𝓝[≠] (0 : ℂ)]
            ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [
            ((affineChartProjY (H := Hrev) b hbX).open_target.mem_nhds hzeroInf),
            hUNE] with w hw hune hwne
          exact hDirect hw (by simpa using hwne) hune
        simpa [hz0] using hCoeff_of_eventually hzeroInf hEqEv
      · by_cases huZ : e.symm (z ^ 2) = 0
        · have hz_ne_neg : z ≠ -z := by
            intro hneg
            have htwice : (2 : ℂ) * z = 0 := by
              simpa [two_mul] using (add_eq_zero_iff_eq_neg.mpr hneg)
            have hz_eq : z = 0 :=
              (mul_eq_zero.mp htwice).resolve_left (by norm_num)
            exact hz0 hz_eq
          have hne0Ev : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
            eventually_ne_nhds hz0
          have hneNegEv : ∀ᶠ w in 𝓝 z, w ≠ -z :=
            eventually_ne_nhds hz_ne_neg
          have hEqEv : (form.coeff q) =ᶠ[𝓝[≠] z]
              ((HyperellipticEvenProj.hyperellipticForm H g).coeff q) := by
            rw [eventuallyEq_nhdsWithin_iff]
            filter_upwards [
              ((affineChartProjY (H := Hrev) b hbX).open_target.mem_nhds hzInf),
              hne0Ev, hneNegEv] with w hw hw0 hwneNeg hwnez
            have hune : e.symm (w ^ 2) ≠ 0 := by
              intro huw
              have hw2 : w ^ 2 ∈ e.target := by
                simpa [HyperellipticAffine.affineChartProjY, e] using hw
              have hz2 : z ^ 2 ∈ e.target := by
                simpa [HyperellipticAffine.affineChartProjY, e] using hzInf
              have hsq : w ^ 2 = z ^ 2 := by
                calc
                  w ^ 2 = (e : ℂ → ℂ) (e.symm (w ^ 2)) := (e.right_inv hw2).symm
                  _ = (e : ℂ → ℂ) 0 := by rw [huw]
                  _ = (e : ℂ → ℂ) (e.symm (z ^ 2)) := by rw [huZ]
                  _ = z ^ 2 := e.right_inv hz2
              rcases eq_or_eq_neg_of_sq_eq_sq w z hsq with hwz | hwneg
              · exact hwnez hwz
              · exact hwneNeg hwneg
            exact hDirect hw hw0 hune
          exact hCoeff_of_eventually hzInf hEqEv
        · exact hDirect hzInf hz0 huZ

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
