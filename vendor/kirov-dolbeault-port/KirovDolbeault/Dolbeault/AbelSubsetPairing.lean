/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetCriterion
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.FormCoeff
import KirovDolbeault.HolomorphicForms

/-!
# Abel ⊆ campaign, P-block: the concrete period pairing `σ ↦ ∫_X σ∧ω`

Realization of the period functional that the S-block's abstract criterion
(`mem_dbarImage_of_periodFunctional`, `AbelSubsetCriterion.lean`) consumes — rungs P1–P6 of
`docs/planning/AB_ROUTE.md`.  The global integral is the PoU-planar `FineResidue.resIntegral`;
the pairing's `(1,1)` chart-coefficient family is the product of

* the **(0,1) read** of `σ ∈ A^{0,1}(X)` — the proven `cutoffPullback` of the forward Dolbeault
  comparison (smooth, compactly supported, `ℝ`-linear in `σ`), whose `conj φ′` overlap law
  (`cutoffPullback_overlap_law`, **P1**) we derive from the cross-chart cancellation
  `dbar_planarDiff_eq_zero` + the Wirtinger chain rule — no frame computations;
* a **holomorphic `(1,0)` slot family** `g` (`IsOneZeroCoeff`, in the application the chart
  coefficients `omegaCoeff 𝔇 ω` of a global holomorphic 1-form).

Main declarations:

* `pairCoeff 𝔇 σ g` / `pairCoeff_mem_oneOneCoeff` (**P2**) — the product family is a global
  `(1,1)` chart-coefficient family (`conj φ′ · φ′ = |φ′|²`, R1's `OneOneLawAt`).
* `pairFormL 𝔇 hσ hg` / `pairOmega 𝔇 σ α` (**P3**) — the pairing `∫_X σ∧ω` as the
  `resIntegral` of `pairCoeff`; `ℝ`-linear in `σ`, `ℂ`-linear in the holomorphic slot
  (`pairOmega_slot_smul`, `pairOmega_slot_add`), `ℂ`-homogeneous in `σ` through constant
  rescaling (`pairOmega_cSmul`).
* `pairOmega_dbarL` (**P4**, the Stokes kill) — `∫_X ∂̄u∧ω = 0`: per chart the Leibniz split
  `ρ̃ⱼ·∂̄ũⱼ·gⱼ = ∂̄(ρ̃ⱼ·ũⱼ·gⱼ) − ∂̄ρ̃ⱼ·ũⱼ·gⱼ` plus the planar Stokes atom, then the proven
  relocation + PoU-reinsertion kill of `CoboundaryVanish` at the global weight `β = u`.
* `exists_pairOmega_ne_zero` (**P5**, nondegeneracy) — every nonzero holomorphic form pairs
  nontrivially against some `(0,1)`-form: a one-chart bump witness `σ = h·∂̄w` whose pairing is
  `∫ χ·|f|² > 0` at a point where the coefficient `f` of `ω` does not vanish.
* `pairPeriod_surjective` (**P5**) — the period functional `Λ = (pairOmega · ωᵢ)ᵢ` onto
  `ℂ^g` is surjective: its range is a `ℂ`-subspace (P3 homogeneity) meeting no annihilating
  hyperplane (P5 nondegeneracy + slot linearity).
* `dbar_solvable_of_pairOmega_eq_zero` (**P6**, the solvability theorem) — Forster 19.10:
  a `(0,1)`-form pairing to zero against every holomorphic 1-form is `∂̄`-exact.  S4 + P4 + P5.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19.10, §20; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. X §2.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`Integral` (the
-- `SmoothCFunctions` coercions and hom-bundle instances below need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ## P1 — the `(0,1)` overlap law of the cutoff chart-pullback

The chart-`j` read of `σ ∈ A^{0,1}` used throughout is the **proven** forward-comparison datum
`𝔇.cutoffPullback j σ` (smooth with compact support, equal to the honest read `σ x (frame 1)` on
the chart image of `U j` where the disk bump is `1`).  Its `(0,1)` transformation law on overlaps
falls out of three public bricks of the comparison proof — no frame algebra:

* `∂̄(planarPrimitive i σ) = cutoffPullback i σ`  (`dbar_planarPrimitive`),
* the cross-chart cancellation `∂̄(P_k∘φ − P_j) = 0` on overlaps (`dbar_planarDiff_eq_zero`),
* the Wirtinger chain rule `∂̄(f∘φ) = conj φ′ · (∂̄f)∘φ` (`dbarDisk_comp_holo`). -/

/-- The `FineResidue` transition map is the extended-chart transition (the model embedding of
`𝓘(ℝ, ℂ)` is the identity, so both are the bare chart composite). -/
theorem transitionMap_eq_extChartAt (j k : 𝔇.toFiniteCover.ι) (z : ℂ) :
    transitionMap 𝔇 j k z
      = (extChartAt 𝓘(ℝ, ℂ) (𝔇.center k)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z) := rfl

/-- **P1 — the pointwise `(0,1)` overlap law of the cutoff chart-pullback.**  At the chart-`j`
coordinate of every overlap point `x ∈ U j ⊓ U k`,

  `σ̃_j = (σ̃_k ∘ φ_{jk}) · conj φ′_{jk}`,   `σ̃_i := cutoffPullback 𝔇 i σ`.

Derivation: both disk primitives satisfy `∂̄P_i = σ̃_i`; the relocated difference `P_k∘φ − P_j`
is `∂̄`-closed at the overlap (`dbar_planarDiff_eq_zero`), and the chain rule turns
`∂̄(P_k∘φ)` into `conj φ′ · σ̃_k∘φ`. -/
theorem cutoffPullback_overlap_law {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {j k : 𝔇.toFiniteCover.ι} {x : X} (hxj : x ∈ (𝔇.U j : Set X))
    (hxk : x ∈ (𝔇.U k : Set X)) :
    𝔇.cutoffPullback j σ (chartMap 𝔇 j x)
      = 𝔇.cutoffPullback k σ (transitionMap 𝔇 j k (chartMap 𝔇 j x))
          * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x)) := by
  set z₀ := chartMap 𝔇 j x with hz₀
  set τ := transitionMap 𝔇 j k with hτ
  -- The relocated difference of the disk primitives is `∂̄`-closed at `z₀` (the relocated read
  -- is definitionally `P_k ∘ τ` — the model embedding of `𝓘(ℝ, ℂ)` is the identity).
  have hdiff0 : DbarDisk.dbar (fun z => (𝔇.planarPrimitive k σ ∘ τ) z
      - 𝔇.planarPrimitive j σ z) z₀ = 0 :=
    𝔇.dbar_planarDiff_eq_zero hσ j k hxj hxk
  -- Differentiability of the pieces at `z₀`.
  have hτdiff : DifferentiableAt ℂ τ z₀ :=
    (transitionMap_analyticAt 𝔇 hxj hxk).differentiableAt
  have hPk : DifferentiableAt ℝ (𝔇.planarPrimitive k σ) (τ z₀) :=
    (𝔇.contDiff_planarPrimitive k σ).differentiable (by norm_num) _
  have hPj : DifferentiableAt ℝ (𝔇.planarPrimitive j σ) z₀ :=
    (𝔇.contDiff_planarPrimitive j σ).differentiable (by norm_num) _
  have hPkτ : DifferentiableAt ℝ (𝔇.planarPrimitive k σ ∘ τ) z₀ :=
    hPk.comp z₀ (hτdiff.restrictScalars ℝ)
  -- `∂̄` of the difference splits termwise.
  have hsub : DbarDisk.dbar (fun z => (𝔇.planarPrimitive k σ ∘ τ) z
        - 𝔇.planarPrimitive j σ z) z₀
      = DbarDisk.dbar (𝔇.planarPrimitive k σ ∘ τ) z₀
        - DbarDisk.dbar (𝔇.planarPrimitive j σ) z₀ := by
    unfold DbarDisk.dbar
    rw [show (fun z => (𝔇.planarPrimitive k σ ∘ τ) z - 𝔇.planarPrimitive j σ z)
        = (𝔇.planarPrimitive k σ ∘ τ) - 𝔇.planarPrimitive j σ from rfl,
      fderiv_sub hPkτ hPj]
    simp only [ContinuousLinearMap.sub_apply]
    ring
  rw [hsub] at hdiff0
  -- Chain rule on the relocated primitive, then read the two `∂̄`s as cutoff pullbacks.
  rw [dbarDisk_comp_holo (𝔇.planarPrimitive k σ) τ z₀ hPk hτdiff,
    𝔇.dbar_planarPrimitive k σ (τ z₀), 𝔇.dbar_planarPrimitive j σ z₀] at hdiff0
  linear_combination -hdiff0

/-! ## P2 — the pairing `(1,1)` chart-coefficient family -/

/-- The **pairing `(1,1)` chart-coefficient family** of a smooth `(0,1)`-form `σ` and a
holomorphic `(1,0)` slot family `g`:

  `t_j := σ̃_j · g_j`,   `σ̃_j = cutoffPullback 𝔇 j σ`

— the chart-coefficient presentation of the global `(1,1)`-form `σ∧ω` whose surface integral is
the period pairing.  (For the cutoff-vs-honest-read discrepancy outside the disks: the residue
integral weights by `pouCoeff`, which vanishes there, so only the honest read is ever
integrated.) -/
noncomputable def pairCoeff (σ : SmoothCOneForms X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) :
    𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun j z => 𝔇.cutoffPullback j σ z * g j z

@[simp] theorem pairCoeff_apply (σ : SmoothCOneForms X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j : 𝔇.toFiniteCover.ι) (z : ℂ) :
    pairCoeff 𝔇 σ g j z = 𝔇.cutoffPullback j σ z * g j z := rfl

/-- **P2 — the pairing family is a global `(1,1)` chart-coefficient family.**  Smoothness is the
(global) smoothness of the cutoff pullback times the analyticity of the slot; the `(1,1)` law
`normSq φ′` assembles as `conj φ′` (P1) times `φ′` (the slot's `OneZeroLawAt`), by
`Complex.mul_conj`. -/
theorem pairCoeff_mem_oneOneCoeff {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    pairCoeff 𝔇 σ g ∈ oneOneCoeff 𝔇 := by
  rw [mem_oneOneCoeff]
  constructor
  · intro j x hx
    exact ((𝔇.contDiff_cutoffPullback j σ).contDiffAt).mul
      (((hg.1 j x hx).restrictScalars (𝕜 := ℝ)).contDiffAt)
  · intro j k x hx
    unfold OneOneLawAt
    filter_upwards [(isOpen_overlapImage 𝔇 j k).mem_nhds ⟨x, hx, rfl⟩, hg.2 j k x hx]
      with z hzov hzg
    obtain ⟨x', hx', hzx'⟩ := hzov
    subst hzx'
    have hlaw := cutoffPullback_overlap_law 𝔇 hσ hx'.1 hx'.2
    have hns : ((normSq (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x')) :=
      (Complex.mul_conj _).symm
    simp only [pairCoeff_apply]
    rw [hlaw, hzg, hns]
    ring

/-! ## P3 — the pairing as a linear functional

`pairFormL 𝔇 hg : A^{0,1}(X) →ₗ[ℝ] ℂ` is `resIntegral` of the pairing family; linearity in `σ`
comes from the (proven) `ℝ`-linearity of the cutoff pullback through the `ℂ`-linearity of
`resIntegral`. -/

/-- The pairing family bundled as an element of the `(1,1)` submodule. -/
noncomputable def pairElem {σ : SmoothCOneForms X} (hσ : σ ∈ OneFormsZeroOne X)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) : oneOneCoeff 𝔇 :=
  ⟨pairCoeff 𝔇 σ g, pairCoeff_mem_oneOneCoeff 𝔇 hσ hg⟩

/-- **P3 — the period pairing against a fixed holomorphic slot family, as an `ℝ`-linear
functional on `A^{0,1}(X)`**:

  `σ ↦ ∮_X σ∧ω := resIntegral 𝔇 (σ̃·g)`.

(`ℝ`-linear because `A^{0,1}` carries only `Module ℝ`; `ℂ`-rescaling is `pairFormL_cSmulForm`
below.) -/
noncomputable def pairFormL {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    ↥(OneFormsZeroOne X) →ₗ[ℝ] ℂ where
  toFun σ := resIntegral 𝔇 (pairElem 𝔇 σ.2 hg)
  map_add' σ τ := by
    have helem : pairElem 𝔇 (σ + τ).2 hg = pairElem 𝔇 σ.2 hg + pairElem 𝔇 τ.2 hg := by
      apply Subtype.ext
      show pairCoeff 𝔇 ((σ : SmoothCOneForms X) + (τ : SmoothCOneForms X)) g
        = pairCoeff 𝔇 (σ : SmoothCOneForms X) g + pairCoeff 𝔇 (τ : SmoothCOneForms X) g
      funext j z
      simp only [pairCoeff_apply, 𝔇.cutoffPullback_add j, Pi.add_apply]
      ring
    rw [helem, map_add]
  map_smul' c σ := by
    have helem : pairElem 𝔇 (c • σ).2 hg = (c : ℂ) • pairElem 𝔇 σ.2 hg := by
      apply Subtype.ext
      show pairCoeff 𝔇 (c • (σ : SmoothCOneForms X)) g
        = (c : ℂ) • pairCoeff 𝔇 (σ : SmoothCOneForms X) g
      funext j z
      simp only [pairCoeff_apply, 𝔇.cutoffPullback_smul j, Pi.smul_apply, smul_eq_mul,
        Complex.real_smul]
      ring
    rw [helem, map_smul, RingHom.id_apply, smul_eq_mul, Complex.real_smul]

theorem pairFormL_apply {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g)
    (σ : ↥(OneFormsZeroOne X)) :
    pairFormL 𝔇 hg σ = resIntegral 𝔇 (pairElem 𝔇 σ.2 hg) := rfl

/-- **The period pairing against a global holomorphic 1-form** — `pairFormL` at the canonical
slot family `omegaCoeff 𝔇 α` (the chart coefficients of `α`, R-lane witness
`isOneZeroCoeff_omegaCoeff`). -/
noncomputable def pairOmega (σ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) : ℂ :=
  pairFormL 𝔇 (isOneZeroCoeff_omegaCoeff 𝔇 α) σ

theorem pairOmega_apply (σ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) :
    pairOmega 𝔇 σ α
      = resIntegral 𝔇 (pairElem 𝔇 σ.2 (isOneZeroCoeff_omegaCoeff 𝔇 α)) := rfl

/-! ## P4 — the Stokes kill: `∫_X ∂̄u ∧ ω = 0`

Per chart: the cutoff pullback of `∂̄u` is the planar `∂̄` of the chart read of `u`
(`cutoffPullback_dbarL`, the chart-bridge + chain-rule computation), the Leibniz split
`ρ̃ⱼ·∂̄ũⱼ·gⱼ = ∂̄(ρ̃ⱼ·ũⱼ·gⱼ) − ∂̄ρ̃ⱼ·(ũⱼ·gⱼ)` (its total-derivative part dying by the planar
Stokes atom), and then the **proven** relocation + PoU-reinsertion kill of `CoboundaryVanish`
at the global weight `β = u`. -/

/-- **P4a — the cutoff pullback of `∂̄u` is the planar `∂̄` of the chart read of `u`** on the
chart image of the cover disk.  The intrinsic Wirtinger scalar transported to the cover chart:
chart bridge at `x`'s own chart (`dbar_apply_one_eq_dbarDisk`), conjugate-homogeneity of the
`(0,1)` fiber (`proj01_eq_conj_smul`), the frame identity
(`frameVector_eq_deriv_transition_symm`), and the Wirtinger chain rule reassembling the two
`conj` factors. -/
theorem cutoffPullback_dbarL {u : SmoothCFunctions X} {j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U j : Set X)) :
    𝔇.cutoffPullback j (dbarL u) (chartMap 𝔇 j x)
      = DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
  set ej := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) with hej
  set ex := extChartAt 𝓘(ℝ, ℂ) x with hexx
  set z₀ := chartMap 𝔇 j x with hz₀
  set σtr := (ex : X → ℂ) ∘ (ej.symm : ℂ → X) with hσtr
  have hxsrc : x ∈ ej.source := 𝔇.subset_chart_source j hx
  have hsymm : ej.symm z₀ = x := ej.left_inv hxsrc
  -- The disk bump is `1` on the disk.
  have hball : ej x ∈ Metric.ball (ej (𝔇.center j)) (𝔇.radius j) := by
    have h := hx
    rw [𝔇.isDisk j] at h
    exact h.1
  have hχ : (𝔇.diskBump j) z₀ = 1 :=
    (𝔇.diskBump j).one_of_mem_closedBall (Metric.ball_subset_closedBall hball)
  -- Unfold the cutoff pullback at `z₀` and substitute the frame vector.
  rw [show 𝔇.cutoffPullback j (dbarL u) z₀ = ((𝔇.diskBump j) z₀ : ℝ) •
      ((dbarL u) (ej.symm z₀)) ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j)) (ej.symm z₀)) (1 : ℂ))
    from rfl, hχ, hsymm, one_smul,
    frameVector_eq_deriv_transition_symm (𝔇.center j) x hxsrc]
  -- Re-read the left side as `proj01 (mfderiv u x)` applied to the (planar) `deriv σtr (ej x)`,
  -- so the conjugate-homogeneity + chart bridge apply.
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) (deriv σtr (ej x))
    = DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z₀
  rw [proj01_eq_conj_smul, dbar_apply_one_eq_dbarDisk u x]
  -- Read the right-hand side through the holomorphic inverse transition `σtr = eₓ ∘ ej.symm`.
  have hσdiff : DifferentiableAt ℂ σtr z₀ :=
    differentiableAt_chartTransition_symm (𝔇.center j) x hxsrc
  have hσz₀ : σtr z₀ = ex x := by
    rw [hσtr]
    simp only [Function.comp_apply, hsymm]
  have hev : (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ))
      =ᶠ[𝓝 z₀] (fun ζ => u (ex.symm ζ)) ∘ σtr := by
    have hcont : ContinuousAt ej.symm z₀ :=
      continuousAt_extChartAt_symm'' (ej.map_source hxsrc)
    have hmem : ∀ᶠ ζ in 𝓝 z₀, ej.symm ζ ∈ ex.source := by
      refine hcont.preimage_mem_nhds ?_
      rw [hsymm]
      exact (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
    filter_upwards [hmem] with ζ hζ
    simp only [Function.comp_apply, hσtr]
    rw [ex.left_inv hζ]
    rfl
  have hudiff : DifferentiableAt ℝ (fun ζ => u (ex.symm ζ)) (σtr z₀) := by
    rw [hσz₀]
    exact (contDiffAt_chartSymmRead u.contMDiff
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).differentiableAt (by simp)
  rw [dbar_congr_of_eventuallyEq hev,
    dbarDisk_comp_holo (fun ζ => u (ex.symm ζ)) σtr z₀ hudiff hσdiff, hσz₀]
  rfl

/-- **P4b — the per-chart Leibniz/Stokes step at a global smooth `β`** (the `∂̄u`-pairing
analogue of `integral_pouCoeff_glueCoeff_of_coboundary`): the `j`-th summand of the pairing
integral is, after the Leibniz split

  `ρ̃ⱼ·∂̄β̃ⱼ·gⱼ = ∂̄(ρ̃ⱼ·(β̃ⱼ·gⱼ)) − ∂̄ρ̃ⱼ·(β̃ⱼ·gⱼ)`

and the planar Stokes atom on the total-derivative term, minus the PoU-reinserted overlap sum
ready for the (proven) relocation. -/
theorem integral_pouCoeff_dbarRead_mul {β : X → ℂ}
    (hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) β) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z
        * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
  have hBsm := contDiffAt_pouAverageRead_mul 𝔇 hβ hg j
  -- the everywhere pointwise Leibniz identity
  have hpt : ∀ z, pouCoeff 𝔇 j z
      * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        - DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    intro z
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
        (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hxU)
      have hβd : DifferentiableAt ℝ
          (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) :=
        (contDiffAt_chartSymmRead hβ hzt).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      have hdbarB : DbarDisk.dbar
            (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hβd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarPB : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (β ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _)
          ((hBsm _ ⟨x, hxU, rfl⟩).differentiableAt (by simp))
      rw [hdbarPB, hdbarB]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hPB0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hP0, hD0, hPB0, zero_mul, zero_mul, sub_zero]
  -- integrability bookkeeping (the `CoboundaryVanish` clearance pattern)
  have hDBcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    contDiff_of_chartImage_clearance 𝔇
      (fun z hz => (ChartDiskCover.contDiffAt_dbar_chartDisk
        (contDiff_pouCoeff 𝔇 j).contDiffAt).mul (hBsm z hz))
      (fun z hz => by rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul])
  have hDBcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hI1 : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hDBcd.continuous.integrable_of_hasCompactSupport hDBcs
  have hPBcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    contDiff_pouCoeff_mul 𝔇 hBsm
  have hPBcs : HasCompactSupport fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    (hasCompactSupport_pouCoeff 𝔇 j).mul_right
  have hI2 : Integrable fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z :=
    (DbarDisk.continuous_dbar hPBcd).integrable_of_hasCompactSupport
      (DbarDisk.hasCompactSupport_dbar hPBcs)
  calc ∫ z, pouCoeff 𝔇 j z
      * (DbarDisk.dbar (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z)
      = ∫ z, (DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
          - DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
          - ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
        integral_sub hI2 hI1
    _ = - ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
        rw [integral_dbar_eq_zero hPBcd hPBcs, zero_sub]
    _ = - ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
    _ = - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        congr 1
        refine integral_finsetSum Finset.univ fun k _ => ?_
        have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
            rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
          contDiff_of_chartImage_clearance 𝔇
            (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
              (chartMap_image_U_subset_target 𝔇 j hz)).mul hDBcd.contDiffAt)
            (fun z hz => by
              rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
        exact hcd.continuous.integrable_of_hasCompactSupport hDBcs.mul_left

/-- **P4 — the Stokes kill.**  The period pairing annihilates the image of `∂̄`:

  `∮_X ∂̄u ∧ ω = 0`

for every real-smooth `u : X → ℂ` and every holomorphic `(1,0)` slot family.  Per chart the
integrand is `ρ̃ⱼ·∂̄ũⱼ·gⱼ` (P4a); Leibniz + planar Stokes (P4b), the proven relocation
(`integral_overlapTerm_relocate` at `β = u`), and the PoU-reinsertion kill
(`sum_integral_relocated_eq_zero`) finish exactly as in Forster §17.3 step 5. -/
theorem pairFormL_dbarL {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g)
    (u : SmoothCFunctions X) :
    pairFormL 𝔇 hg ⟨dbarL u, dbarL_mem_zeroOne u⟩ = 0 := by
  have happly : pairFormL 𝔇 hg ⟨dbarL u, dbarL_mem_zeroOne u⟩
      = ∑ j, ∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z) := rfl
  rw [happly]
  -- replace the cutoff pullback of `∂̄u` by the planar `∂̄` of the chart read (P4a)
  have hcongr : ∀ j, (∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z))
      = ∫ z, pouCoeff 𝔇 j z
          * (DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z) := by
    intro j
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      rw [cutoffPullback_dbarL 𝔇 hxU]
    · rw [show pouCoeff 𝔇 j z = 0 from Set.indicator_of_notMem hzU _, zero_mul, zero_mul]
  calc ∑ j, ∫ z, pouCoeff 𝔇 j z * (𝔇.cutoffPullback j (dbarL u) z * g j z)
      = ∑ j, ∫ z, pouCoeff 𝔇 j z
          * (DbarDisk.dbar (fun ζ => u ((chartAt ℂ (𝔇.center j)).symm ζ)) z * g j z) :=
        Finset.sum_congr rfl fun j _ => hcongr j
    _ = ∑ j, - ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (u ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
        Finset.sum_congr rfl fun j _ =>
          integral_pouCoeff_dbarRead_mul 𝔇 u.contMDiff hg j
    _ = - ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (u ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => congrArg Neg.neg <|
          Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate 𝔇 u.contMDiff hg j k
    _ = - ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (u ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
        rw [Finset.sum_comm]
    _ = 0 := by
        rw [Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero 𝔇 u.contMDiff hg k,
          neg_zero]

/-- **P4 at the canonical slot**: `∮_X ∂̄u ∧ α = 0` for every global holomorphic 1-form. -/
theorem pairOmega_dbarL (u : SmoothCFunctions X) (α : HolomorphicOneForms X) :
    pairOmega 𝔇 ⟨dbarL u, dbarL_mem_zeroOne u⟩ α = 0 :=
  pairFormL_dbarL 𝔇 (isOneZeroCoeff_omegaCoeff 𝔇 α) u

end Jacobians.Dolbeault.FineResidue
