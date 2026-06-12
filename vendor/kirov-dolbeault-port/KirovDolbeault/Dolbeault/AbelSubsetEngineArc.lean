/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetEngineLocal

/-!
# Abel ⊆ campaign, E3: the per-arc weak solution (Forster 20.5)

The E3 per-arc constructor of `docs/planning/AB_E_ROUTE.md` §2: for two distinct points
`a ≠ b` of one cover disk `U j₀` of a `ChartDiskCover`, the Forster 20.5 one-disk weak
solution for the divisor `(b) − (a)`:

* **planar layer** (`SegTube`): a tube system around the coordinate segment `[za, zb]`
  inside the coordinate ball — radius `δ`, a smooth cutoff `ψ` (`1` on the half-tube, `0`
  off the `δ`-tube) and a smooth co-cutoff `θ` (`0` near the segment, `1` off the
  quarter-tube) from the smooth Urysohn lemma; the weak solution
  `F̃ = exp(ψ·log((z−zb)/(z−za)))` glued across the segment as the Möbius ratio
  (`SegTube.Ffun`), with the master planar identity `∂̄F̃ = F̃·(H·∂̄ψ)` off the endpoints
  (`SegTube.dbar_Ffun`), where `H = θ·log((z−zb)/(z−za))` (`SegTube.Hfun`) is globally
  smooth;
* **interface** (`ArcWeakSolution`): the geometric fields of `RawLogDbarDatum` for a
  divisor `D` — everything except the E4 pairing identity, which enters only through the
  constructor `ArcWeakSolution.toRaw` as an explicit hypothesis (E4 is rung-separate; the
  constructor is *conditional on the pairing field*, as `AB_E_ROUTE.md` §2 prescribes);
* **the per-arc constructor** (`exists_arcWeakSolution`): the lifted weak solution
  `F = F̃ ∘ e` on `U j₀` (extended by `1`), the one-chart `(0,1)` datum
  `σ = (lift H)·∂̄(lift ψ)` (the `exists_pairOmega_pos` single-chart support pattern), and
  the four geometric fields: nonvanishing, chart-read differentiability, the logarithmic
  `∂̄`-identity in every cover chart, and the local normal form `(z−za)^{∓1}·unit` at the
  endpoints (`dslope` of the biholomorphic chart transition).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.4–20.5; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VIII §4.
-/

open Complex Metric
open scoped Manifold ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Jacobians.Dolbeault

open FineResidue

/-! ## The planar layer: the segment tube system -/

/-- **The segment tube system** (the planar geometry of Forster 20.5): for the segment
`[a, b]` inside the ball `B(c₀, R)`, a tube radius `δ` with the closed `δ`-tube inside the
ball, a smooth cutoff `ψ` (`≡ 1` on the closed half-tube, `≡ 0` off the open `δ`-tube) and
a smooth co-cutoff `θ` (`≡ 0` on the closed eighth-tube, `≡ 1` off the open quarter-tube).
`θ` kills the segment singularity of the slit logarithm (`Hfun` is globally smooth) and is
`≡ 1` wherever `∂̄ψ ≠ 0`. -/
structure SegTube (a b c₀ : ℂ) (R : ℝ) where
  /-- The tube radius. -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- The closed `δ`-tube lies inside the coordinate ball. -/
  tube_subset : cthickening δ (segment ℝ a b) ⊆ ball c₀ R
  /-- The cutoff. -/
  ψ : ℂ → ℝ
  /-- The co-cutoff. -/
  θ : ℂ → ℝ
  ψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ
  θ_smooth : ContDiff ℝ (⊤ : ℕ∞) θ
  ψ_one : Set.EqOn ψ 1 (cthickening (δ / 2) (segment ℝ a b))
  ψ_zero : Set.EqOn ψ 0 (thickening δ (segment ℝ a b))ᶜ
  θ_zero : Set.EqOn θ 0 (cthickening (δ / 8) (segment ℝ a b))
  θ_one : Set.EqOn θ 1 (thickening (δ / 4) (segment ℝ a b))ᶜ

/-- A segment tube system exists for any segment inside an open ball: the tube radius from
`IsCompact.exists_cthickening_subset_open`, the two cutoffs from the smooth Urysohn lemma
(`exists_contMDiffMap_zero_one_of_isClosed` on the manifold `ℂ`). -/
theorem SegTube.exists_segTube {a b c₀ : ℂ} {R : ℝ}
    (hseg : segment ℝ a b ⊆ ball c₀ R) : Nonempty (SegTube a b c₀ R) := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_segment a b).exists_cthickening_subset_open isOpen_ball hseg
  -- the cutoff ψ: `0` off the open δ-tube, `1` on the closed half-tube
  obtain ⟨ψ, hψ0, hψ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) isOpen_thickening.isClosed_compl (isClosed_cthickening
      (δ := δ / 2) (E := segment ℝ a b))
    (disjoint_compl_left.mono_right
      (cthickening_subset_thickening' hδpos (by linarith) (segment ℝ a b)))
  -- the co-cutoff θ: `0` on the closed eighth-tube, `1` off the open quarter-tube
  obtain ⟨θ, hθ0, hθ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) (isClosed_cthickening (δ := δ / 8) (E := segment ℝ a b))
    isOpen_thickening.isClosed_compl
    (disjoint_compl_right.mono_left
      (cthickening_subset_thickening' (by linarith) (by linarith) (segment ℝ a b)))
  exact ⟨{
    δ := δ
    δ_pos := hδpos
    tube_subset := hδsub
    ψ := ψ
    θ := θ
    ψ_smooth := contMDiff_iff_contDiff.mp ψ.contMDiff
    θ_smooth := contMDiff_iff_contDiff.mp θ.contMDiff
    ψ_one := hψ1
    ψ_zero := hψ0
    θ_zero := hθ0
    θ_one := hθ1 }⟩

namespace SegTube

variable {a b c₀ : ℂ} {R : ℝ} (T : SegTube a b c₀ R)

/-- The cutoff, complex-valued. -/
def psiC : ℂ → ℂ := fun z => (T.ψ z : ℂ)

/-- The globally smooth logarithm weight `H = θ·log((z−b)/(z−a))`: the co-cutoff `θ` kills
the slit-segment singularity. -/
def Hfun : ℂ → ℂ := fun z => (T.θ z : ℂ) * slitLogRatio a b z

/-- **The Forster 20.5 one-disk weak solution**: the Möbius ratio `(z−b)/(z−a)` on the open
half-tube (across the segment), glued as `exp(ψ·log((z−b)/(z−a)))` off the segment;
`≡ 1` off the `δ`-tube. -/
def Ffun : ℂ → ℂ := fun z =>
  if z ∈ thickening (T.δ / 2) (segment ℝ a b) then (z - b) / (z - a)
  else Complex.exp (T.psiC z * slitLogRatio a b z)

theorem psiC_smooth : ContDiff ℝ (⊤ : ℕ∞) T.psiC :=
  Complex.ofRealCLM.contDiff.comp T.ψ_smooth

/-- The slit-segment logarithm is real-`C^∞` off the segment (holomorphic ⟹ analytic). -/
theorem contDiffAt_slitLogRatio_real {z : ℂ} (hz : z ∉ segment ℝ a b) :
    ContDiffAt ℝ (⊤ : ℕ∞) (slitLogRatio a b) z := by
  have hopen : IsOpen (segment ℝ a b)ᶜ := (isCompact_segment a b).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ (slitLogRatio a b) (segment ℝ a b)ᶜ := fun w hw =>
    (differentiableAt_slitLogRatio hw).differentiableWithinAt
  exact (((hdiff.analyticOnNhd hopen) z hz).restrictScalars (𝕜 := ℝ)).contDiffAt

theorem Hfun_smooth : ContDiff ℝ (⊤ : ℕ∞) T.Hfun := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ thickening (T.δ / 8) (segment ℝ a b)
  · -- near the segment, `θ ≡ 0` kills everything
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
    rw [Hfun, T.θ_zero (thickening_subset_cthickening _ _ hw)]
    simp
  · -- off the eighth-tube the slit logarithm is smooth
    have hzs : z ∉ segment ℝ a b := fun hmem =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ hmem)
    exact ((Complex.ofRealCLM.contDiff.comp T.θ_smooth).contDiffAt).mul
      (T.contDiffAt_slitLogRatio_real hzs)

/-- Off the segment, the weak solution is the exponential `exp(ψ·log)`. -/
theorem Ffun_eq_exp {z : ℂ} (hz : z ∉ segment ℝ a b) :
    T.Ffun z = Complex.exp (T.psiC z * slitLogRatio a b z) := by
  rw [Ffun]
  split_ifs with hmem
  · rw [psiC, T.ψ_one (thickening_subset_cthickening _ _ hmem)]
    simp only [Pi.one_apply, Complex.ofReal_one, one_mul]
    exact (exp_slitLogRatio hz).symm
  · rfl

/-- On the open half-tube (across the segment), the weak solution is the Möbius ratio. -/
theorem Ffun_eq_ratio {z : ℂ} (hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)) :
    T.Ffun z = (z - b) / (z - a) := if_pos hz

/-- Off the closed `δ`-tube, the weak solution is `1`. -/
theorem Ffun_eq_one {z : ℂ} (hz : z ∉ cthickening T.δ (segment ℝ a b)) :
    T.Ffun z = 1 := by
  have hzth : z ∉ thickening T.δ (segment ℝ a b) := fun h =>
    hz (thickening_subset_cthickening _ _ h)
  have hzs : z ∉ segment ℝ a b := fun h =>
    hzth (self_subset_thickening T.δ_pos _ h)
  rw [T.Ffun_eq_exp hzs, psiC, T.ψ_zero hzth]
  simp

/-- The weak solution is nonvanishing off the endpoints. -/
theorem Ffun_ne_zero {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) : T.Ffun z ≠ 0 := by
  rw [Ffun]
  split_ifs
  · exact div_ne_zero (sub_ne_zero.mpr hzb) (sub_ne_zero.mpr hza)
  · exact Complex.exp_ne_zero _

/-- The weak solution is real-differentiable off the endpoints. -/
theorem differentiableAt_Ffun {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    DifferentiableAt ℝ T.Ffun z := by
  by_cases hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)
  · -- across the segment: the ratio is holomorphic at `z ≠ a`
    have hev : T.Ffun =ᶠ[𝓝 z] fun w => (w - b) / (w - a) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      exact T.Ffun_eq_ratio hw
    have hd : DifferentiableAt ℂ (fun w : ℂ => (w - b) / (w - a)) z :=
      (differentiableAt_id.sub_const b).div (differentiableAt_id.sub_const a)
        (sub_ne_zero.mpr hza)
    exact hev.differentiableAt_iff.mpr (hd.restrictScalars ℝ)
  · -- off the half-tube: the exponential of a smooth function
    have hzs : z ∉ segment ℝ a b := fun h =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ h)
    have hev : T.Ffun =ᶠ[𝓝 z]
        fun w => Complex.exp (T.psiC w * slitLogRatio a b w) := by
      filter_upwards [(isCompact_segment a b).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      exact T.Ffun_eq_exp hw
    have hv : DifferentiableAt ℝ (fun w => T.psiC w * slitLogRatio a b w) z :=
      (T.psiC_smooth.contDiffAt.differentiableAt le_top).mul
        ((T.contDiffAt_slitLogRatio_real hzs).differentiableAt le_top)
    exact hev.differentiableAt_iff.mpr hv.cexp

/-- **The master planar `∂̄`-identity** (Forster 20.5): off the endpoints,
`∂̄F̃ = F̃·(H·∂̄ψ)`.  Across the segment both sides vanish (the ratio is holomorphic, the
cutoff locally constant); off the half-tube `θ ≡ 1` makes `H` the slit logarithm and the
chain rule on `exp(ψ·log)` produces exactly `F̃·log·∂̄ψ`. -/
theorem dbar_Ffun {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    DbarDisk.dbar T.Ffun z = T.Ffun z * (T.Hfun z * DbarDisk.dbar T.psiC z) := by
  by_cases hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)
  · -- across the segment: `∂̄(ratio) = 0` and `∂̄ψ = 0`
    have hev : T.Ffun =ᶠ[𝓝 z] fun w => (w - b) / (w - a) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      exact T.Ffun_eq_ratio hw
    have hL : DbarDisk.dbar T.Ffun z = 0 := by
      rw [dbar_congr_of_eventuallyEq hev]
      exact DbarDisk.dbar_eq_zero_of_differentiableAt
        ((differentiableAt_id.sub_const b).div (differentiableAt_id.sub_const a)
          (sub_ne_zero.mpr hza))
    have hψev : T.psiC =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      rw [psiC, T.ψ_one (thickening_subset_cthickening _ _ hw)]
      simp
    rw [hL, dbar_congr_of_eventuallyEq hψev, DbarDisk.dbar_const]
    ring
  · -- off the half-tube: chain rule on the exponential, `θ ≡ 1`
    have hzs : z ∉ segment ℝ a b := fun h =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ h)
    have hθ1 : T.θ z = 1 := by
      refine T.θ_one fun h => hz (thickening_mono (by linarith [T.δ_pos]) _ h)
    have hev : T.Ffun =ᶠ[𝓝 z]
        fun w => Complex.exp (T.psiC w * slitLogRatio a b w) := by
      filter_upwards [(isCompact_segment a b).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      exact T.Ffun_eq_exp hw
    have hψd : DifferentiableAt ℝ T.psiC z :=
      T.psiC_smooth.contDiffAt.differentiableAt le_top
    have hLd : DifferentiableAt ℝ (slitLogRatio a b) z :=
      (T.contDiffAt_slitLogRatio_real hzs).differentiableAt le_top
    have hv : DifferentiableAt ℝ (fun w => T.psiC w * slitLogRatio a b w) z := hψd.mul hLd
    rw [dbar_congr_of_eventuallyEq hev, dbarFun_exp hv,
      dbarFun_mul' hψd hLd,
      DbarDisk.dbar_eq_zero_of_differentiableAt (differentiableAt_slitLogRatio hzs),
      ← T.Ffun_eq_exp hzs, Hfun, hθ1]
    push_cast
    ring

end SegTube

/-! ## The per-arc interface: the geometric fields of `RawLogDbarDatum`

`ArcWeakSolution 𝔇 D` is `RawLogDbarDatum` for a divisor `D` in place of a chain boundary,
*without* the E4 pairing field: exactly the geometric output of the per-arc construction.
The pairing identity enters only through `toRaw`, as an explicit hypothesis — the E2
constructor is **conditional on the pairing field** (E4 is its own rung). -/

/-- **The per-arc weak-solution datum** for a divisor `D`: the geometric fields of
`RawLogDbarDatum` (weak solution, global `(0,1)` datum, nonvanishing, chart-read
differentiability and logarithmic `∂̄`-identity off the support, endpoint normal forms) —
everything except the E4 pairing identity. -/
structure ArcWeakSolution (𝔇 : ChartDiskCover X) (D : Divisor X) where
  /-- The weak solution. -/
  F : X → ℂ
  /-- The global smooth `(0,1)` logarithmic datum. -/
  σ : ↥(OneFormsZeroOne X)
  /-- `F` is nonvanishing off the support of `D`. -/
  F_ne : ∀ x : X, D x = 0 → F x ≠ 0
  /-- Off the support, the cover-chart read of `F` is real-differentiable. -/
  diff_off : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
    DifferentiableAt ℝ (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w))
      (chartMap 𝔇 j x)
  /-- Off the support, the planar logarithmic `∂̄`-identity `∂̄F = F·σ̃` holds in every
  cover chart. -/
  dbar_eq : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
    DbarDisk.dbar (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
      = F x * 𝔇.cutoffPullback j (σ : SmoothCOneForms X) (chartMap 𝔇 j x)
  /-- At each support point, the own-chart read of `F` has the local normal form
  `(z − a)^{D(a)}·(continuous nonvanishing unit)`. -/
  norm_form : ∀ a : X, D a ≠ 0 → ∃ w : ℂ → ℂ,
    ContinuousAt w ((chartAt (H := ℂ) a) a) ∧ w ((chartAt (H := ℂ) a) a) ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
      F ((chartAt (H := ℂ) a).symm z)
        = (z - (chartAt (H := ℂ) a) a) ^ (D a) * w z

/-- **The conditional E2/E3 constructor**: a per-arc weak solution for the boundary divisor
of a chain, *plus* the E4 pairing identity for its `σ`, yields the raw logarithmic-`∂̄`
datum (and hence, through `RawLogDbarDatum.toLogDbarDatum`, the full E2 interface).  The
pairing hypothesis is the one remaining E4 obligation. -/
def ArcWeakSolution.toRaw {𝔇 : ChartDiskCover X} {D : Divisor X}
    (W : ArcWeakSolution 𝔇 D) (c : SmoothOneChain X) (hD : c.boundary = D)
    (hpair : ∀ α : HolomorphicOneForms X,
      FineResidue.pairOmega 𝔇 W.σ α = 2 * (Real.pi : ℂ) * Complex.I * c.period α) :
    RawLogDbarDatum 𝔇 c where
  F := W.F
  σ := W.σ
  pairing := hpair
  F_ne := fun x hx => W.F_ne x (by rw [← hD]; exact hx)
  diff_off := fun j x hxU hx0 => W.diff_off j x hxU (by rw [← hD]; exact hx0)
  dbar_eq := fun j x hxU hx0 => W.dbar_eq j x hxU (by rw [← hD]; exact hx0)
  norm_form := fun x hx => by
    have h := W.norm_form x (by rw [← hD] at hx; exact hx)
    rw [← hD] at h
    exact h

end Jacobians.Dolbeault

end
