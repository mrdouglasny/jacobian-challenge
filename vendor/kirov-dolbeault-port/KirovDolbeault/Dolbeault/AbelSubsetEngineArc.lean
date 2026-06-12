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

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

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

/-- A segment tube system exists at any prescribed radius whose closed tube fits in the
ball: the two cutoffs from the smooth Urysohn lemma
(`exists_contMDiffMap_zero_one_of_isClosed` on the manifold `ℂ`). -/
theorem SegTube.exists_segTube_of_radius {a b c₀ : ℂ} {R δ : ℝ} (hδpos : 0 < δ)
    (hδsub : cthickening δ (segment ℝ a b) ⊆ ball c₀ R) :
    ∃ T : SegTube a b c₀ R, T.δ = δ := by
  -- the cutoff ψ: `0` off the open δ-tube, `1` on the closed half-tube
  obtain ⟨ψ, hψ0, hψ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) isOpen_thickening.isClosed_compl (isClosed_cthickening
      (δ := δ / 2) (E := segment ℝ a b))
    (disjoint_compl_left.mono_right
      (cthickening_subset_thickening' hδpos (by linarith) (segment ℝ a b)))
  -- the co-cutoff θ: `0` on the closed eighth-tube, `1` off the open quarter-tube
  obtain ⟨θ, hθ0, hθ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) (isClosed_cthickening (δ := δ / 8) (E := segment ℝ a b))
    (isOpen_thickening (δ := δ / 4) (E := segment ℝ a b)).isClosed_compl
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
    θ_one := hθ1 }, rfl⟩

/-- A segment tube system exists for any segment inside an open ball
(`IsCompact.exists_cthickening_subset_open` picks the radius). -/
theorem SegTube.exists_segTube {a b c₀ : ℂ} {R : ℝ}
    (hseg : segment ℝ a b ⊆ ball c₀ R) : Nonempty (SegTube a b c₀ R) := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_segment a b).exists_cthickening_subset_open isOpen_ball hseg
  obtain ⟨T, -⟩ := SegTube.exists_segTube_of_radius hδpos hδsub
  exact ⟨T⟩

/-- **Avoiding tube**: the tube radius can additionally be chosen so the closed tube misses
any prescribed finite planar set off the segment (shrink into the ball minus those points).
This is what lets a chain of arcs keep each tube's cutoff annulus away from all OTHER
endpoints: a foreign point ON the segment is automatically in the half-tube where the weak
solution is the holomorphic Möbius ratio, and a foreign point OFF the segment is now
outside the whole tube, where the weak solution is `≡ 1`. -/
theorem SegTube.exists_segTube_avoiding {a b c₀ : ℂ} {R : ℝ}
    (hseg : segment ℝ a b ⊆ ball c₀ R) (A : Finset ℂ) :
    ∃ T : SegTube a b c₀ R,
      ∀ q ∈ A, q ∉ segment ℝ a b → q ∉ cthickening T.δ (segment ℝ a b) := by
  have hopen : IsOpen (ball c₀ R ∩ ((↑A : Set ℂ) \ segment ℝ a b)ᶜ) :=
    isOpen_ball.inter (A.finite_toSet.subset Set.diff_subset).isClosed.isOpen_compl
  have hsub : segment ℝ a b ⊆ ball c₀ R ∩ ((↑A : Set ℂ) \ segment ℝ a b)ᶜ := fun z hz =>
    ⟨hseg hz, fun hzd => hzd.2 hz⟩
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_segment a b).exists_cthickening_subset_open hopen hsub
  obtain ⟨T, hTδ⟩ := SegTube.exists_segTube_of_radius hδpos
    (hδsub.trans Set.inter_subset_left)
  refine ⟨T, fun q hqA hqseg hqth => ?_⟩
  rw [hTδ] at hqth
  exact (hδsub hqth).2 ⟨Finset.mem_coe.mpr hqA, hqseg⟩

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
      (contDiffAt_slitLogRatio_real hzs)

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

/-- The weak solution is real-differentiable off the pole `a` (even at the zero `b`). -/
theorem differentiableAt_Ffun {z : ℂ} (hza : z ≠ a) :
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
      (T.psiC_smooth.contDiffAt.differentiableAt (by simp)).mul
        ((contDiffAt_slitLogRatio_real hzs).differentiableAt (by simp))
    exact hev.differentiableAt_iff.mpr hv.cexp

/-- **The master planar `∂̄`-identity** (Forster 20.5): off the endpoints,
`∂̄F̃ = F̃·(H·∂̄ψ)`.  Across the segment both sides vanish (the ratio is holomorphic, the
cutoff locally constant); off the half-tube `θ ≡ 1` makes `H` the slit logarithm and the
chain rule on `exp(ψ·log)` produces exactly `F̃·log·∂̄ψ`. -/
theorem dbar_Ffun {z : ℂ} (hza : z ≠ a) :
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
      T.psiC_smooth.contDiffAt.differentiableAt (by simp)
    have hLd : DifferentiableAt ℝ (slitLogRatio a b) z :=
      (contDiffAt_slitLogRatio_real hzs).differentiableAt (by simp)
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
  /-- The `(0,1)` datum vanishes (pointwise) at the support: the cutoff annulus carrying
  `∂̄ψ` stays away from the segment endpoints.  (Used by the chain fold: at a cancelling
  support point the folded `σ`'s stay zero, so the folded `∂̄`-identity survives.) -/
  σ_vanish : ∀ x : X, D x ≠ 0 → (σ : SmoothCOneForms X) x = 0
  /-- At each support point, the own-chart read of `F` has the local normal form
  `(z − a)^{D(a)}·(analytic nonvanishing unit)` — analytic (not merely continuous) because
  near its endpoints the weak solution is the Möbius ratio on the half-tube.  (Analyticity
  is what lets the chain fold cancel a zero of one arc against the pole of the next.) -/
  norm_form : ∀ a : X, D a ≠ 0 → ∃ w : ℂ → ℂ,
    AnalyticAt ℂ w ((chartAt (H := ℂ) a) a) ∧ w ((chartAt (H := ℂ) a) a) ≠ 0 ∧
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
    RawLogDbarDatum 𝔇 c := by
  subst hD
  exact {
    F := W.F
    σ := W.σ
    pairing := hpair
    F_ne := W.F_ne
    diff_off := W.diff_off
    dbar_eq := W.dbar_eq
    norm_form := fun x hx => by
      obtain ⟨w, hwa, hw0, hev⟩ := W.norm_form x hx
      exact ⟨w, hwa.continuousAt, hw0, hev⟩ }

/-! ## E3 — the per-arc lift: from the planar tube system to `ArcWeakSolution`

The lift of the planar Forster 20.5 data through one cover chart `j₀`: the weak solution
`F = F̃ ∘ e` (extended by `1` off the closed tube preimage `K`), the single-chart `(0,1)`
datum `σ = (lift H)·∂̄(lift ψ)` (the `exists_pairOmega_pos` support pattern), the chart-`j`
reads handled by the holomorphic transition `w = e_{j₀} ∘ e_j⁻¹` and the `∂̄` chain rule
`dbarDisk_comp_holo`, and the Möbius normal forms at the endpoints by `dslope` of the
biholomorphic transition from the endpoint's own chart. -/

section ArcLift

/-- `∂̄u` vanishes at any point where `u` is locally constant
(`mfderiv` congruence + `mfderiv_const`). -/
theorem dbarL_apply_eq_zero_of_eventuallyEq_const (u : SmoothCFunctions X) {x : X} {c : ℂ}
    (h : ⇑u =ᶠ[𝓝 x] fun _ => c) : dbarL u x = 0 := by
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) = 0
  rw [h.mfderiv_eq, mfderiv_const, map_zero]

variable (𝔇 : ChartDiskCover X) (j₀ : 𝔇.toFiniteCover.ι)

/-- On the cover disk, a chart lift reads back the planar function at the chart
coordinate (the disk bump is `1` there). -/
theorem chartLift_read_of_mem_U {G : ℂ → ℂ} {hG : ContDiff ℝ (⊤ : ℕ∞) G} {y : X}
    (hy : y ∈ (𝔇.U j₀ : Set X)) :
    chartLift 𝔇 j₀ G hG y = G (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) y) := by
  have hsrc : y ∈ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).source := 𝔇.subset_chart_source j₀ hy
  have hball : extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) y
      ∈ Metric.ball (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := hy
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have h := chartLift_symm_read 𝔇 j₀ (F := G) (hF := hG) hball
  rwa [(extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).left_inv hsrc] at h

/-- **E3, the per-arc constructor** (Forster 20.5, lifted to the surface): two distinct
points `a ≠ b` of one cover disk carry an `ArcWeakSolution` for the divisor `(b) − (a)`:
the lifted tube weak solution `F = F̃ ∘ e` (extended by `1` off the tube preimage), the
single-chart `(0,1)` datum `σ = (lift H)·∂̄(lift ψ)`, the logarithmic `∂̄`-identity in every
cover chart, and analytic-unit Möbius normal forms `(z−·)^{±1}·unit` at the endpoints.

**Avoidance**: the tube additionally avoids any prescribed finite set `A` — at every
`q ∈ A` other than the pole `a`, the own-chart read of `F` is *analytic* and `σ` vanishes
(the tube's cutoff annulus misses `q`).  This is the tameness a chain fold needs at the
other arcs' endpoints. -/
theorem exists_arcWeakSolution_avoiding (A : Finset X) {a b : X}
    (ha : a ∈ (𝔇.U j₀ : Set X)) (hb : b ∈ (𝔇.U j₀ : Set X)) (hab : a ≠ b) :
    ∃ W : ArcWeakSolution 𝔇 (Finsupp.single b 1 - Finsupp.single a 1),
      ∀ q ∈ A, q ≠ a →
        AnalyticAt ℂ (fun ζ => W.F ((chartAt (H := ℂ) q).symm ζ)) ((chartAt (H := ℂ) q) q)
        ∧ (W.σ : SmoothCOneForms X) q = 0 := by
  classical
  set e := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) with he
  set za := e a with hza
  set zb := e b with hzb
  set D : Divisor X := Finsupp.single b 1 - Finsupp.single a 1 with hD
  -- chart bookkeeping for the two endpoints
  have hasrc : a ∈ e.source := 𝔇.subset_chart_source j₀ ha
  have hbsrc : b ∈ e.source := 𝔇.subset_chart_source j₀ hb
  have haball : za ∈ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := ha
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have hbball : zb ∈ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := hb
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have hzab : za ≠ zb := fun h => hab (e.injOn hasrc hbsrc h)
  -- the divisor values
  have hDa : D a = -1 := by
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_of_ne hab, Finsupp.single_eq_same]
    ring
  have hDb : D b = 1 := by
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hab)]
    ring
  have hsupp : ∀ x : X, D x ≠ 0 → x = a ∨ x = b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    refine hx ?_
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_of_ne hcon.2,
      Finsupp.single_eq_of_ne hcon.1, sub_zero]
  have hne_pts : ∀ {x : X}, D x = 0 → x ∈ e.source → e x ≠ za ∧ e x ≠ zb := by
    intro x hx0 hxsrc
    constructor
    · intro h
      have hxa : x = a := e.injOn hxsrc hasrc h
      rw [hxa, hDa] at hx0
      norm_num at hx0
    · intro h
      have hxb : x = b := e.injOn hxsrc hbsrc h
      rw [hxb, hDb] at hx0
      norm_num at hx0
  -- the planar tube
  have hseg : segment ℝ za zb ⊆ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) :=
    (convex_ball _ _).segment_subset haball hbball
  obtain ⟨T, hTavoid⟩ := SegTube.exists_segTube_avoiding hseg (A.image fun q => e q)
  -- the global data
  set ψl := chartLift 𝔇 j₀ T.psiC T.psiC_smooth with hψl
  set Hl := chartLift 𝔇 j₀ T.Hfun T.Hfun_smooth with hHl
  set σ₀ : SmoothCOneForms X := cSmulForm Hl (dbarL ψl) with hσ₀
  have hσmem : σ₀ ∈ OneFormsZeroOne X := cSmulForm_mem_zeroOne Hl (dbarL_mem_zeroOne ψl)
  set F : X → ℂ := fun x => if x ∈ (𝔇.U j₀ : Set X) then T.Ffun (e x) else 1 with hF
  set K : Set X := e.symm '' cthickening T.δ (segment ℝ za zb) with hK
  -- the tube preimage K: compact inside the cover disk
  have htube_ball : cthickening T.δ (segment ℝ za zb)
      ⊆ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := T.tube_subset
  have hKU : K ⊆ (𝔇.U j₀ : Set X) := by
    rintro y ⟨z, hz, rfl⟩
    exact symm_mem_U_of_mem_ball 𝔇 (htube_ball hz)
  have hKcl : IsClosed K := by
    refine IsCompact.isClosed ?_
    refine ((isCompact_segment za zb).cthickening).image_of_continuousOn ?_
    exact (continuousOn_extChartAt_symm (𝔇.center j₀)).mono fun z hz =>
      𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall (htube_ball hz))
  have hmemK : ∀ {y : X}, y ∈ e.source →
      e y ∈ cthickening T.δ (segment ℝ za zb) → y ∈ K :=
    fun {y} hysrc hyth => ⟨e y, hyth, e.left_inv hysrc⟩
  -- the reads on the cover disk
  have hψread : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → ψl y = T.psiC (e y) :=
    fun {y} hy => chartLift_read_of_mem_U 𝔇 j₀ hy
  have hHread : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → Hl y = T.Hfun (e y) :=
    fun {y} hy => chartLift_read_of_mem_U 𝔇 j₀ hy
  have hFU : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → F y = T.Ffun (e y) := by
    intro y hy
    simp only [hF, if_pos hy]
  -- `F ≡ 1` and `lift ψ ≡ 0` off the tube preimage
  have hFone : ∀ y ∉ K, F y = 1 := by
    intro y hyK
    rw [hF]
    dsimp only
    split_ifs with hyU
    · exact T.Ffun_eq_one fun hth => hyK (hmemK (𝔇.subset_chart_source j₀ hyU) hth)
    · rfl
  have hψzero : ∀ y ∉ K, ψl y = 0 := by
    intro y hyK
    by_contra hne
    rw [hψl] at hne
    obtain ⟨hysrc, hψ⟩ := chartLift_ne_zero 𝔇 hne
    have hysrc' : y ∈ e.source := by
      rw [he, extChartAt_source]
      exact hysrc
    have hyth : e y ∈ thickening T.δ (segment ℝ za zb) := by
      by_contra hth
      refine hψ ?_
      show ((T.ψ (e y) : ℝ) : ℂ) = 0
      rw [T.ψ_zero hth]
      simp
    exact hyK (hmemK hysrc' (thickening_subset_cthickening _ _ hyth))
  -- `lift ψ ≡ 1` near the segment preimage (kills `∂̄(lift ψ)` at the endpoints)
  have hψone_ev : ∀ {x : X}, x ∈ (𝔇.U j₀ : Set X) → e x ∈ segment ℝ za zb →
      ⇑ψl =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    intro x hxU hxseg
    have hxsrc : x ∈ e.source := 𝔇.subset_chart_source j₀ hxU
    have hcont : ContinuousAt e x := continuousAt_extChartAt' hxsrc
    have hth : e x ∈ thickening (T.δ / 2) (segment ℝ za zb) :=
      self_subset_thickening (by linarith [T.δ_pos]) _ hxseg
    filter_upwards [(𝔇.U j₀).isOpen.mem_nhds hxU,
      hcont.preimage_mem_nhds (isOpen_thickening.mem_nhds hth)] with y hyU hyth
    rw [hψread hyU]
    show ((T.ψ (e y) : ℝ) : ℂ) = 1
    rw [T.ψ_one (thickening_subset_cthickening _ _ hyth)]
    simp
  -- σ vanishes at the support
  have hσsupp : ∀ x : X, D x ≠ 0 → σ₀ x = 0 := by
    intro x hx
    have hxU : x ∈ (𝔇.U j₀ : Set X) := by
      rcases hsupp x hx with rfl | rfl
      exacts [ha, hb]
    have hxseg : e x ∈ segment ℝ za zb := by
      rcases hsupp x hx with rfl | rfl
      · exact left_mem_segment ℝ za zb
      · exact right_mem_segment ℝ za zb
    have hdb : dbarL ψl x = 0 :=
      dbarL_apply_eq_zero_of_eventuallyEq_const ψl (hψone_ev hxU hxseg)
    rw [hσ₀, cSmulForm_apply, hdb]
    module
  -- F is nonvanishing off the support
  have hFne : ∀ x : X, D x = 0 → F x ≠ 0 := by
    intro x hx0
    by_cases hxU : x ∈ (𝔇.U j₀ : Set X)
    · rw [hFU hxU]
      obtain ⟨hexa, hexb⟩ := hne_pts hx0 (𝔇.subset_chart_source j₀ hxU)
      exact T.Ffun_ne_zero hexa hexb
    · rw [hF]
      simp [hxU]
  -- the chart-j differentiability of the read, off the support
  have hdiff : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
      DifferentiableAt ℝ (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w))
        (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmx : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmc : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    by_cases hxK : x ∈ K
    · -- on the tube: the read is `F̃ ∘ (holomorphic transition)`
      have hxU0 : x ∈ (𝔇.U j₀ : Set X) := hKU hxK
      have hxsrc0 : x ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hxU0
      set w : ℂ → ℂ := (chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ (𝔇.center j)).symm with hw
      have hwz : w (chartMap 𝔇 j x) = e x := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) = e x
        rw [hsymmx]
        rfl
      have hwan : AnalyticAt ℂ w (chartMap 𝔇 j x) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ (𝔇.center j))
          (chart_mem_atlas ℂ (𝔇.center j₀)) hxsrcj hxsrc0
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.Ffun ∘ w := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact (𝔇.U j₀).isOpen.mem_nhds hxU0)] with ζ hζ
        rw [hFU hζ]
        rfl
      have hFd : DifferentiableAt ℝ T.Ffun (w (chartMap 𝔇 j x)) := by
        rw [hwz]
        exact T.differentiableAt_Ffun (hne_pts hx0 (𝔇.subset_chart_source j₀ hxU0)).1
      exact hevF.differentiableAt_iff.mpr
        (hFd.comp _ (hwan.differentiableAt.restrictScalars ℝ))
    · -- off the tube: the read is locally `1`
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hFone _ hζ
      exact hevF.differentiableAt_iff.mpr (differentiableAt_const _)
  -- the chart-j logarithmic ∂̄-identity, off the support
  have hdbar : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
      DbarDisk.dbar (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
        = F x * 𝔇.cutoffPullback j σ₀ (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmx : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmc : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    -- the cutoff pullback of σ₀ collapses to `Hl x · ∂̄(read of lift ψ)`
    have hsymmx' : (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).left_inv (𝔇.subset_chart_source j hxU)
    have hcut : 𝔇.cutoffPullback j σ₀ (chartMap 𝔇 j x)
        = Hl x * DbarDisk.dbar (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
            (chartMap 𝔇 j x) := by
      rw [hσ₀, cutoffPullback_cSmulForm, hsymmx', cutoffPullback_dbarL 𝔇 hxU]
    by_cases hxK : x ∈ K
    · -- on the tube: transition chain rule + the planar master identity
      have hxU0 : x ∈ (𝔇.U j₀ : Set X) := hKU hxK
      have hxsrc0 : x ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hxU0
      obtain ⟨hexa, hexb⟩ := hne_pts hx0 (𝔇.subset_chart_source j₀ hxU0)
      set w : ℂ → ℂ := (chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ (𝔇.center j)).symm with hw
      have hwz : w (chartMap 𝔇 j x) = e x := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) = e x
        rw [hsymmx]
        rfl
      have hwan : AnalyticAt ℂ w (chartMap 𝔇 j x) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ (𝔇.center j))
          (chart_mem_atlas ℂ (𝔇.center j₀)) hxsrcj hxsrc0
      have hwd : DifferentiableAt ℂ w (chartMap 𝔇 j x) := hwan.differentiableAt
      have hevU : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j x),
          (chartAt ℂ (𝔇.center j)).symm ζ ∈ (𝔇.U j₀ : Set X) :=
        hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact (𝔇.U j₀).isOpen.mem_nhds hxU0)
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.Ffun ∘ w := by
        filter_upwards [hevU] with ζ hζ
        rw [hFU hζ]
        rfl
      have hevψ : (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.psiC ∘ w := by
        filter_upwards [hevU] with ζ hζ
        rw [hψread hζ]
        rfl
      have hFd : DifferentiableAt ℝ T.Ffun (w (chartMap 𝔇 j x)) := by
        rw [hwz]
        exact T.differentiableAt_Ffun hexa
      have hψd : DifferentiableAt ℝ T.psiC (w (chartMap 𝔇 j x)) :=
        T.psiC_smooth.contDiffAt.differentiableAt (by simp)
      rw [dbar_congr_of_eventuallyEq hevF, dbarDisk_comp_holo _ _ _ hFd hwd,
        hcut, dbar_congr_of_eventuallyEq hevψ, dbarDisk_comp_holo _ _ _ hψd hwd,
        hwz, T.dbar_Ffun hexa, hFU hxU0, hHread hxU0]
      ring
    · -- off the tube: both sides vanish
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hFone _ hζ
      have hevψ : (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (0 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hψzero _ hζ
      rw [dbar_congr_of_eventuallyEq hevF, hcut, dbar_congr_of_eventuallyEq hevψ,
        DbarDisk.dbar_const, DbarDisk.dbar_const, mul_zero, mul_zero]
  -- the endpoint normal forms (Möbius, with analytic units)
  have hnorm : ∀ p : X, D p ≠ 0 → ∃ wp : ℂ → ℂ,
      AnalyticAt ℂ wp ((chartAt (H := ℂ) p) p) ∧ wp ((chartAt (H := ℂ) p) p) ≠ 0 ∧
      ∀ᶠ ζ in 𝓝[≠] ((chartAt (H := ℂ) p) p),
        F ((chartAt (H := ℂ) p).symm ζ) = (ζ - (chartAt (H := ℂ) p) p) ^ (D p) * wp ζ := by
    intro p hp
    -- shared transition data at the endpoint's own chart
    have hpU : p ∈ (𝔇.U j₀ : Set X) := by
      rcases hsupp p hp with rfl | rfl
      exacts [ha, hb]
    have hpsrc0 : p ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hpU
    have hpsrc : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
    have hsymmp : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
      (chartAt ℂ p).left_inv hpsrc
    have hva : AnalyticAt ℂ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p) :=
      analyticAt_atlasTransition (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ (𝔇.center j₀))
        hpsrc hpsrc0
    have hvζ : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = e p := by
      show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ p).symm ((chartAt ℂ p) p)) = e p
      rw [hsymmp]
      rfl
    have hq : AnalyticAt ℂ (dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p)) ((chartAt ℂ p) p) := by
      obtain ⟨pser, hpser⟩ := id hva
      exact hpser.has_fpower_series_dslope_fslope.analyticAt
    have hdv : deriv ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ≠ 0 := by
      have h := deriv_chartTransition_ne_zero (𝔇.center j₀) p (𝔇.subset_chart_source j₀ hpU)
      have hfe : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
          = (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)) ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm := by
        funext zz
        simp [mfld_simps]
      have hpe : ((chartAt ℂ p) p : ℂ) = extChartAt 𝓘(ℝ, ℂ) p p := by
        simp [mfld_simps]
      rw [hfe, hpe]
      exact h
    have hq0 : dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p) ((chartAt ℂ p) p) ≠ 0 := by
      rw [dslope_same]
      exact hdv
    have hsymmc : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source hpsrc)
    have hmemU : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
        (chartAt ℂ p).symm ζ ∈ (𝔇.U j₀ : Set X) := by
      refine hsymmc.preimage_mem_nhds ((𝔇.U j₀).isOpen.mem_nhds ?_)
      rw [hsymmp]
      exact hpU
    have hqne : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
        dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ ≠ 0 :=
      hq.continuousAt.eventually_ne hq0
    have hvread : ∀ {ζ : ℂ}, (chartAt ℂ p).symm ζ ∈ (𝔇.U j₀ : Set X) →
        F ((chartAt ℂ p).symm ζ)
          = T.Ffun (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ) := by
      intro ζ hζ
      rw [hFU hζ]
      rfl
    rcases hsupp p hp with rfl | rfl
    · -- the pole endpoint (`D p = −1`):  F = (ζ−ζ₀)⁻¹ · (v−zb)/dslope
      have hvζa : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = za := by
        rw [hza]
        exact hvζ
      have hmemHT : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
          ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ
            ∈ thickening (T.δ / 2) (segment ℝ za zb) := by
        refine hva.continuousAt.preimage_mem_nhds (isOpen_thickening.mem_nhds ?_)
        rw [hvζa]
        exact self_subset_thickening (by linarith [T.δ_pos]) _ (left_mem_segment ℝ za zb)
      refine ⟨fun ζ => (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - zb)
          / dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ,
        (hva.sub analyticAt_const).div hq hq0, ?_, ?_⟩
      · dsimp only
        rw [dslope_same, hvζa]
        exact div_ne_zero (sub_ne_zero.mpr hzab) hdv
      · filter_upwards [self_mem_nhdsWithin, hmemU.filter_mono nhdsWithin_le_nhds,
          hmemHT.filter_mono nhdsWithin_le_nhds, hqne.filter_mono nhdsWithin_le_nhds]
          with ζ hζne hζU hζT hζq
        have hζne' : ζ ≠ (chartAt ℂ p) p := hζne
        have hsub : ζ - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr hζne'
        rw [hvread hζU, T.Ffun_eq_ratio hζT, hDa, zpow_neg_one]
        have hvza : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - za
            = (ζ - (chartAt ℂ p) p)
              * dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ := by
          rw [dslope_of_ne _ hζne', slope_def_field, hvζa]
          field_simp [hsub]
        rw [hvza]
        field_simp [hsub, hζq]
    · -- the zero endpoint (`D p = 1`):  F = (ζ−ζ₀) · dslope/(v−za)
      have hvζb : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = zb := by
        rw [hzb]
        exact hvζ
      have hmemHT : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
          ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ
            ∈ thickening (T.δ / 2) (segment ℝ za zb) := by
        refine hva.continuousAt.preimage_mem_nhds (isOpen_thickening.mem_nhds ?_)
        rw [hvζb]
        exact self_subset_thickening (by linarith [T.δ_pos]) _ (right_mem_segment ℝ za zb)
      refine ⟨fun ζ => dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
            ((chartAt ℂ p) p) ζ
          / (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - za),
        hq.div (hva.sub analyticAt_const)
          (by rw [hvζb]; exact sub_ne_zero.mpr (Ne.symm hzab)), ?_, ?_⟩
      · dsimp only
        rw [dslope_same, hvζb]
        exact div_ne_zero hdv (sub_ne_zero.mpr (Ne.symm hzab))
      · filter_upwards [self_mem_nhdsWithin, hmemU.filter_mono nhdsWithin_le_nhds,
          hmemHT.filter_mono nhdsWithin_le_nhds]
          with ζ hζne hζU hζT
        have hζne' : ζ ≠ (chartAt ℂ p) p := hζne
        have hsub : ζ - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr hζne'
        rw [hvread hζU, T.Ffun_eq_ratio hζT, hDb, zpow_one]
        have hvzb : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - zb
            = (ζ - (chartAt ℂ p) p)
              * dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ := by
          rw [dslope_of_ne _ hζne', slope_def_field, hvζb]
          field_simp [hsub]
        rw [hvzb]
        ring
  -- assemble, then discharge the avoidance conclusions
  refine ⟨{
    F := F
    σ := ⟨σ₀, hσmem⟩
    F_ne := hFne
    diff_off := hdiff
    dbar_eq := hdbar
    σ_vanish := hσsupp
    norm_form := hnorm }, ?_⟩
  intro q hqA hqa
  have hsymmq : (chartAt ℂ q).symm ((chartAt ℂ q) q) = q :=
    (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
  have hsymmcq : ContinuousAt (chartAt ℂ q).symm ((chartAt ℂ q) q) :=
    (chartAt ℂ q).continuousAt_symm ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
  by_cases hqK : q ∈ K
  · -- in the tube preimage: avoidance forces `e q` ON the segment, where `F` is the ratio
    have hqU : q ∈ (𝔇.U j₀ : Set X) := hKU hqK
    have hqsrc : q ∈ e.source := 𝔇.subset_chart_source j₀ hqU
    have hqth : e q ∈ cthickening T.δ (segment ℝ za zb) := by
      obtain ⟨z', hz', hzq⟩ := hqK
      have hz't : z' ∈ e.target :=
        𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall (htube_ball hz'))
      have heq : e q = z' := by
        rw [← hzq]
        exact e.right_inv hz't
      rwa [heq]
    have hqseg : e q ∈ segment ℝ za zb := by
      by_contra hqs
      exact hTavoid (e q) (Finset.mem_image_of_mem _ hqA) hqs hqth
    have hqea : e q ≠ za := fun h => hqa (e.injOn hqsrc hasrc h)
    constructor
    · -- the read is the Möbius ratio of the holomorphic transition
      have hτa : AnalyticAt ℂ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm)
          ((chartAt ℂ q) q) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ q) (chart_mem_atlas ℂ (𝔇.center j₀))
          (mem_chart_source ℂ q) (mem_chartSource_of_mem_U 𝔇 hqU)
      have hτq : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) = e q := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ q).symm ((chartAt ℂ q) q)) = e q
        rw [hsymmq]
        rfl
      have hread_an : AnalyticAt ℂ
          (fun ζ => (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ζ - zb)
            / (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ζ - za)) ((chartAt ℂ q) q) :=
        (hτa.sub analyticAt_const).div (hτa.sub analyticAt_const)
          (by rw [hτq]; exact sub_ne_zero.mpr hqea)
      refine hread_an.congr ?_
      have hth2 : e q ∈ thickening (T.δ / 2) (segment ℝ za zb) :=
        self_subset_thickening (by linarith [T.δ_pos]) _ hqseg
      filter_upwards [hsymmcq.preimage_mem_nhds
          (by rw [hsymmq]; exact (𝔇.U j₀).isOpen.mem_nhds hqU),
        hτa.continuousAt.preimage_mem_nhds
          (by rw [hτq]; exact isOpen_thickening.mem_nhds hth2)] with ζ hζU hζT
      rw [hFU hζU, ← T.Ffun_eq_ratio hζT]
      rfl
    · -- `lift ψ ≡ 1` near the segment kills `∂̄(lift ψ)` at `q`
      have hdb : dbarL ψl q = 0 :=
        dbarL_apply_eq_zero_of_eventuallyEq_const ψl (hψone_ev hqU hqseg)
      show σ₀ q = 0
      rw [hσ₀, cSmulForm_apply, hdb]
      module
  · -- off the tube preimage: `F ≡ 1`, `lift ψ ≡ 0` near `q`
    constructor
    · have hev : (fun ζ => F ((chartAt (H := ℂ) q).symm ζ))
          =ᶠ[𝓝 ((chartAt ℂ q) q)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmcq.preimage_mem_nhds
          (by rw [hsymmq]; exact hKcl.isOpen_compl.mem_nhds hqK)] with ζ hζ
        exact hFone _ hζ
      exact analyticAt_const.congr hev.symm
    · have hψ0ev : ⇑ψl =ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hqK] with y hy
        exact hψzero y hy
      have hdb : dbarL ψl q = 0 := dbarL_apply_eq_zero_of_eventuallyEq_const ψl hψ0ev
      show σ₀ q = 0
      rw [hσ₀, cSmulForm_apply, hdb]
      module

/-- **E3, the per-arc constructor** (plain form, no avoidance set). -/
theorem exists_arcWeakSolution {a b : X} (ha : a ∈ (𝔇.U j₀ : Set X))
    (hb : b ∈ (𝔇.U j₀ : Set X)) (hab : a ≠ b) :
    Nonempty (ArcWeakSolution 𝔇 (Finsupp.single b 1 - Finsupp.single a 1)) := by
  obtain ⟨W, -⟩ := exists_arcWeakSolution_avoiding 𝔇 j₀ ∅ ha hb hab
  exact ⟨W⟩

end ArcLift

end Jacobians.Dolbeault

end
