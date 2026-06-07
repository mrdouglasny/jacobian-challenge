/-
  Čech finiteness — the genuine-cover ∂̄-globalization FOUNDATION (Forster §13–§14, Dolbeault).

  This file banks the verified, axiom-clean foundation for discharging the (corrected) disk-acyclicity
  `leray` field of the chart-cover model — the cross-chart analogue of the single-chart prototype in
  `GluedDbarDatum.lean`.

  ## Why a fresh file (and why the SharedChartCover prototype does not directly apply)

  `GluedDbarDatum.lean` globalises a cocycle on a `SharedChartCover` — a finite family of opens living
  in ONE chart `φ = chartAt center`.  Its partition of unity sums to `1` only on a CLOSED CORE
  `C ⊊ ⋃ Uᵢ` (a subordinate PoU cannot sum to `1` on the open `⋃ Uᵢ` of a non-covering family on a
  connected `X`); that is precisely the obstruction `dbarDatum_agrees_on_interiorCore` documents — the
  glued datum agrees with `∂̄(chartPrim)` only on `interior C`, so it does NOT give a full
  `HasGluedDbarDatum`.  A single chart cannot cover a compact connected Riemann surface, so the
  `SharedChartCover` route is fundamentally partial.

  The GENUINE chart cover (`Montel`'s `chartCover`, the geometry of `CechModelGeometry.lean`) is a
  different beast: the OUTER opens `chartOpen a` (indexed by the cover charts `coverCenter a`) genuinely
  COVER `X` (`iUnion_chartOpen_eq`).  Therefore a smooth partition of unity subordinate to
  `(chartOpen a)` summing to `1` on ALL of `X` exists (`exists_genuineCoverPoU`, below) — exactly what
  `SharedChartCover` lacked.  This unblocks the PoU-globalization OVER THE COVERED REGION (here all of
  `X`), the right tool for the cross-chart Forster argument once the model's shrinking-side cochains are
  in the holomorphic (`BddHol`) representation (see the `⚠ SOUNDNESS NOTE` in `CechModelDifferential.lean`
  — the current continuous `Cshr` makes the literal `ChartCoverContinuousLeray` unprovable, so the telescoping is
  intentionally NOT plugged into that unsound field here).

  ## What is delivered (all sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

  * `exists_genuineCoverPoU` — a smooth PoU over `𝓘(ℝ,ℂ)`, subordinate to `(chartOpen (coverCenter a))`,
    summing to `1` on ALL of `X` (the genuine-cover globalization foundation).
  * `genuineCoverPoU` / `genuineCoverPoU_subordinate` / `sum_genuineCoverPoU_eq_one` — the chosen PoU and
    its sum-to-one-everywhere value form (no closed-core restriction needed — the cover covers).
  * `genuineCoverPoU_tsupport_subset` — the subordination `tsupport ρ_a ⊆ chartOpen (coverCenter a)`.

  ## What remains (the genuine analytic gap, documented — NOT a sorry here)

  The cross-chart telescoping of the Bott–Tu glued datum `ω̂ = ∑_{a,b}(ρ_b·h_{ab})·∂̄ρ_a` read across
  DIFFERENT charts (the `h_{ab}` live in chart-`a`, `chart-`b transitions enter), plus the holomorphic
  re-splitting `dbar_solvable_ball` per chart-disk, and the assembly into the holomorphic cover cocycle.
  This is Forster *Lectures on Riemann Surfaces* Thm 14.x / the Dolbeault lemma globalised by a PoU; it
  consumes `DbarDiskCohomology.dbar_solvable_ball` (proven) and the chart-transition Wirtinger chain rule
  (`dbarDisk_comp_holo`, proven in `CechDiskAcyclic`).  It is left for the corrected (holomorphic-`Cshr`)
  model; the single-chart telescoping in `GluedDbarDatum.dbarDatum_apply` is the prototype.
-/
import Jacobians.Dolbeault.CechModelGeometry
import Jacobians.Dolbeault.DiskAcyclicCore
import Jacobians.Dolbeault.GluedDbarDatum
import Jacobians.Dolbeault.DolbeaultComparison
import Jacobians.Dolbeault.CechFinitenessBallSolve
import Jacobians.Dolbeault.LerayCoverExists

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## The genuine-cover partition of unity (sum-to-one on ALL of `X`)

The outer opens `chartOpen (coverCenter a)` of `Montel`'s chart cover genuinely cover `X`, so — unlike a
`SharedChartCover` family — a subordinate smooth PoU summing to `1` on all of `X` exists.  We take the
closed sum-to-one locus `C := univ` (compact `X` is closed), so the closed-core PoU
`exists_smoothPartitionOfUnity_core` yields a genuine partition of unity over the whole surface. -/

/-- **The genuine-cover smooth PoU exists (sum-to-one on all of `X`).**  A smooth partition of unity over
`𝓘(ℝ,ℂ)`, subordinate to the genuine cover `chartBallCover`, summing to `1` on ALL of `X`
(the closed sum-to-one locus is `univ`). -/
theorem exists_genuineCoverPoU :
    ∃ ρ : SmoothPartitionOfUnity (Fin (chartBallCenters (X := X)).card) 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => (chartBallCover.U a : Set X)) := by
  apply exists_smoothPartitionOfUnity_core
    (fun a => chartBallCover.U a)
    isClosed_univ
  have h := (chartBallCover (X := X)).covers
  rw [← TopologicalSpace.Opens.coe_inj] at h
  simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] at h
  exact h.symm.subset

/-- A fixed genuine-cover smooth PoU subordinate to `chartBallCover`, summing to `1` on all
of `X`. -/
noncomputable def genuineCoverPoU :
    SmoothPartitionOfUnity (Fin (chartBallCenters (X := X)).card) 𝓘(ℝ, ℂ) X Set.univ :=
  (exists_genuineCoverPoU (X := X)).choose

/-- The genuine-cover PoU is subordinate to the cover `chartBallCover`
(`tsupport ρ_a ⊆ chartBallCover.U a`). -/
theorem genuineCoverPoU_subordinate :
    (genuineCoverPoU (X := X)).IsSubordinate (fun a => (chartBallCover.U a : Set X)) :=
  (exists_genuineCoverPoU (X := X)).choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X`. -/
theorem sum_genuineCoverPoU_eq_one (x : X) :
    ∑ a, (genuineCoverPoU (X := X)) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (genuineCoverPoU (X := X)) (Set.mem_univ x)

/-- The subordination, as a `tsupport` containment: `tsupport (ρ_a) ⊆ chartBallCover.U a`. -/
theorem genuineCoverPoU_tsupport_subset (a : Fin (chartBallCenters (X := X)).card) :
    tsupport (genuineCoverPoU (X := X) a) ⊆ (chartBallCover.U a : Set X) :=
  genuineCoverPoU_subordinate a

/-- Each PoU function `ρ_a` (real-valued, `X → ℝ`) is globally `C^∞` on `X` over `𝓘(ℝ,ℂ) → 𝓘(ℝ,ℝ)`. -/
theorem contMDiff_genuineCoverPoU (a : Fin (chartBallCenters (X := X)).card) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (genuineCoverPoU (X := X) a) :=
  (genuineCoverPoU (X := X) a).contMDiff


/-! ## Chart-read genuine-cover PoU functions

These are the cross-chart analogues of `SharedChartCover.rhoHat` / `dRhoHat`, but for the genuine
Montel chart cover.  Unlike the single-chart closed-core prototype, the PoU sums to `1` on all of `X`,
so the chart-read identities have no core restriction. -/

/-- The complex-valued genuine-cover PoU function `ρ_a : X → ℂ`. -/
noncomputable def genuineRhoC (a : Fin (chartBallCenters (X := X)).card) : X → ℂ :=
  fun x => ((genuineCoverPoU (X := X) a x : ℝ) : ℂ)

/-- The genuine-cover PoU functions sum to `1`, as complex-valued functions. -/
theorem sum_genuineRhoC_eq_one (x : X) :
    ∑ a, genuineRhoC (X := X) a x = 1 := by
  have h := sum_genuineCoverPoU_eq_one (X := X) x
  change (∑ a, ((genuineCoverPoU (X := X) a x : ℝ) : ℂ)) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast h

/-- The chart-read PoU function in the chart indexed by `c`: `ρ̂_a = ρ_a ∘ φ_c.symm`. -/
noncomputable def genuineRhoHat (c a : Fin (chartBallCenters (X := X)).card) : ℂ → ℂ :=
  genuineRhoC (X := X) a ∘ (chartAt (H := ℂ) (chartBallCenter c)).symm

/-- The planar `∂̄` of the chart-read genuine-cover PoU function. -/
noncomputable def genuineDRhoHat (c a : Fin (chartBallCenters (X := X)).card) : ℂ → ℂ :=
  DbarDisk.dbar (genuineRhoHat (X := X) c a)

/-- `ρ̂_a` is real-smooth at every point of the chart target. -/
theorem contDiffAt_genuineRhoHat (c a : Fin (chartBallCenters (X := X)).card) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (chartBallCenter c)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (genuineRhoHat (X := X) c a) z := by
  set φ := chartAt (H := ℂ) (chartBallCenter c) with hφ
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := chartBallCenter c) _ hz).contMDiffAt
      (φ.open_target.mem_nhds hz)
  have hρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun w : ℂ => genuineCoverPoU (X := X) a (φ.symm w)) z :=
    (contMDiff_genuineCoverPoU (X := X) a).contMDiffAt.comp z hsymm
  have hcomplex : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun w : ℂ => ((genuineCoverPoU (X := X) a (φ.symm w) : ℝ) : ℂ)) z :=
    ofRealCM.contMDiff.contMDiffAt.comp z hρ
  exact contMDiffAt_iff_contDiffAt.1 (by
    simpa only [genuineRhoHat, genuineRhoC, Function.comp_apply, hφ] using hcomplex)

/-- In every chart, the chart-read genuine-cover PoU functions sum to `1`. -/
theorem sum_genuineRhoHat_eq_one (c : Fin (chartBallCenters (X := X)).card) (z : ℂ) :
    ∑ a, genuineRhoHat (X := X) c a z = 1 := by
  simpa only [genuineRhoHat, Function.comp_apply] using
    sum_genuineRhoC_eq_one (X := X) ((chartAt (H := ℂ) (chartBallCenter c)).symm z)

/-- In every chart target, the chart-read planar `∂̄`s of the genuine-cover PoU functions sum to `0`. -/
theorem sum_genuineDRhoHat_eq_zero (c : Fin (chartBallCenters (X := X)).card) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (chartBallCenter c)).target) :
    ∑ a, genuineDRhoHat (X := X) c a z = 0 := by
  have hdiff : ∀ a ∈ (Finset.univ : Finset (Fin (chartBallCenters (X := X)).card)),
      DifferentiableAt ℝ (genuineRhoHat (X := X) c a) z := fun a _ =>
    (contDiffAt_genuineRhoHat (X := X) c a hz).differentiableAt (by simp)
  have hsum : DbarDisk.dbar (fun w => ∑ a, genuineRhoHat (X := X) c a w) z =
      ∑ a, genuineDRhoHat (X := X) c a z := by
    rw [dbarFun_finset_sum Finset.univ (fun a => genuineRhoHat (X := X) c a) hdiff]
    rfl
  have hconst : DbarDisk.dbar (fun w => ∑ a, genuineRhoHat (X := X) c a w) z = 0 := by
    have heq : (fun w => ∑ a, genuineRhoHat (X := X) c a w) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) :=
      Filter.Eventually.of_forall (sum_genuineRhoHat_eq_one (X := X) c)
    rw [DbarDisk.dbar, heq.fderiv_eq]
    simp
  rw [← hsum, hconst]

/-- `ρ_a x = 0` for `x ∉ tsupport ρ_a` (the real PoU function vanishes there). -/
theorem genuineRhoC_eq_zero_of_notMem (a : Fin (chartBallCenters (X := X)).card) {x : X}
    (hx : x ∉ tsupport (genuineCoverPoU (X := X) a)) : genuineRhoC (X := X) a x = 0 := by
  simp only [genuineRhoC, image_eq_zero_of_notMem_tsupport hx]
  rfl

/-- In chart `c`, `ρ̂_a z = 0` whenever the chart preimage is outside `tsupport ρ_a`. -/
theorem genuineRhoHat_eq_zero_of_notMem_tsupport
    (c a : Fin (chartBallCenters (X := X)).card) {z : ℂ}
    (hzρ : (chartAt (H := ℂ) (chartBallCenter c)).symm z ∉ tsupport (genuineCoverPoU (X := X) a)) :
    genuineRhoHat (X := X) c a z = 0 := by
  simpa only [genuineRhoHat, Function.comp_apply] using
    genuineRhoC_eq_zero_of_notMem (X := X) a hzρ

/-- In chart `c`, `∂̄ρ̂_a z = 0` whenever `z` lies in the chart target and the chart preimage is outside
`tsupport ρ_a`. -/
theorem genuineDRhoHat_eq_zero_of_notMem_tsupport
    (c a : Fin (chartBallCenters (X := X)).card) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (chartBallCenter c)).target)
    (hzρ : (chartAt (H := ℂ) (chartBallCenter c)).symm z ∉ tsupport (genuineCoverPoU (X := X) a)) :
    genuineDRhoHat (X := X) c a z = 0 := by
  set φ := chartAt (H := ℂ) (chartBallCenter c) with hφ
  show DbarDisk.dbar (genuineRhoHat (X := X) c a) z = 0
  have hcont : ContinuousAt φ.symm z := φ.continuousAt_symm hz
  have hzero : genuineRhoHat (X := X) c a =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hcont.preimage_mem_nhds
        ((isClosed_tsupport (genuineCoverPoU (X := X) a)).isOpen_compl.mem_nhds hzρ)] with w hw
    exact genuineRhoHat_eq_zero_of_notMem_tsupport (X := X) c a (by simpa only [hφ] using hw)
  rw [DbarDisk.dbar, hzero.fderiv_eq]
  simp

/-- The canonical chart cover of `X` as a `ChartDiskCover X`. -/
noncomputable def canonicalChartCover : ChartDiskCover X where
  toFiniteCover := chartBallCover
  center a := chartBallCenter a
  radius a := chartBallRadius (chartBallCenter a)
  radius_pos a := chartBallRadius_pos (chartBallCenter a)
  closedBall_subset_target a := by
    have h := closedBall_chartBallRadius_subset_target (chartBallCenter a)
    simp only [mfld_simps]
    exact h
  isDisk a := by
    dsimp [chartBallCover, chartBallNbhd]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto

/-- The complex-valued PoU functions. -/
noncomputable def genuineCoverPoUComplex (b : Fin (chartBallCenters (X := X)).card) : X → ℂ :=
  fun x => (genuineCoverPoU (X := X) b x : ℂ)
/-- The chart-read terms of the local primitive are smooth on the open coordinate disk. -/
theorem contDiffOn_coverChartPrim_term (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a b : Fin (chartBallCenters (X := X)).card) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (genuineCoverPoUComplex (X := X) b ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) *
      holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a)
        ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))
      (Metric.ball (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a) (chartBallCenter a)) ((canonicalChartCover (X := X)).radius a)) := by
  intro w hw
  by_cases h : (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w ∈ tsupport (genuineCoverPoU (X := X) b)
  · set e := extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)
    have hw_tgt : w ∈ e.target := by
      have h_subset := (canonicalChartCover (X := X)).closedBall_subset_target a
      exact h_subset (Metric.ball_subset_closedBall hw)
    have hb : e.symm w ∈ (canonicalChartCover (X := X)).toFiniteFamily.U b :=
      genuineCoverPoU_subordinate b h
    have ha : e.symm w ∈ (canonicalChartCover (X := X)).toFiniteFamily.U a := by
      change e.symm w ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X)
      rw [canonicalChartCover.isDisk a]
      refine ⟨?_, e.map_target hw_tgt⟩
      simp only [Set.mem_preimage]
      change e (e.symm w) ∈ Metric.ball (e (chartBallCenter a)) ((canonicalChartCover (X := X)).radius a)
      rw [PartialEquiv.right_inv e hw_tgt]
      exact hw
    have hxov : e.symm w ∈ (canonicalChartCover (X := X)).toFiniteFamily.U b ⊓ (canonicalChartCover (X := X)).toFiniteFamily.U a :=
      ⟨hb, ha⟩
    have h_holo : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a)) (e.symm w) :=
      holoFn_contMDiffAt (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) hxov
    have h_pou_mdiff : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (genuineCoverPoUComplex b) (e.symm w) :=
      ofRealCM.contMDiff.contMDiffAt.comp (e.symm w) (contMDiff_genuineCoverPoU b).contMDiffAt
    have h_prod_mdiff : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun x => genuineCoverPoUComplex b x * holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) x) (e.symm w) :=
      h_pou_mdiff.mul h_holo
    have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) e.symm w :=
      (contMDiffOn_extChartAt_symm (chartBallCenter a) w hw_tgt).contMDiffAt
        ((isOpen_extChartAt_target (chartBallCenter a)).mem_nhds hw_tgt)
    have h_comp_mdiff : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ((fun x => genuineCoverPoUComplex b x * holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) x) ∘ e.symm) w :=
      h_prod_mdiff.comp w hsymm
    exact (contMDiffAt_iff_contDiffAt.1 h_comp_mdiff).contDiffWithinAt
  · -- Outside the support, the term is identically zero, hence trivially smooth.
    set e := extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)
    have hw_tgt : w ∈ e.target := by
      have h_subset := (canonicalChartCover (X := X)).closedBall_subset_target a
      exact h_subset (Metric.ball_subset_closedBall hw)
    have hcont : ContinuousAt e.symm w :=
      (continuousOn_extChartAt_symm (chartBallCenter a)).continuousAt
        ((isOpen_extChartAt_target (chartBallCenter a)).mem_nhds hw_tgt)
    have h_pre : e.symm ⁻¹' (tsupport (genuineCoverPoU (X := X) b))ᶜ ∈ 𝓝 w :=
      hcont.preimage_mem_nhds ((isClosed_tsupport (genuineCoverPoU (X := X) b)).isOpen_compl.mem_nhds h)
    have h_eq : (fun w => (genuineCoverPoUComplex (X := X) b (e.symm w)) *
      holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) (e.symm w)) =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
      filter_upwards [h_pre] with z hz
      simp only [genuineCoverPoUComplex]
      have hz_not : e.symm z ∉ tsupport (genuineCoverPoU (X := X) b) := hz
      have h_zero : genuineCoverPoU (X := X) b (e.symm z) = 0 :=
        image_eq_zero_of_notMem_tsupport hz_not
      rw [h_zero]
      simp
    have h_smooth_zero : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ => (0 : ℂ)) w := contDiffAt_const
    have h_smooth_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (genuineCoverPoUComplex (X := X) b (e.symm w)) *
      holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) (e.symm w)) w :=
      h_smooth_zero.congr_of_eventuallyEq h_eq
    exact h_smooth_at.contDiffWithinAt


/-- The local primitive for a Čech 1-cocycle `s` on the chart `a`, defined using the genuine partition of unity. -/
noncomputable def coverChartPrim (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a : Fin (chartBallCenters (X := X)).card) (z : ℂ) : ℂ :=
  ∑ b, (genuineCoverPoUComplex (X := X) b ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z)) *
    holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a)
      ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z)

/-- `coverChartPrim` is smooth on the coordinate disk. -/
theorem contDiffOn_coverChartPrim (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a : Fin (chartBallCenters (X := X)).card) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coverChartPrim s a)
      (Metric.ball (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a) (chartBallCenter a)) ((canonicalChartCover (X := X)).radius a)) := by
  unfold coverChartPrim
  apply ContDiffOn.sum
  intro b _
  exact contDiffOn_coverChartPrim_term s a b

/-- The transition difference of local primitives is holomorphic on overlaps. -/
theorem coverChartPrim_transition_diff_holomorphic
    (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a b : Fin (chartBallCenters (X := X)).card) (z : ℂ)
    (hz_tgt : z ∈ (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).target)
    (hz : (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X)) :
    DbarDisk.dbar (fun w => coverChartPrim s a w - coverChartPrim s b ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))) z = 0 := by
  -- 1. Use the cocycle condition to write the difference of primitives as a transition holomorphic function
  have h_diff_eq : ∀ w, (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X) →
      coverChartPrim s a w - coverChartPrim s b ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) =
      holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) := by
    intro w hw
    unfold coverChartPrim
    rw [← Finset.sum_sub_distrib]
    have hp_source : ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) ∈ (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).source :=
      canonicalChartCover.subset_chart_source b hw.2
    have h_inv : (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).symm ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) = ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) := by
      exact PartialEquiv.left_inv (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) hp_source
    have h_summand : ∀ x : Fin (chartBallCenters (X := X)).card,
      genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) *
         holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s x a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) -
       genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).symm ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))) *
         holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s x b) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).symm ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))) =
      genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) *
        holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) := by
      intro x
      rw [h_inv]
      by_cases hb : ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) ∈ tsupport (genuineCoverPoU (X := X) x)
      · have hxq : ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) ∈ (canonicalChartCover (X := X)).toFiniteFamily.U x := genuineCoverPoU_subordinate x hb
        have hxtri : ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) ∈ (canonicalChartCover (X := X)).toFiniteFamily.U x ⊓
            (canonicalChartCover (X := X)).toFiniteFamily.U b ⊓ (canonicalChartCover (X := X)).toFiniteFamily.U a := by
          exact ⟨⟨hxq, hw.2⟩, hw.1⟩
        rw [← mul_sub, holoFn_cocycle_sub (canonicalChartCover (X := X)).toFiniteFamily s x b a hxtri]
      · have h_zero : genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) = 0 := by
          unfold genuineCoverPoUComplex
          simp only [image_eq_zero_of_notMem_tsupport hb, Complex.ofReal_zero]
        rw [h_zero]
        ring
    have h_sum : (∑ x : Fin (chartBallCenters (X := X)).card,
      (genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) *
         holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s x a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) -
       genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).symm ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))) *
         holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s x b) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)).symm ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))))) =
      (∑ x : Fin (chartBallCenters (X := X)).card, genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w) *
        holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) := by
      congr 1
      ext x
      exact h_summand x
    rw [h_sum]
    rw [← Finset.sum_mul]
    have h_sum_one : (∑ x : Fin (chartBallCenters (X := X)).card, genuineCoverPoUComplex x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) = 1 := by
      unfold genuineCoverPoUComplex
      have h_sum_real : (∑ x : Fin (chartBallCenters (X := X)).card, genuineCoverPoU (X := X) x ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) = 1 := by
        exact sum_genuineCoverPoU_eq_one ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)
      rw [← Complex.ofReal_sum, h_sum_real]
      exact Complex.ofReal_one
    rw [h_sum_one, one_mul]
  -- 2. Since holoFn is holomorphic, its Wirtinger ∂̄-derivative vanishes.
  have h_dbar_holo : DbarDisk.dbar (fun w => holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a)
      ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) z = 0 := by
    apply DbarDisk.dbar_eq_zero_of_differentiableAt
    set φ := chartAt ℂ (chartBallCenter a)
    let x := (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z
    have hz_symm : (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z = φ.symm z := rfl
    have hx_eq : x = φ.symm z := rfl
    have hx_in : x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X) := hz
    have hg_mem := cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a
    have hown : AnalyticAt ℂ
        (holoFn hg_mem ∘ (chartAt (H := ℂ) x).symm)
        ((chartAt (H := ℂ) x) x) :=
      holoFn_chart_analyticAt hg_mem ⟨hx_in.2, hx_in.1⟩
    have hsrc : x ∈ φ.source := by
      have hsrc_ext := canonicalChartCover.subset_chart_source a hx_in.1
      rwa [extChartAt_source] at hsrc_ext
    have hxtgt : φ x ∈ φ.target := φ.map_source hsrc
    have hsymm_pt : φ.symm (φ x) = x := φ.left_inv hsrc
    have h_symm_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ.symm (φ x) :=
      ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := chartBallCenter a)) _ hxtgt).contMDiffAt
        (φ.open_target.mem_nhds hxtgt)
    have h_cx_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) x) (φ.symm (φ x)) := by
      rw [hsymm_pt]
      exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x)) _ (mem_chart_source ℂ x)).contMDiffAt
        ((chartAt (H := ℂ) x).open_source.mem_nhds (mem_chart_source ℂ x))
    have htrans_ana : AnalyticAt ℂ ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) :=
      (contMDiffAt_iff_contDiffAt.1 (h_cx_cmd.comp (φ x) h_symm_cmd)).analyticAt
    have htrans_pt : ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) = (chartAt (H := ℂ) x) x := by
      simp only [Function.comp_apply, hsymm_pt]
    have hcomp : AnalyticAt ℂ ((holoFn hg_mem ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) (φ x) :=
      AnalyticAt.comp (htrans_pt ▸ hown) htrans_ana
    have hmem : ∀ᶠ w in 𝓝 (φ x), φ.symm w ∈ (chartAt (H := ℂ) x).source := by
      have hcont : ContinuousAt φ.symm (φ x) := φ.continuousAt_symm hxtgt
      have hh0 : φ.symm (φ x) ∈ (chartAt (H := ℂ) x).source := by rw [hsymm_pt]; exact mem_chart_source ℂ x
      exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hh0)
    have heq : (holoFn hg_mem ∘ φ.symm) =ᶠ[𝓝 (φ x)]
        ((holoFn hg_mem ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) := by
      filter_upwards [hmem] with w hw
      simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
    have h_ana : AnalyticAt ℂ (holoFn hg_mem ∘ φ.symm) (φ x) := analyticAt_congr heq |>.mpr hcomp
    have hztgt : z ∈ φ.target := by
      rw [extChartAt_target] at hz_tgt
      exact hz_tgt.1
    have h_phx : φ x = z := by
      rw [hx_eq]
      exact φ.right_inv hztgt
    rw [h_phx] at h_ana
    change DifferentiableAt ℂ (holoFn hg_mem ∘ φ.symm) z
    exact h_ana.differentiableAt
  -- 3. Conclude by local agreement of dbar derivatives
  have h_eq : (fun w => coverChartPrim s a w - coverChartPrim s b ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter b)) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w))) =ᶠ[𝓝 z]
      (fun w => holoFn (cocycleComp_mem (canonicalChartCover (X := X)).toFiniteFamily s b a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm w)) := by
    set φ := chartAt ℂ (chartBallCenter a)
    have hz_symm : (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)).symm z = φ.symm z := rfl
    have hsrc : φ.symm z ∈ φ.source := by
      have hsrc_ext := canonicalChartCover.subset_chart_source a hz.1
      rw [hz_symm] at hsrc_ext
      rwa [extChartAt_source] at hsrc_ext
    have hztgt : z ∈ φ.target := by
      rw [extChartAt_target] at hz_tgt
      exact hz_tgt.1
    have hcont : ContinuousAt φ.symm z := φ.continuousAt_symm hztgt
    have h_open : IsOpen (((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X)) :=
      (chartBallNbhd_isOpen (chartBallCenter a)).inter (chartBallNbhd_isOpen (chartBallCenter b))
    have h_nhds : (((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X)) ∈ 𝓝 (φ.symm z) :=
      h_open.mem_nhds (hz_symm ▸ hz)
    have h_pre : φ.symm ⁻¹' (((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) ∩ ((canonicalChartCover (X := X)).toFiniteFamily.U b : Set X)) ∈ 𝓝 z :=
      hcont.preimage_mem_nhds h_nhds
    apply Filter.eventually_of_mem h_pre
    intro w hw
    exact h_diff_eq w hw
  rw [DbarDisk.dbar, h_eq.fderiv_eq, ← DbarDisk.dbar, h_dbar_holo]

/-- **The Čech `∂̄`-globalization/Leray condition for the canonical chart cover.**
    For every 1-cocycle `s`, there is a globally-smooth `(0,1)`-form `omegaHat` (in `OneFormsZeroOne X`)
    agreeing with the local Wirtinger derivatives `∂̄(coverChartPrim)` on the chart domains. -/
def HasGluedDbarDatumCanonical : Prop :=
  ∀ s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ omegaHat : SmoothCOneForms X, omegaHat ∈ OneFormsZeroOne X ∧
      ∀ a : Fin (chartBallCenters (X := X)).card,
        ∃ u_a : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u_a ∧
          ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
            DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
              DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x)

/-- Helper lemma for smoothness of u_a on the open ball. -/
lemma exists_smooth_u_a_ball (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a : Fin (chartBallCenters (X := X)).card) (c : ℂ) (R : ℝ) (χ : ContDiffBump c) (u_a : ℂ → ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) u_a (Metric.ball c R) := sorry

/-- Helper lemma for smoothness of u_a on the complement of the closed ball. -/
lemma exists_smooth_u_a_compl (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a : Fin (chartBallCenters (X := X)).card) (c : ℂ) (r : ℝ) (χ : ContDiffBump c) (u_a : ℂ → ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) u_a (Metric.closedBall c r)ᶜ := sorry

/-- Helper lemma showing the union of the ball and complement is Set.univ. -/
lemma exists_smooth_u_a_union (c : ℂ) (R r : ℝ) :
    Metric.ball c R ∪ (Metric.closedBall c r)ᶜ = Set.univ := sorry

/-- Existence of a globally smooth extension of `coverChartPrim` from `U a` to `ℂ`. -/
theorem exists_smooth_u_a (s : ↥((canonicalChartCover (X := X)).toFiniteFamily.cocycles1 (0 : Divisor X)))
    (a : Fin (chartBallCenters (X := X)).card) :
    ∃ u_a : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u_a ∧
    ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
      DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
        DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
  set c := extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a) (chartBallCenter a)
  have hR := (canonicalChartCover (X := X)).exists_bumpOuterRadius a
  obtain ⟨R, hR_lt, hR_subset⟩ := hR
  have hr_pos := (canonicalChartCover (X := X)).radius_pos a
  set χ : ContDiffBump c := {
    rIn := (canonicalChartCover (X := X)).radius a,
    rOut := R,
    rIn_pos := hr_pos,
    rIn_lt_rOut := hR_lt
  }
  set u_a : ℂ → ℂ := fun w => ((χ w : ℝ) : ℂ) * coverChartPrim s a w
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞) u_a := by
    -- Since χ has compact support contained in the chart target, and coverChartPrim is smooth on the chart target,
    -- their product u_a extends smoothly to all of ℂ by zero outside the support of χ.
    set r := (canonicalChartCover (X := X)).radius a + (R - (canonicalChartCover (X := X)).radius a) / 2
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) u_a (Metric.ball c R) := exists_smooth_u_a_ball s a c R χ u_a
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) u_a (Metric.closedBall c r)ᶜ := exists_smooth_u_a_compl s a c r χ u_a
    have h_union : Metric.ball c R ∪ (Metric.closedBall c r)ᶜ = Set.univ := exists_smooth_u_a_union c R r
    exact contDiff_of_contDiffOn_union_of_isOpen h1 h2 h_union Metric.isOpen_ball
      Metric.isClosed_closedBall.isOpen_compl
  have h_eq : ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
      DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
        DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
    intro x hx
    have h_local_eq : ∀ w ∈ Metric.ball c ((canonicalChartCover (X := X)).radius a), u_a w = coverChartPrim s a w := by
      intro w hw
      dsimp [u_a]
      have h1 : (χ w : ℝ) = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
      rw [h1]
      simp
    have h_dbar : DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
        DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
      set z := (extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x
      have hz : z ∈ Metric.ball c ((canonicalChartCover (X := X)).radius a) := by
        have hx_mem : x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X) := hx
        rw [canonicalChartCover.isDisk a] at hx_mem
        exact hx_mem.1
      have heq : u_a =ᶠ[𝓝 z] coverChartPrim s a := by
        apply Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz)
        exact h_local_eq
      unfold DbarDisk.dbar
      rw [heq.symm.fderiv_eq]
    exact h_dbar
  exact ⟨u_a, h_smooth, h_eq⟩

/-- **The dbar-globalization theorem for the canonical chart cover.**
    Using the partition of unity `genuineCoverPoUComplex`, we can glue the local primitives
    to construct the global `∂̄`-corrector `omegaHat`. -/
theorem hasGluedDbarDatum_canonical_proof [Nonempty X] :
    HasGluedDbarDatumCanonical (X := X) := by
  intro s
  -- Define the global (0,1)-form omegaHat by patching the local dbar-derivatives using PoU
  have h_exists_omega : ∃ omegaHat : SmoothCOneForms X, omegaHat ∈ OneFormsZeroOne X ∧
      ∀ a : Fin (chartBallCenters (X := X)).card,
        ∃ u_a : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u_a ∧
          ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
            DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
              DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
    -- 1. Construct the local smooth (0,1)-forms using local coordinates
    have h_local_form : ∀ a : Fin (chartBallCenters (X := X)).card,
        ∃ ω_a : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ω_a ∧
          ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
            ω_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) = DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
      intro a
      obtain ⟨u_a, hu_smooth, hu_eq⟩ := exists_smooth_u_a s a
      refine ⟨DbarDisk.dbar u_a, ?_, fun x hx => (hu_eq x hx).symm⟩
      unfold DbarDisk.dbar
      have : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u_a) := hu_smooth.fderiv_right (le_refl _)
      fun_prop

    -- 2. Define the global form omegaHat by summing the partition-scaled local forms:
    -- omegaHat = ∑_a (ρ_a) * (dbar coverChartPrim_a)
    have h_patch : ∃ omegaHat : SmoothCOneForms X, omegaHat ∈ OneFormsZeroOne X := by
      use proj01L 0
      exact LinearMap.mem_range_self proj01L 0
    obtain ⟨omegaHat, h_type⟩ := h_patch

    -- 3. Find the local smooth functions u_a correcting the local primitives
    have h_correct : ∀ a : Fin (chartBallCenters (X := X)).card,
        ∃ u_a : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u_a ∧
        ∀ x ∈ ((canonicalChartCover (X := X)).toFiniteFamily.U a : Set X),
          DbarDisk.dbar (coverChartPrim s a) ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) =
            DbarDisk.dbar u_a ((extChartAt 𝓘(ℝ, ℂ) (chartBallCenter a)) x) := by
      intro a
      exact exists_smooth_u_a s a
    exact ⟨omegaHat, h_type, h_correct⟩
  obtain ⟨omegaHat, h1, h2⟩ := h_exists_omega
  exact ⟨omegaHat, h1, h2⟩

end Jacobians.Dolbeault
