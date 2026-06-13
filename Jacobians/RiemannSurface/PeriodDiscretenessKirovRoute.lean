/-
# Period-lattice discreteness — the Kirov dissection-free route (K-LITE lane)

Target (TR-DISC): `DiscreteTopology (loopPeriodLattice x₀ b)` for any basis
`b` of OUR `HolomorphicOneForm X`, with NO cycle-basis axiom
(`AX_PeriodCycleBasis` does not enter), following the dissection-free
strategy of Forster §21.3–21.4 as realized in R. Kirov's
`rkirov/jacobian-claude` @ `906335f` (Apache 2.0; ideas cited per
docstring, implementation ours over OUR structures via
`Jacobians.Bridge.bridgeKDFormEquiv`).

This file is the K-LITE ladder umbrella-leaf
(`docs/planning/KIROV_214_STUDY.md` §4). Rungs:

* **K1 (this section, DONE):** base points — the chart-centre evaluation
  functional `formEvalSelf`, the Forster 21.3 kernel-drop induction, and
  the invertible `g × g` evaluation matrix `jacobiEvalMatrix b a`
  (`exists_jacobiBasePoints_det_ne_zero`).
* K2: the local Jacobi map and its strict Fréchet derivative (openness
  window).
* K3: the Abel-engine local normal form at boundary points.
* K4–K5: isolated zero of the lattice via the engine + residue theorem.
* K6: `DiscreteTopology (loopPeriodLattice x₀ b)` and the #208 packaging.

The identity-theorem atom is the Dolbeault port's
`Jacobians.Dolbeault.exists_localRep_self_ne_zero`
(`KirovDolbeault/Dolbeault/FormCoeff.lean`, kernel-verified standard-3),
transported to OUR forms across `bridgeKDFormEquiv`.
-/
import Jacobians.RiemannSurface.PeriodDiscreteness
import Jacobians.Bridge.KirovDolbeaultTrace
import Jacobians.Bridge.KirovDolbeaultPeriods
import KirovDolbeault.Dolbeault.FormCoeff
import KirovDolbeault.Dolbeault.AbelSubsetEngineArc
import KirovDolbeault.Dolbeault.LerayCoverExists
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealSlitGeometry
import KirovDolbeault.Dolbeault.TailFrameWitness
import KirovDolbeault.OfCurveAnalyticitySkeleton
import KirovDolbeault.Abel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## K1 — Forster 21.3: base points with invertible evaluation matrix

Idea source: Kirov `906335f`, `Jacobians/JacobiBasePoints.lean` (Apache
2.0); restated over OUR `HolomorphicOneForm X` with the evaluation read
through the form bridge. -/

/-- **Evaluation of one of OUR holomorphic 1-forms at a point**, as a
ℂ-linear functional: the chart-centre coefficient `localRep α̂ a a` of the
bridged Dolbeault-port form `α̂ = bridgeKDFormEquiv α`. Its vanishing is
the chart-invariant meaning of "`α(a) = 0`" (the tangent fibre is
1-dimensional). [Idea: Kirov `JacobiBasePoints.lean:40`.] -/
def formEvalSelf (a : X) : HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun α := Jacobians.Montel.localRep (Jacobians.Bridge.bridgeKDFormEquiv α) a a
  map_add' α η := by
    rw [map_add]
    exact Jacobians.Montel.localRep_add _ _ a a
  map_smul' c α := by
    rw [map_smul, RingHom.id_apply]
    exact Jacobians.Montel.localRep_smul c _ a a

omit [Nonempty X] in
@[simp] theorem formEvalSelf_apply (a : X) (α : HolomorphicOneForm X) :
    formEvalSelf a α
      = Jacobians.Montel.localRep (Jacobians.Bridge.bridgeKDFormEquiv α) a a :=
  rfl

/-- **The identity-theorem atom over OUR forms**: a nonzero holomorphic
1-form has a nonzero chart-centre coefficient at SOME point. Transport of
the Dolbeault port's `exists_localRep_self_ne_zero`
(`FormCoeff.lean:77`) across the form bridge. -/
theorem exists_formEvalSelf_ne_zero {α : HolomorphicOneForm X} (hα : α ≠ 0) :
    ∃ a : X, formEvalSelf a α ≠ 0 := by
  have hbne : Jacobians.Bridge.bridgeKDFormEquiv α ≠ 0 := by
    intro h
    exact hα ((LinearEquiv.map_eq_zero_iff _).mp h)
  obtain ⟨a, ha⟩ :=
    Jacobians.Dolbeault.exists_localRep_self_ne_zero
      (Jacobians.Bridge.bridgeKDFormEquiv α) hbne
  exact ⟨a, ha⟩

omit [Nonempty X] in
/-- **One-step kernel drop.** If some `α ∈ V` has `formEvalSelf a α ≠ 0`,
cutting `V` by the kernel of the evaluation at `a` drops the dimension by
exactly one. [Idea: Kirov `JacobiBasePoints.lean:52`; our proof replaces
his rank–nullity on the restricted functional by the submodule splitting
`V = (V ⊓ ker) ⊔ span {α}` with trivial intersection, which sidesteps a
pathological instance-path unification on the `ℂ`-codomain.] -/
theorem finrank_inf_ker_formEvalSelf (V : Submodule ℂ (HolomorphicOneForm X))
    {α : HolomorphicOneForm X} (hαV : α ∈ V) {a : X}
    (hαa : formEvalSelf a α ≠ 0) :
    finrank ℂ ↥(V ⊓ LinearMap.ker (formEvalSelf (X := X) a))
      = finrank ℂ ↥V - 1 := by
  classical
  set W : Submodule ℂ (HolomorphicOneForm X) :=
    V ⊓ LinearMap.ker (formEvalSelf (X := X) a) with hW
  set S : Submodule ℂ (HolomorphicOneForm X) := Submodule.span ℂ {α} with hS
  have hαne : α ≠ 0 := fun h => hαa (h ▸ map_zero (formEvalSelf a))
  -- V splits as W ⊔ span {α}.
  have hsplit : W ⊔ S = V := by
    apply le_antisymm
    · exact sup_le inf_le_left
        ((Submodule.span_singleton_le_iff_mem α V).mpr hαV)
    · intro β hβ
      have hmem : β - (formEvalSelf a β / formEvalSelf a α) • α ∈ W := by
        refine Submodule.mem_inf.mpr ⟨V.sub_mem hβ (V.smul_mem _ hαV), ?_⟩
        rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
          div_mul_cancel₀ _ hαa, sub_self]
      have : β = (β - (formEvalSelf a β / formEvalSelf a α) • α)
          + (formEvalSelf a β / formEvalSelf a α) • α := by abel
      rw [this]
      exact Submodule.add_mem_sup hmem
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self α))
  -- The two pieces intersect trivially: a multiple of α in the kernel is 0.
  have hdisj : W ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro β hβ
    obtain ⟨hβW, hβS⟩ := Submodule.mem_inf.mp hβ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hβS
    have hc : c * formEvalSelf a α = 0 := by
      have := (Submodule.mem_inf.mp hβW).2
      rwa [LinearMap.mem_ker, map_smul, smul_eq_mul] at this
    rcases mul_eq_zero.mp hc with hc0 | h0
    · simp [hc0]
    · exact absurd h0 hαa
  -- Dimension bookkeeping.
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W S
  rw [hsplit, hdisj, finrank_bot, finrank_span_singleton hαne] at hdim
  omega

/-- **The Forster 21.3 induction core**: for every `k ≤ g` there is a
`k`-element set of points whose common evaluation kernel has dimension
exactly `g − k`. [Idea: Kirov `JacobiBasePoints.lean:83`.] -/
theorem exists_finset_formEvalSelf_ker (k : ℕ) (hk : k ≤ genus X) :
    ∃ s : Finset X, s.card = k ∧
      finrank ℂ ↥(⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a))
        = genus X - k := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, Finset.card_empty, ?_⟩
    rw [show (⨅ a ∈ (∅ : Finset X), LinearMap.ker (formEvalSelf (X := X) a)) = ⊤ by
      simp, finrank_top]
    rfl
  | succ n ih =>
    obtain ⟨s, hcard, hdim⟩ := ih (by omega)
    set V : Submodule ℂ (HolomorphicOneForm X) :=
      ⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a) with hV
    -- V is nonzero (its dimension is g − n ≥ 1), so pick 0 ≠ α ∈ V.
    have hVne : V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim
      omega
    obtain ⟨α, hαV, hαne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    -- α has a nonzero coefficient at some point a'.
    obtain ⟨a', ha'eval⟩ := exists_formEvalSelf_ne_zero hαne
    -- a' is new: α's coefficient vanishes at every point of s.
    have ha'new : a' ∉ s := by
      intro hmem
      exact ha'eval ((biInf_le _ hmem : V ≤ LinearMap.ker (formEvalSelf a')) hαV)
    refine ⟨insert a' s, by rw [Finset.card_insert_of_notMem ha'new, hcard], ?_⟩
    rw [Finset.iInf_insert, inf_comm, ← hV,
      finrank_inf_ker_formEvalSelf V hαV ha'eval, hdim]
    omega

/-- **Forster Lemma 21.3** over OUR forms: there are `g` distinct points
`a j` on `X` such that the only holomorphic 1-form whose chart-centre
coefficient vanishes at all of them is the zero form.
[Idea: Kirov `JacobiBasePoints.lean:119`.] -/
theorem exists_jacobiBasePoints :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      ∀ α : HolomorphicOneForm X, (∀ j, formEvalSelf (a j) α = 0) → α = 0 := by
  classical
  obtain ⟨s, hcard, hdim⟩ := exists_finset_formEvalSelf_ker (X := X) (genus X) le_rfl
  rw [Nat.sub_self] at hdim
  have hequiv : Fin (genus X) ≃ ↥s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun j => (hequiv j : X), fun j₁ j₂ h => hequiv.injective (Subtype.ext h), ?_⟩
  intro α hα
  have hmem : α ∈ ⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a) := by
    rw [Submodule.mem_iInf]
    intro b
    rw [Submodule.mem_iInf]
    intro hb
    have h := hα (hequiv.symm ⟨b, hb⟩)
    simpa using h
  have hbot : (⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hdim
  rw [hbot] at hmem
  exact hmem

/-- The `g × g` **evaluation matrix** of a chosen basis `b` of OUR
holomorphic 1-forms at a point family: `A i j = formEvalSelf (a j) (b i)`.
This is the Jacobian matrix of the local Jacobi map (K2) at the base
points. [Idea: Kirov `JacobiBasePoints.lean:150`, with his fixed period
basis replaced by an arbitrary basis `b` — the one `loopPeriodLattice x₀ b`
carries.] -/
def jacobiEvalMatrix (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) : Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Matrix.of fun i j => formEvalSelf (a j) (b i)

omit [Nonempty X] in
@[simp] theorem jacobiEvalMatrix_apply
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (i j : Fin (genus X)) :
    jacobiEvalMatrix b a i j = formEvalSelf (a j) (b i) :=
  rfl

omit [Nonempty X] in
/-- **Rank `g` of the evaluation matrix** (Forster 21.4(a) ingredient): at
a family of base points with the 21.3 property, the evaluation matrix of
any basis is invertible. A nonzero left null vector `v` would make
`α = ∑ v i • b i` a nonzero form whose coefficient vanishes at every
`a j`. [Idea: Kirov `JacobiBasePoints.lean:158`.] -/
theorem jacobiEvalMatrix_det_ne_zero
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    {a : Fin (genus X) → X}
    (ha : ∀ α : HolomorphicOneForm X, (∀ j, formEvalSelf (a j) α = 0) → α = 0) :
    (jacobiEvalMatrix b a).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set α : HolomorphicOneForm X := ∑ i, v i • b i with hα
  have hαeval : ∀ j, formEvalSelf (a j) α = 0 := by
    intro j
    have hvj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hvj
    calc formEvalSelf (a j) α
        = ∑ i, v i * formEvalSelf (a j) (b i) := by
          rw [hα, map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
      _ = 0 := hvj
  have hα0 : α = 0 := ha α hαeval
  apply hvne
  have hindep := (Fintype.linearIndependent_iff.mp b.linearIndependent) v (hα ▸ hα0)
  funext i
  exact hindep i

/-- **K1 packaged** (Forster 21.3 + the 21.4(a) rank statement): for any
basis `b` of OUR holomorphic 1-forms there is a family of `g` distinct
base points at which the evaluation matrix of `b` is invertible.
[Idea: Kirov `JacobiBasePoints.lean:195`.] -/
theorem exists_jacobiBasePoints_det_ne_zero
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      (jacobiEvalMatrix b a).det ≠ 0 := by
  obtain ⟨a, hinj, ha⟩ := exists_jacobiBasePoints (X := X)
  exact ⟨a, hinj, jacobiEvalMatrix_det_ne_zero b ha⟩

/-! ## K2 — Forster 21.4(a): the local Jacobi map and its open image

Idea source: Kirov `906335f`, `Jacobians/JacobiLocalMap.lean` (Apache 2.0);
restated over OUR forms: the chart coefficient/primitive are taken of the
bridged form `bridgeKDFormEquiv (b i)`, and the evaluation matrix is K1's
`jacobiEvalMatrix b a`. The two FTC atoms
(`exists_analytic_primitive_on_ball`, `segmentIntegral_eq_primitive_diff`)
are the Dolbeault port's, generic in the integrand. -/

/-- The chart-coordinate coefficient of one of OUR holomorphic 1-forms in
the canonical chart at `Q₀`: the local representative of the bridged form
at `(chartAt ℂ Q₀).symm z`. [Idea: Kirov `SmoothPathCore.lean:433`.] -/
def formChartCoeff (Q₀ : X) (α : HolomorphicOneForm X) (z : ℂ) : ℂ :=
  Jacobians.Montel.localRep (Jacobians.Bridge.bridgeKDFormEquiv α) Q₀
    ((chartAt (H := ℂ) Q₀).symm z)

omit [Nonempty X] in
/-- The chart coefficient is holomorphic on the chart target (the Montel
analyticity bridge, applied to the bridged form). -/
theorem formChartCoeff_differentiableOn (Q₀ : X) (α : HolomorphicOneForm X) :
    DifferentiableOn ℂ (formChartCoeff Q₀ α) (chartAt (H := ℂ) Q₀).target :=
  (Jacobians.Montel.localRep_analyticOn_chartTarget
    (Jacobians.Bridge.bridgeKDFormEquiv α) Q₀).differentiableOn

omit [Nonempty X] in
/-- At the chart centre, the chart coefficient is the K1 evaluation
functional. -/
theorem formChartCoeff_center (Q₀ : X) (α : HolomorphicOneForm X) :
    formChartCoeff Q₀ α ((chartAt (H := ℂ) Q₀) Q₀) = formEvalSelf Q₀ α := by
  rw [formChartCoeff, (chartAt (H := ℂ) Q₀).left_inv (mem_chart_source ℂ Q₀)]
  rfl

/-- The chart-coordinate primitive `Φ̃_{Q₀}` of one of OUR forms, normalized
to vanish at the chart centre: the straight-segment integral of the chart
coefficient from `z₀ = chartAt Q₀ Q₀` to `z`.
[Idea: Kirov `SmoothPathCore.lean:460`, with `constants = 0`.] -/
def formChartPrimitive (Q₀ : X) (α : HolomorphicOneForm X) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    formChartCoeff Q₀ α
        ((chartAt (H := ℂ) Q₀) Q₀ + (t : ℂ) * (z - (chartAt (H := ℂ) Q₀) Q₀))
      * (z - (chartAt (H := ℂ) Q₀) Q₀)

omit [Nonempty X] in
/-- The chart primitive vanishes at the chart centre (the segment
degenerates). -/
theorem formChartPrimitive_center (Q₀ : X) (α : HolomorphicOneForm X) :
    formChartPrimitive Q₀ α ((chartAt (H := ℂ) Q₀) Q₀) = 0 := by
  rw [formChartPrimitive]
  simp [sub_self, mul_zero]

omit [Nonempty X] in
/-- **Strict differentiability of the chart primitive at the chart
centre**, with derivative the K1 evaluation functional: on a chart ball
the primitive reads `g z − g z₀` for an analytic primitive `g` of the
chart coefficient (FTC on the segment), and the analytic model is
strictly differentiable. [Idea: Kirov `JacobiLocalMap.lean:60,105`,
collapsed into a single strict-derivative lemma.] -/
theorem formChartPrimitive_hasStrictDerivAt_center (Q₀ : X)
    (α : HolomorphicOneForm X) :
    HasStrictDerivAt (formChartPrimitive Q₀ α) (formEvalSelf Q₀ α)
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  classical
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source (mem_chart_source ℂ Q₀)
  obtain ⟨r, hr_pos, hr_subset⟩ :=
    Metric.isOpen_iff.mp (chartAt (H := ℂ) Q₀).open_target _ h_mem
  have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
  have hdiff : DifferentiableOn ℂ (formChartCoeff Q₀ α) (Metric.ball z₀ r) :=
    (formChartCoeff_differentiableOn Q₀ α).mono hr_subset
  obtain ⟨g, hg_deriv, _hg_ana⟩ :=
    Jacobians.OfCurveSkeleton.exists_analytic_primitive_on_ball hdiff
  -- on the ball, the chart primitive is `g z − g z₀`.
  have h_eq : Set.EqOn (formChartPrimitive Q₀ α) (fun z => g z - g z₀)
      (Metric.ball z₀ r) := by
    intro z hz
    have hseg : Set.Icc (0 : ℝ) 1
        ⊆ {t | z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r} := by
      intro t ht
      show z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r
      have h_rewrite : z₀ + (t : ℂ) * (z - z₀) = z₀ + t • (z - z₀) := by
        rw [Complex.real_smul]
      rw [h_rewrite]
      exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz ht
    have hFTC := Jacobians.OfCurveSkeleton.segmentIntegral_eq_primitive_diff
      (c := z₀) (r := r) (a := z₀) (b := z)
      (f := formChartCoeff Q₀ α) (g := g)
      hz₀_mem hz hseg hdiff.continuousOn hg_deriv
    rw [formChartPrimitive, ← hz₀_def]
    exact hFTC
  -- the analytic model has the strict derivative at `z₀`.
  have hgdiff : DifferentiableOn ℂ g (Metric.ball z₀ r) := fun w hw =>
    (hg_deriv w hw).differentiableAt.differentiableWithinAt
  have hga : AnalyticAt ℂ g z₀ :=
    hgdiff.analyticAt (Metric.isOpen_ball.mem_nhds hz₀_mem)
  have hg_strict : HasStrictDerivAt g (formChartCoeff Q₀ α z₀) z₀ := by
    have h := hga.contDiffAt.hasStrictDerivAt (n := ω) (by simp)
    rwa [(hg_deriv z₀ hz₀_mem).deriv] at h
  have h_model : HasStrictDerivAt (fun z => g z - g z₀)
      (formChartCoeff Q₀ α z₀) z₀ := hg_strict.sub_const (g z₀)
  have h_strict : HasStrictDerivAt (formChartPrimitive Q₀ α)
      (formChartCoeff Q₀ α z₀) z₀ := by
    refine h_model.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀_mem] with z hz
    exact (h_eq hz).symm
  rwa [hz₀_def, formChartCoeff_center] at h_strict

/-! ### The local Jacobi map -/

/-- **The local Jacobi map** at a base-point family `a : Fin g → X` for a
basis `b` of OUR forms (Forster 21.4(a)): `G(z)ᵢ = ∑ⱼ Φ̃_{a j}(b i)(z j)`,
each summand read in its own chart coordinate.
[Idea: Kirov `JacobiLocalMap.lean:119`.] -/
def jacobiMap (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (z : Fin (genus X) → ℂ) : Fin (genus X) → ℂ :=
  fun i => ∑ j, formChartPrimitive (a j) (b i) (z j)

/-- The chart-coordinate centre of the local Jacobi map. -/
def jacobiCenter (a : Fin (genus X) → X) : Fin (genus X) → ℂ :=
  fun j => (chartAt (H := ℂ) (a j)) (a j)

omit [Nonempty X] in
/-- The local Jacobi map vanishes at the centre. -/
theorem jacobiMap_center (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) :
    jacobiMap b a (jacobiCenter a) = 0 := by
  funext i
  rw [jacobiMap]
  exact Finset.sum_eq_zero fun j _ => formChartPrimitive_center (a j) (b i)

/-- The Fréchet derivative of the local Jacobi map at the centre: the
continuous linear map `v ↦ (jacobiEvalMatrix b a).mulVec v`, assembled as
a `Pi` of summed coordinate projections.
[Idea: Kirov `JacobiLocalMap.lean:138`.] -/
def jacobiDeriv (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) :
    (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, jacobiEvalMatrix b a i j • ContinuousLinearMap.proj j

omit [Nonempty X] in
@[simp] theorem jacobiDeriv_apply
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (v : Fin (genus X) → ℂ) (i : Fin (genus X)) :
    jacobiDeriv b a v i = ∑ j, jacobiEvalMatrix b a i j * v j := by
  rw [jacobiDeriv, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

omit [Nonempty X] in
/-- **Strict differentiability of the local Jacobi map at the centre**,
with derivative the K1 evaluation matrix: per-summand strict derivatives
composed with coordinate projections, summed, and assembled through `Pi`.
[Idea: Kirov `JacobiLocalMap.lean:152`.] -/
theorem jacobiMap_hasStrictFDerivAt
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) :
    HasStrictFDerivAt (jacobiMap b a) (jacobiDeriv b a) (jacobiCenter a) := by
  rw [show jacobiDeriv b a = ContinuousLinearMap.pi fun i =>
      ∑ j, jacobiEvalMatrix b a i j • ContinuousLinearMap.proj j from rfl]
  apply hasStrictFDerivAt_pi''
  intro i
  rw [ContinuousLinearMap.proj_pi]
  have hfun : (∑ j, fun z : Fin (genus X) → ℂ => formChartPrimitive (a j) (b i) (z j))
      = fun z => jacobiMap b a z i := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rw [← hfun]
  refine HasStrictFDerivAt.sum fun j _ => ?_
  -- the `(i,j)` summand: the chart primitive after the `j`-th projection.
  have houter : HasStrictDerivAt (formChartPrimitive (a j) (b i))
      (jacobiEvalMatrix b a i j) (jacobiCenter a j) :=
    formChartPrimitive_hasStrictDerivAt_center (a j) (b i)
  have hproj : HasStrictFDerivAt (fun z : Fin (genus X) → ℂ => z j)
      (ContinuousLinearMap.proj j) (jacobiCenter a) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (genus X) => ℂ)
      j).hasStrictFDerivAt
  show HasStrictFDerivAt
    ((formChartPrimitive (a j) (b i)) ∘ (fun z : Fin (genus X) → ℂ => z j))
    (jacobiEvalMatrix b a i j • ContinuousLinearMap.proj j) (jacobiCenter a)
  exact houter.comp_hasStrictFDerivAt (jacobiCenter a) hproj

/-! ### The inverse function theorem at a rank-`g` base-point family -/

/-- At a base-point family with invertible evaluation matrix, `jacobiDeriv`
is (the coercion of) a continuous linear equivalence.
[Idea: Kirov `JacobiLocalMap.lean:186`.] -/
def jacobiDerivEquiv (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (ha : (jacobiEvalMatrix b a).det ≠ 0) :
    (Fin (genus X) → ℂ) ≃L[ℂ] (Fin (genus X) → ℂ) :=
  ((jacobiEvalMatrix b a).toLinearEquiv'
    ((jacobiEvalMatrix b a).invertibleOfIsUnitDet
      (isUnit_iff_ne_zero.mpr ha))).toContinuousLinearEquiv

omit [Nonempty X] in
theorem coe_jacobiDerivEquiv (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (ha : (jacobiEvalMatrix b a).det ≠ 0) :
    (jacobiDerivEquiv b a ha : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ))
      = jacobiDeriv b a := by
  ext v i
  show ((jacobiEvalMatrix b a).toLinearEquiv' _) v i = jacobiDeriv b a v i
  rw [jacobiDeriv_apply]
  show (jacobiEvalMatrix b a).mulVec v i = _
  rw [Matrix.mulVec, dotProduct]

omit [Nonempty X] in
/-- **Forster 21.4(a), the open-image conclusion**: at a base-point family
with `det A ≠ 0`, the local Jacobi map sends neighbourhoods of the centre
to neighbourhoods of `0` (`HasStrictFDerivAt.map_nhds_eq_of_equiv`; no
manifold IFT). [Idea: Kirov `JacobiLocalMap.lean:205`.] -/
theorem jacobiMap_map_nhds (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (a : Fin (genus X) → X) (ha : (jacobiEvalMatrix b a).det ≠ 0) :
    Filter.map (jacobiMap b a) (nhds (jacobiCenter a)) = nhds 0 := by
  have hstrict : HasStrictFDerivAt (jacobiMap b a)
      (jacobiDerivEquiv b a ha : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ))
      (jacobiCenter a) := by
    rw [coe_jacobiDerivEquiv]
    exact jacobiMap_hasStrictFDerivAt b a
  have h := hstrict.map_nhds_eq_of_equiv
  rwa [jacobiMap_center b a] at h

/-- **K2 packaged** (Forster 21.4(a)): a base-point family `a` (injective,
invertible evaluation matrix) at which the local Jacobi map has
`G(centre) = 0` and maps every neighbourhood of the centre onto a
neighbourhood of `0 ∈ ℂ^g`. [Idea: Kirov `JacobiLocalMap.lean:219`.] -/
theorem exists_jacobiMap_map_nhds
    (b : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      (jacobiEvalMatrix b a).det ≠ 0 ∧
      jacobiMap b a (jacobiCenter a) = 0 ∧
      ∀ V ∈ nhds (jacobiCenter a),
        jacobiMap b a '' V ∈ nhds (0 : Fin (genus X) → ℂ) := by
  obtain ⟨a, hinj, hdet⟩ := exists_jacobiBasePoints_det_ne_zero b
  refine ⟨a, hinj, hdet, jacobiMap_center b a, fun V hV => ?_⟩
  rw [← jacobiMap_map_nhds b a hdet]
  exact Filter.image_mem_map hV

/-! ## K3 — the engine's centred local normal form at divisor points

The Abel engine (`exists_meromorphic_of_zeroPeriodChain'`) returns `f`
with `div f = ∂c`. The residue read (K5) needs the centred Laurent
normal form `f̂ = (w − w₀)^n · H`, `H(w₀) ≠ 0`, at each point of the
divisor. Rather than replaying Kirov's `exp(−u)·G` construction
(`AbelEngineMeromorphic.lean:83-110`), we DERIVE the normal form from
the port's `orderW`/`orderAtPoint` chain and Mathlib's
`meromorphicOrderAt_eq_int_iff` — the study's "orderW shortcut"
(`docs/planning/KIROV_214_STUDY.md` §4, rung K3 option (ii)). -/

/-- The divisor coefficient is the chart-pullback `untop₀` order
(definitional unfold of `div`/`divViaOrder`/`orderAtPoint`). -/
theorem meromorphicFunction_div_apply (f : _root_.Jacobians.MeromorphicFunction X)
    (a : X) :
    _root_.Jacobians.MeromorphicFunction.div X f a
      = (meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) a).symm)
          ((chartAt (H := ℂ) a) a)).untop₀ := by
  rw [_root_.Jacobians.MeromorphicFunction.div,
    _root_.Jacobians.MeromorphicFunction.divViaOrder,
    Finsupp.ofSupportFinite_coe]
  rfl

/-- **K3 — centred local normal form at a divisor point.** If the divisor
of a meromorphic `f` has nonzero coefficient `n` at `a`, then in the
canonical chart at `a` the function factors on a punctured neighbourhood
of the centre `w₀` as `f̂(w) = (w − w₀)^n · H(w)` with `H` analytic at
`w₀` and `H(w₀) ≠ 0` — the Laurent data the K5 residue read consumes.
Derived from Mathlib's `meromorphicOrderAt_eq_int_iff`; no replay of the
engine's `exp(−u)·G` construction.
[Idea: Kirov `AbelEngineMeromorphic.lean:72-110`, via the `orderW`
shortcut instead of his explicit construction.] -/
theorem meromorphicFunction_normalForm_of_div
    (f : _root_.Jacobians.MeromorphicFunction X) (a : X) {n : ℤ}
    (hdiv : _root_.Jacobians.MeromorphicFunction.div X f a = n) (hn : n ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt (H := ℂ) a) a) ∧
      H ((chartAt (H := ℂ) a) a) ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) a) a),
        f.toFun ((chartAt (H := ℂ) a).symm w)
          = (w - (chartAt (H := ℂ) a) a) ^ n * H w := by
  classical
  rw [meromorphicFunction_div_apply] at hdiv
  -- the `WithTop ℤ` order is exactly `n` (`⊤` would have `untop₀ = 0 ≠ n`).
  have horder : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) a).symm)
      ((chartAt (H := ℂ) a) a) = (n : WithTop ℤ) := by
    cases ho : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) a).symm)
        ((chartAt (H := ℂ) a) a) with
    | top => rw [ho] at hdiv; simp at hdiv; exact absurd hdiv.symm hn
    | coe m =>
      rw [ho] at hdiv
      simp only [WithTop.untop₀_coe] at hdiv
      exact congrArg _ hdiv
  obtain ⟨H, hH_ana, hH_ne, hH_ev⟩ :=
    (meromorphicOrderAt_eq_int_iff (f.meromorphic a)).mp horder
  refine ⟨H, hH_ana, hH_ne, ?_⟩
  filter_upwards [hH_ev] with w hw
  simpa [smul_eq_mul] using hw

/-! ## K4 bricks — segments, loops, and the chain's raw material

Idea source: Kirov `906335f`, `Jacobians/PeriodLatticeDiscrete.lean:87-394`
(Apache 2.0). Over the port's `SmoothOneChain` instead of his `OneChain`:
the segment pieces are the port's zero-velocity chart hops
(`ChartBallPathSmooth`/`zeroVelHop`), valued by the public cell FTC
(`Bridge.lineIntegral_cell_eq_primitive_sub`); the loop pieces are the
smooth representatives of OUR analytic loops
(`Bridge.exists_isClosedSmoothLoop_lineIntegral_eq_developingValue`, #216).
-/

omit [Nonempty X] in
/-- Pairwise-disjoint open neighbourhoods of an injective finite family
(T2 separation, intersected over the off-diagonal pairs).
[Idea: Kirov `PeriodLatticeDiscrete.lean:87`.] -/
theorem exists_pairwise_disjoint_opens {n : ℕ} {a : Fin n → X}
    (ha : Function.Injective a) :
    ∃ O : Fin n → Set X, (∀ j, IsOpen (O j)) ∧ (∀ j, a j ∈ O j) ∧
      ∀ j k, j ≠ k → Disjoint (O j) (O k) := by
  classical
  have hpair : ∀ j k : Fin n, j ≠ k → ∃ uv : Set X × Set X,
      IsOpen uv.1 ∧ IsOpen uv.2 ∧ a j ∈ uv.1 ∧ a k ∈ uv.2 ∧ Disjoint uv.1 uv.2 := by
    intro j k hjk
    obtain ⟨u, v, hu, hv, hau, hav, huv⟩ := t2_separation (fun h => hjk (ha h))
    exact ⟨(u, v), hu, hv, hau, hav, huv⟩
  choose! uv huv1 huv2 hauv havuv hdisj using hpair
  refine ⟨fun j => ⋂ k ∈ Finset.univ.erase j, ((uv j k).1 ∩ (uv k j).2), ?_, ?_, ?_⟩
  · intro j
    refine isOpen_biInter_finset fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact (huv1 j k (Ne.symm hkj)).inter (huv2 k j hkj)
  · intro j
    refine Set.mem_biInter fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact ⟨hauv j k (Ne.symm hkj), havuv k j hkj⟩
  · intro j k hjk
    have hsub1 : (⋂ l ∈ Finset.univ.erase j, ((uv j l).1 ∩ (uv l j).2)) ⊆ (uv j k).1 :=
      fun x hx => (Set.mem_iInter₂.mp hx k
        (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)).1
    have hsub2 : (⋂ l ∈ Finset.univ.erase k, ((uv k l).1 ∩ (uv l k).2)) ⊆ (uv j k).2 :=
      fun x hx => (Set.mem_iInter₂.mp hx j
        (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)).2
    exact Set.disjoint_of_subset hsub1 hsub2 (hdisj j k hjk)

/-- **The coefficient identity**: OUR cocycle coefficient of a form at a
chart-target coordinate is the local representative of the bridged form at
the underlying point. From the bridge round-trip
`inverseForm (bridgeForm form) = form`, whose left side reads the section
in chart coordinates (`sectionCoeff`). -/
theorem coeff_eq_localRep_bridgeKD (α : HolomorphicOneForm X) (x : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    α.coeff x z
      = Jacobians.Montel.localRep (Jacobians.Bridge.bridgeKDFormEquiv α) x
          ((chartAt ℂ x).symm z) := by
  have hround := Jacobians.Bridge.BridgeFormEquiv.inverseForm_bridgeForm
    (X := X) α
  have hz' : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := by
    simpa [extChartAt] using hz
  calc α.coeff x z
      = (Jacobians.Bridge.BridgeFormEquiv.inverseForm
          (Jacobians.Bridge.bridgeForm α)).coeff x z := by rw [hround]
    _ = Jacobians.Bridge.BridgeFormEquiv.sectionCoeff
          (Jacobians.Bridge.bridgeForm α) x z := rfl
    _ = Jacobians.Vendor.Kirov.Montel.localRep (Jacobians.Bridge.bridgeForm α) x
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z) :=
        Jacobians.Bridge.BridgeFormEquiv.sectionCoeff_apply_of_mem _ hz'
    _ = Jacobians.Montel.localRep (Jacobians.Bridge.bridgeKDFormEquiv α) x
          ((chartAt ℂ x).symm z) := by
        rw [show (extChartAt 𝓘(ℂ, ℂ) x).symm z = (chartAt ℂ x).symm z by
          simp [extChartAt]]
        rfl

omit [Nonempty X] in
/-- The chart coefficient of K2 equals OUR cocycle coefficient on the chart
target. -/
theorem formChartCoeff_eq_coeff [Nonempty X] (Q₀ : X) (α : HolomorphicOneForm X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ Q₀).target) :
    formChartCoeff Q₀ α z = α.coeff Q₀ z :=
  (coeff_eq_localRep_bridgeKD α Q₀ hz).symm

omit [Nonempty X] in
/-- `formChartPrimitive` is the endpoint difference of ANY primitive of the
chart coefficient on a chart ball at the centre (FTC on the straight
segment; same mechanism as the K2 strict-derivative lemma). -/
theorem formChartPrimitive_eq_primitive_sub (Q₀ : X) (α : HolomorphicOneForm X)
    {r : ℝ} (hsub : Metric.ball ((chartAt (H := ℂ) Q₀) Q₀) r ⊆ (chartAt ℂ Q₀).target)
    {P : ℂ → ℂ}
    (hP : ∀ w ∈ Metric.ball ((chartAt (H := ℂ) Q₀) Q₀) r,
      HasDerivAt P (formChartCoeff Q₀ α w) w)
    {z : ℂ} (hz : z ∈ Metric.ball ((chartAt (H := ℂ) Q₀) Q₀) r) :
    formChartPrimitive Q₀ α z = P z - P ((chartAt (H := ℂ) Q₀) Q₀) := by
  classical
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have hr_pos : 0 < r := Metric.nonempty_ball.mp ⟨z, hz⟩
  have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
  have hdiff : DifferentiableOn ℂ (formChartCoeff Q₀ α) (Metric.ball z₀ r) :=
    (formChartCoeff_differentiableOn Q₀ α).mono hsub
  have hseg : Set.Icc (0 : ℝ) 1
      ⊆ {t | z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r} := by
    intro t ht
    show z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r
    have h_rewrite : z₀ + (t : ℂ) * (z - z₀) = z₀ + t • (z - z₀) := by
      rw [Complex.real_smul]
    rw [h_rewrite]
    exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz ht
  have hFTC := Jacobians.OfCurveSkeleton.segmentIntegral_eq_primitive_diff
    (c := z₀) (r := r) (a := z₀) (b := z)
    (f := formChartCoeff Q₀ α) (g := P)
    hz₀_mem hz hseg hdiff.continuousOn hP
  rw [formChartPrimitive, ← hz₀_def]
  exact hFTC

/-- **The segment piece (K4).** For a chart ball at `Q₀` and a coordinate
`z` in it, there is a port-smooth path from `Q₀` to `(chartAt Q₀).symm z`
whose port line integral of every bridged form is the K2 chart primitive
`formChartPrimitive Q₀ · z` — the local Jacobi map's summand. Built from
the port's zero-velocity hop (`zeroVelHop`) and valued by the public cell
FTC (`Bridge.lineIntegral_cell_eq_primitive_sub`). -/
theorem exists_isSmoothPath_lineIntegral_eq_formChartPrimitive
    (Q₀ : X) {r : ℝ}
    (hsub : Metric.ball ((chartAt (H := ℂ) Q₀) Q₀) r ⊆ (chartAt ℂ Q₀).target)
    {z : ℂ} (hz : z ∈ Metric.ball ((chartAt (H := ℂ) Q₀) Q₀) r) :
    ∃ σ : ℝ → X,
      _root_.Jacobians.IsSmoothPath Q₀ ((chartAt ℂ Q₀).symm z) σ ∧
      ∀ α : HolomorphicOneForm X,
        _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv α) σ
          = formChartPrimitive Q₀ α z := by
  classical
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have hr_pos : 0 < r := Metric.nonempty_ball.mp ⟨z, hz⟩
  have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
  -- the endpoint downstairs.
  set Q : X := (chartAt ℂ Q₀).symm z with hQ_def
  have hz_tgt : z ∈ (chartAt ℂ Q₀).target := hsub hz
  have hQ_src : Q ∈ (chartAt ℂ Q₀).source := (chartAt ℂ Q₀).map_target hz_tgt
  have hQ_coord : (chartAt ℂ Q₀) Q = z := (chartAt ℂ Q₀).right_inv hz_tgt
  -- the affine segment in coordinates stays in the ball.
  have haff : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ Metric.ball z₀ r := by
    intro s hs
    have h_rewrite : (1 - (s : ℂ)) * z₀ + (s : ℂ) * z = z₀ + s • (z - z₀) := by
      rw [Complex.real_smul]
      ring
    rw [h_rewrite]
    exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz hs
  -- the hop is valid, giving the zero-velocity smooth path.
  have hhop : _root_.Jacobians.HopValid Q₀ Q := by
    refine ⟨hQ_src, fun s hs => ?_⟩
    rw [hQ_coord]
    exact hsub (haff s hs)
  obtain ⟨hσ_sm, _, _⟩ := _root_.Jacobians.zeroVelHop hhop
  set σ : ℝ → X := _root_.Jacobians.ChartBallPathSmooth Q₀ Q with hσ_def
  refine ⟨σ, hσ_sm, ?_⟩
  intro α
  -- the chart ball as a `PathChartBall`, with its primitive.
  set B : PathChartBall X :=
    { p := Q₀, c := z₀, r := r,
      ball_subset_target := by
        intro w hw
        simpa [extChartAt] using hsub hw } with hB_def
  -- the path stays in the cell.
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, σ t ∈ (chartAt ℂ B.p).source ∧
      (extChartAt 𝓘(ℂ) B.p) (σ t) ∈ Metric.ball B.c B.r := by
    intro t _ht
    set s : ℝ := _root_.Jacobians.smoothStep01 t with hs_def
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := _root_.Jacobians.smoothStep01_mem_unit t
    have hw : (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ Metric.ball z₀ r := haff s hs01
    have hw_tgt : (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ (chartAt ℂ Q₀).target :=
      hsub hw
    have hσt : σ t = (chartAt ℂ Q₀).symm
        ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z) := by
      show _root_.Jacobians.ChartBallPath Q₀ Q₀ Q (_root_.Jacobians.smoothStep01 t)
        = (chartAt ℂ Q₀).symm ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z)
      rw [_root_.Jacobians.ChartBallPath, ← hs_def, hQ_coord, ← hz₀_def]
    constructor
    · rw [hσt]
      exact (chartAt ℂ Q₀).map_target hw_tgt
    · rw [hσt]
      change (extChartAt 𝓘(ℂ) Q₀) ((chartAt ℂ Q₀).symm
        ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z)) ∈ Metric.ball z₀ r
      rw [show (extChartAt 𝓘(ℂ) Q₀) ((chartAt ℂ Q₀).symm
          ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z))
          = (chartAt ℂ Q₀) ((chartAt ℂ Q₀).symm
            ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z)) by simp [extChartAt],
        (chartAt ℂ Q₀).right_inv hw_tgt]
      exact hw
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (σ t)).toFun ∘ σ) t := by
    intro t ht
    exact hσ_sm.diff t (by rwa [Set.uIcc_of_le zero_le_one])
  have hint : IntervalIntegrable
      (fun t => (Jacobians.Bridge.bridgeForm α).toFun (σ t)
        (Jacobians.Vendor.Kirov.pathSpeed σ t))
      MeasureTheory.volume 0 1 :=
    _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous
      (Jacobians.Bridge.bridgeKDFormEquiv α) σ hσ_sm.velCont
  have hFTC := Jacobians.Bridge.lineIntegral_cell_eq_primitive_sub
    α B σ zero_le_one hσ_sm.cont hdiff hmem hint
  -- read off the endpoints.
  have hσ0 : σ 0 = Q₀ := hσ_sm.start
  have hσ1 : σ 1 = Q := hσ_sm.finish
  have hcoord0 : (extChartAt 𝓘(ℂ) B.p) (σ 0) = z₀ := by
    rw [hσ0]
    change (extChartAt 𝓘(ℂ) Q₀) Q₀ = z₀
    simp [hz₀_def, extChartAt]
  have hcoord1 : (extChartAt 𝓘(ℂ) B.p) (σ 1) = z := by
    rw [hσ1]
    change (extChartAt 𝓘(ℂ) Q₀) Q = z
    rw [show (extChartAt 𝓘(ℂ) Q₀) Q = (chartAt ℂ Q₀) Q by simp [extChartAt]]
    exact hQ_coord
  -- the chart-ball primitive is a primitive of the K2 coefficient.
  have hP : ∀ w ∈ Metric.ball z₀ r,
      HasDerivAt (pathChartBallPrimitive α B) (formChartCoeff Q₀ α w) w := by
    intro w hw
    have h := pathChartBallPrimitive_hasDerivAt α B w hw
    rwa [show α.coeff B.p w = formChartCoeff Q₀ α w from
      (formChartCoeff_eq_coeff Q₀ α (hsub hw)).symm] at h
  have hprim := formChartPrimitive_eq_primitive_sub Q₀ α hsub hP hz
  calc _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv α) σ
      = ∫ t in (0 : ℝ)..1, (Jacobians.Bridge.bridgeForm α).toFun (σ t)
          (Jacobians.Vendor.Kirov.pathSpeed σ t) := rfl
    _ = pathChartBallPrimitive α B ((extChartAt 𝓘(ℂ) B.p) (σ 1)) -
          pathChartBallPrimitive α B ((extChartAt 𝓘(ℂ) B.p) (σ 0)) := hFTC
    _ = pathChartBallPrimitive α B z - pathChartBallPrimitive α B z₀ := by
          rw [hcoord0, hcoord1]
    _ = formChartPrimitive Q₀ α z := hprim.symm

/-- **The loop piece (K4).** Every analytic loop at `x₀` has a port-smooth
closed-loop representative whose port line integral of every bridged form
is OUR canonical arc integral — the entry of `loopPeriodVec`. Composition
of the smooth-representative brick (#216) with the HI-0 developing-value
bridge. -/
theorem exists_isClosedSmoothLoop_lineIntegral_eq_canonicalArcIntegral
    (x₀ : X) (γ : AnalyticLoop X x₀) :
    ∃ lp : ℝ → X, _root_.Jacobians.IsClosedSmoothLoop lp ∧
      ∀ α : HolomorphicOneForm X,
        _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv α) lp
          = canonicalArcIntegral γ.arc α := by
  classical
  -- the loop as a Mathlib `Path x₀ x₀`.
  set δ : Path x₀ x₀ :=
    { toContinuousMap := analyticArcToContinuousMap γ.arc
      source' := γ.start_eq
      target' := γ.end_eq } with hδ_def
  obtain ⟨lp, hlp, _, hval⟩ :=
    Jacobians.Bridge.exists_isClosedSmoothLoop_lineIntegral_eq_developingValue
      x₀ δ
  refine ⟨lp, hlp, fun α => ?_⟩
  rw [hval α]
  have hcoe : (δ : C(unitInterval, X)) = analyticArcToContinuousMap γ.arc := rfl
  rw [hcoe]
  exact developingValue_eq_canonicalArcIntegral x₀ α γ.arc

/-! ## K5 helpers — the simple-pole residue read and port-form spanning -/

omit [Nonempty X] in
/-- **The simple-pole residue read** `Res_c (Φ·(z−c)⁻¹) = Φ(c)` for `Φ`
analytic at `c` (split off the constant term via `dslope`). Port of Kirov's
`PeriodLatticeDiscrete.lean:45` over the port's `resAt`. -/
theorem resAt_analyticAt_mul_sub_inv {Φ : ℂ → ℂ} {c : ℂ}
    (hΦ : AnalyticAt ℂ Φ c) :
    Jacobians.Dolbeault.resAt (fun w => Φ w * (w - c)⁻¹) c = Φ c := by
  obtain ⟨pser, hpser⟩ := hΦ
  have hd : AnalyticAt ℂ (dslope Φ c) c :=
    ⟨_, hpser.has_fpower_series_dslope_fslope⟩
  -- the split `Φ·(w−c)⁻¹ = Φ(c)·(w−c)⁻¹ + dslope Φ c` off `c`.
  have hgerm : (fun w => Φ w * (w - c)⁻¹) =ᶠ[nhdsWithin c {c}ᶜ]
      (fun w => Φ c * (w - c)⁻¹) + dslope Φ c := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwc : w - c ≠ 0 := sub_ne_zero.mpr hw
    have hds : (w - c) * dslope Φ c w = Φ w - Φ c := by
      have h := sub_smul_dslope Φ c w
      simpa [smul_eq_mul] using h
    show Φ w * (w - c)⁻¹ = Φ c * (w - c)⁻¹ + dslope Φ c w
    rw [show dslope Φ c w = (Φ w - Φ c) * (w - c)⁻¹ from by
      rw [eq_mul_inv_iff_mul_eq₀ hwc, mul_comm]; exact hds]
    ring
  rw [Jacobians.Dolbeault.resAt_congr hgerm]
  -- additivity + the two atomic residues.
  have h1 : Jacobians.Dolbeault.HoloPunctured (fun w => Φ c * (w - c)⁻¹) c := by
    refine ⟨1, one_pos, fun z hz => ?_⟩
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.sub_const c).inv (sub_ne_zero.mpr hz.2))
  obtain ⟨ρd, hρd, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_analyticAt ℂ (dslope Φ c)) c
      hd.eventually_analyticAt.self_of_nhds
  have h2 : Jacobians.Dolbeault.HoloPunctured (dslope Φ c) c := by
    refine ⟨ρd, hρd, fun z hz => ?_⟩
    exact (hball hz.1).differentiableAt
  rw [Jacobians.Dolbeault.resAt_add h1 h2,
    Jacobians.Dolbeault.resAt_const_mul_sub_inv,
    Jacobians.Dolbeault.resAt_eq_zero_of_differentiableOn_ball hρd
      (fun z hz => (hball hz).differentiableAt), add_zero]

omit [Nonempty X] in
/-- **The bridged basis spans the port forms.** `bridgeKDFormEquiv` is a
linear equivalence `HolomorphicOneForm X ≃ₗ Jacobians.HolomorphicOneForms X`,
so the image of OUR basis `b` is a spanning family of the port's forms. The
spanning input the engine's E1 rung (`period_eq_zero_of_spanning`) consumes. -/
theorem span_range_bridgeKD_basis
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Submodule.span ℂ
        (Set.range fun i => Jacobians.Bridge.bridgeKDFormEquiv (b i)) = ⊤ := by
  have hrange : (Set.range fun i => Jacobians.Bridge.bridgeKDFormEquiv (b i))
      = Jacobians.Bridge.bridgeKDFormEquiv.toLinearMap '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [hrange, ← LinearMap.map_span,
    show Submodule.span ℂ (Set.range b) = ⊤ from b.span_eq,
    Submodule.map_top, LinearMap.range_eq_top.mpr
      (Jacobians.Bridge.bridgeKDFormEquiv).surjective]

/-! ## K5 — the isolated zero of the loop-period lattice

Idea source: Kirov `906335f`, `Jacobians/PeriodLatticeDiscrete.lean:120-557`
(Apache 2.0), `truePeriodLattice_isolated_zero`. Re-stated over OUR
`loopPeriodLattice x₀ b` (whose generators are the `canonicalArcIntegral`
period vectors of ALL analytic loops, so NO cycle-basis axiom enters) and
OUR merged engine `exists_meromorphic_of_zeroPeriodChain'` + the port's
`residueTheorem_unconditional`.

*Argument (Forster 21.4b).* Pick `g` base points `a j` with invertible
evaluation matrix `A = jacobiEvalMatrix b a` (K1,
`exists_jacobiBasePoints_det_ne_zero`) and the local-Jacobi-map openness
window `U = jacobiMap b a '' V` around `0` (K2, `exists_jacobiMap_map_nhds`),
with `V` a polydisc of chart balls shrunk into pairwise-disjoint T2
neighbourhoods `O j ∋ a j` (`exists_pairwise_disjoint_opens`). Suppose
`0 ≠ v ∈ loopPeriodLattice ∩ U`, so `v = jacobiMap b a z`. Set
`x j := (chartAt ℂ (a j)).symm (z j) ∈ O j`; some `x j₀ ≠ a j₀`.

Build the smooth 1-chain `c` = the K4 segment pieces `a j → x j`
(`exists_isSmoothPath_lineIntegral_eq_formChartPrimitive`, summing to
`jacobiMap b a z = v`) MINUS the finite ℤ-combination of K4 loop pieces
(`exists_isClosedSmoothLoop_lineIntegral_eq_canonicalArcIntegral`) realizing
`v ∈ span ℤ (range loopPeriodVec)` (`Submodule.mem_span_set'`, contributing
`−v`). Then `c.boundary = ∑ⱼ (xⱼ − aⱼ)` and every basis period
`c.period (bridgeKDFormEquiv (b i)) = vᵢ − vᵢ = 0` vanishes. The merged
engine `exists_meromorphic_of_zeroPeriodChain'` returns meromorphic `f`
with `div f = c.boundary` and (K3) the centred Laurent normal form
`f̂ = H·(w−w₀)^n`, `H(w₀) ≠ 0`, at every point. Applying
`residueTheorem_unconditional` to each `f·(b i)`: the residue at the simple
pole `a j` is `cvec j · A i j` (the `resAt_analyticAt_mul_sub_inv` split,
K3 leading coefficient `cvec j := H_{a j}(w₀)`), residues vanish at the
`x j` (divisor coefficient `≥ 0`). Summing: `A.mulVec cvec = 0` with
`cvec ≠ 0` (leading coefficient at `a j₀` is nonzero) — contradicting
`det A ≠ 0`. Hence `v = 0`.

K-LITE CLOSED (sorry-free). The chain-assembly + residue-read core
(Kirov :229-557) is fully ported here: the chain is a port `SmoothOneChain`
(segments coeff `1` ⊕ ℤ-loop combination coeff `−fl k`); periods over all
port forms vanish by `period_eq_zero_of_spanning` against the bridged basis
(`span_range_bridgeKD_basis`); the merged engine
`exists_meromorphic_of_zeroPeriodChain'` returns `f₀` with `div f₀ = ∂c`;
off-pole analyticity is honest via the junk-repair `f₀.repair`
(`repair_read_analyticAt`, germ-equal so `div` is preserved), and the
simple-pole leading coefficient is read off K3's centred normal form
(`meromorphicFunction_normalForm_of_div`) through
`resAt_analyticAt_mul_sub_inv`. The downstream K6 packaging
(`discreteTopology_loopPeriodLattice` and the unconditional ZLattice
corollaries) is fully proven FROM this statement; the whole Kirov
dissection-free route is now sorry-free and `AX_PeriodCycleBasis`-free. -/
theorem loopPeriodLattice_isolated_zero (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    ∃ U ∈ nhds (0 : Fin (genus X) → ℂ),
      ∀ v ∈ loopPeriodLattice x₀ b, v ∈ U → v = 0 := by
  classical
  obtain ⟨a, hainj, hdet, hG0, hmap⟩ := exists_jacobiMap_map_nhds (X := X) b
  -- pairwise-disjoint opens at the base points.
  obtain ⟨O, hOopen, haO, hOdisj⟩ := exists_pairwise_disjoint_opens hainj
  -- chart-ball radii whose `symm`-images stay in `O j`.
  have hrad : ∀ j, ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt (H := ℂ) (a j)) (a j)) r
        ⊆ (chartAt (H := ℂ) (a j)) '' (O j ∩ (chartAt (H := ℂ) (a j)).source) := by
    intro j
    have hopen : IsOpen ((chartAt (H := ℂ) (a j)) ''
        (O j ∩ (chartAt (H := ℂ) (a j)).source)) :=
      (chartAt (H := ℂ) (a j)).isOpen_image_of_subset_source
        ((hOopen j).inter (chartAt (H := ℂ) (a j)).open_source) Set.inter_subset_right
    have hmem : (chartAt (H := ℂ) (a j)) (a j) ∈ (chartAt (H := ℂ) (a j)) ''
        (O j ∩ (chartAt (H := ℂ) (a j)).source) :=
      Set.mem_image_of_mem _ ⟨haO j, mem_chart_source ℂ (a j)⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen _ hmem
    exact ⟨r, hr, hsub⟩
  choose r hrpos hrsub using hrad
  -- the polydisc window and its Jacobi image.
  set V : Set (Fin (genus X) → ℂ) :=
    Set.univ.pi (fun j => Metric.ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)) with hV
  have hVnhds : V ∈ nhds (jacobiCenter a) := by
    refine set_pi_mem_nhds Set.finite_univ fun j _ => ?_
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hrpos j))
  refine ⟨jacobiMap b a '' V, hmap V hVnhds, ?_⟩
  -- the discreteness claim.
  intro t htΓ htW
  by_contra ht0
  obtain ⟨z, hzV, hzt⟩ := htW
  have hz_ball : ∀ j, z j ∈ Metric.ball ((chartAt (H := ℂ) (a j)) (a j)) (r j) :=
    fun j => hzV j (Set.mem_univ j)
  -- the ball is inside the chart target.
  have hball_tgt : ∀ j, Metric.ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)
      ⊆ (chartAt (H := ℂ) (a j)).target := by
    intro j w hw
    obtain ⟨y, hy, hyz⟩ := hrsub j hw
    rw [← hyz]
    exact (chartAt (H := ℂ) (a j)).map_source hy.2
  -- the endpoints `x j` and their geometry.
  set x : Fin (genus X) → X := fun j => (chartAt (H := ℂ) (a j)).symm (z j) with hx
  have hx_mem : ∀ j, x j ∈ O j ∩ (chartAt (H := ℂ) (a j)).source := by
    intro j
    obtain ⟨y, hy, hyz⟩ := hrsub j (hz_ball j)
    have hxy : x j = y := by
      rw [hx]
      show (chartAt (H := ℂ) (a j)).symm (z j) = y
      rw [← hyz, (chartAt (H := ℂ) (a j)).left_inv hy.2]
    rw [hxy]; exact hy
  have hchart_x : ∀ j, (chartAt (H := ℂ) (a j)) (x j) = z j :=
    fun j => (chartAt (H := ℂ) (a j)).right_inv (hball_tgt j (hz_ball j))
  have hsymm_c : ∀ j,
      (chartAt (H := ℂ) (a j)).symm ((chartAt (H := ℂ) (a j)) (a j)) = a j :=
    fun j => (chartAt (H := ℂ) (a j)).left_inv (mem_chart_source ℂ (a j))
  -- nondegeneracy: some coordinate moved.
  have hzc : z ≠ jacobiCenter a := by
    intro h; rw [h, hG0] at hzt; exact ht0 hzt.symm
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hzc
  have hxa : ∀ j, z j ≠ jacobiCenter a j → x j ≠ a j := by
    intro j hzj h; refine hzj ?_; rw [← hchart_x j, h]; rfl
  -- the segment paths `a j → x j` (K4 brick).
  have hseg : ∀ j, ∃ σ : ℝ → X,
      _root_.Jacobians.IsSmoothPath (a j) (x j) σ ∧
      ∀ α : HolomorphicOneForm X,
        _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv α) σ
          = formChartPrimitive (a j) α (z j) := by
    intro j
    have hsub : Metric.ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)
        ⊆ (chartAt ℂ (a j)).target := hball_tgt j
    obtain ⟨σ, hσsp, hσval⟩ :=
      exists_isSmoothPath_lineIntegral_eq_formChartPrimitive (a j) hsub (hz_ball j)
    refine ⟨σ, ?_, hσval⟩
    -- the brick's endpoint is `(chartAt ℂ (a j)).symm (z j) = x j`.
    have : (chartAt ℂ (a j)).symm (z j) = x j := rfl
    rwa [this] at hσsp
  choose seg hsegsp hsegval using hseg
  -- the lattice combination realizing `t`.
  rw [loopPeriodLattice, Submodule.mem_span_set'] at htΓ
  obtain ⟨nl, fl, gl, hsum⟩ := htΓ
  -- each generator is a loop's period vector; get K4 loop reps whose period
  -- of every basis form is the `i`-th coordinate of the generator.
  have hloop : ∀ k : Fin nl, ∃ lp : ℝ → X,
      _root_.Jacobians.IsClosedSmoothLoop lp ∧
      ∀ i : Fin (genus X),
        _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv (b i)) lp
          = (gl k : Fin (genus X) → ℂ) i := by
    intro k
    obtain ⟨γ, hγ⟩ := (gl k).2
    obtain ⟨lp, hlpc, hlpval⟩ :=
      exists_isClosedSmoothLoop_lineIntegral_eq_canonicalArcIntegral x₀ γ
    refine ⟨lp, hlpc, fun i => ?_⟩
    rw [hlpval (b i)]
    rw [show canonicalArcIntegral γ.arc (b i) = loopPeriodVec x₀ b γ i from rfl, hγ]
  choose lp hlpc hlpval using hloop
  -- each loop, viewed as a smooth path from its basepoint to itself.
  have hlpsp : ∀ k, _root_.Jacobians.IsSmoothPath (lp k 0) (lp k 0) (lp k) :=
    fun k =>
      { start := rfl
        finish := ((hlpc k).closed).symm
        cont := (hlpc k).cont
        diff := (hlpc k).diff
        velCont := (hlpc k).velCont }
  -- THE CHAIN: segments `a j → x j` (coeff 1) ⊕ loops (coeff `−fl k`).
  set c : Jacobians.Dolbeault.SmoothOneChain X :=
    { n := genus X + nl
      coeff := Fin.addCases (fun _ => (1 : ℤ)) (fun k => -(fl k))
      src := Fin.addCases a (fun k => lp k 0)
      tgt := Fin.addCases x (fun k => lp k 0)
      path := Fin.addCases seg lp
      smooth := by
        intro i
        refine Fin.addCases ?_ ?_ i
        · intro j; rw [Fin.addCases_left, Fin.addCases_left, Fin.addCases_left]
          exact hsegsp j
        · intro k; rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right]
          exact hlpsp k } with hc
  -- the boundary is `∑ⱼ (xⱼ − aⱼ)` (loops contribute 0).
  have hbd : c.boundary
      = ∑ j, (Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1) := by
    rw [hc, Jacobians.Dolbeault.SmoothOneChain.boundary]
    show (∑ m : Fin (genus X + nl), _) = _
    rw [Fin.sum_univ_add]
    have hL : ∀ j : Fin (genus X),
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => (1 : ℤ)) (fun k => -(fl k))
            (Fin.castAdd nl j)) •
          (Finsupp.single ((Fin.addCases (motive := fun _ => X) x (fun k => lp k 0)
              (Fin.castAdd nl j))) (1 : ℤ)
            - Finsupp.single ((Fin.addCases (motive := fun _ => X) a (fun k => lp k 0)
              (Fin.castAdd nl j))) 1)
        = Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1 := by
      intro j
      rw [Fin.addCases_left, Fin.addCases_left, Fin.addCases_left, one_smul]
    have hR : ∀ k : Fin nl,
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => (1 : ℤ)) (fun k => -(fl k))
            (Fin.natAdd (genus X) k)) •
          (Finsupp.single ((Fin.addCases (motive := fun _ => X) x (fun k => lp k 0)
              (Fin.natAdd (genus X) k))) (1 : ℤ)
            - Finsupp.single ((Fin.addCases (motive := fun _ => X) a (fun k => lp k 0)
              (Fin.natAdd (genus X) k))) 1)
        = 0 := by
      intro k
      rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, sub_self,
        smul_zero]
    rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_congr rfl fun k _ => hR k,
      Finset.sum_const_zero, add_zero]
  -- the chain has vanishing basis periods: `vᵢ − vᵢ = 0`.
  have hper_basis : ∀ i : Fin (genus X),
      c.period (Jacobians.Bridge.bridgeKDFormEquiv (b i)) = 0 := by
    intro i
    rw [hc, Jacobians.Dolbeault.SmoothOneChain.period]
    show (∑ m : Fin (genus X + nl), _) = 0
    rw [Fin.sum_univ_add]
    have hL : ∀ j : Fin (genus X),
        ((Fin.addCases (motive := fun _ => ℤ) (fun _ => (1 : ℤ)) (fun k => -(fl k))
            (Fin.castAdd nl j) : ℤ) : ℂ) *
          _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv (b i))
            (Fin.addCases (motive := fun _ => ℝ → X) seg lp (Fin.castAdd nl j))
        = formChartPrimitive (a j) (b i) (z j) := by
      intro j
      rw [Fin.addCases_left, Fin.addCases_left, Int.cast_one, one_mul]
      exact hsegval j (b i)
    have hR : ∀ k : Fin nl,
        ((Fin.addCases (motive := fun _ => ℤ) (fun _ => (1 : ℤ)) (fun k => -(fl k))
            (Fin.natAdd (genus X) k) : ℤ) : ℂ) *
          _root_.Jacobians.lineIntegral (Jacobians.Bridge.bridgeKDFormEquiv (b i))
            (Fin.addCases (motive := fun _ => ℝ → X) seg lp (Fin.natAdd (genus X) k))
        = -(fl k : ℂ) * (gl k : Fin (genus X) → ℂ) i := by
      intro k
      rw [Fin.addCases_right, Fin.addCases_right, hlpval k i]
      push_cast; ring
    rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_congr rfl fun k _ => hR k]
    -- `∑ⱼ Φ̃ⱼ(z j) = jacobiMap b a z i = t i`; the loop part is `−t i`.
    have hjac : (∑ j, formChartPrimitive (a j) (b i) (z j)) = t i := by
      rw [show (∑ j, formChartPrimitive (a j) (b i) (z j)) = jacobiMap b a z i from rfl,
        hzt]
    have hloopsum : (∑ k, (fl k : ℂ) * (gl k : Fin (genus X) → ℂ) i) = t i := by
      have hc2 : (∑ k, fl k • (gl k : Fin (genus X) → ℂ)) i = t i := congrFun hsum i
      simp only [Finset.sum_apply, zsmul_eq_mul] at hc2
      exact hc2
    rw [hjac]
    rw [show (∑ k, -(fl k : ℂ) * (gl k : Fin (genus X) → ℂ) i)
        = -∑ k, (fl k : ℂ) * (gl k : Fin (genus X) → ℂ) i from by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring]
    rw [hloopsum]; ring
  -- extend to ALL port forms via the spanning bridged basis (engine E1).
  have hper : ∀ α : Jacobians.HolomorphicOneForms X, c.period α = 0 :=
    c.period_eq_zero_of_spanning
      (fun i => Jacobians.Bridge.bridgeKDFormEquiv (b i))
      (span_range_bridgeKD_basis b) hper_basis
  -- THE ENGINE: a meromorphic `f₀` with `div f₀ = c.boundary = D`.
  obtain ⟨f₀, hdiv⟩ :=
    Jacobians.Dolbeault.exists_meromorphic_of_zeroPeriodChain'
      Jacobians.Dolbeault.chartDiskCover c hper
  rw [hbd] at hdiv
  set D : _root_.Jacobians.Divisor X :=
    ∑ j, (Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1) with hD
  -- pass to the honest junk-repair `f` (germ-equal; analytic off poles).
  set f : _root_.Jacobians.MeromorphicFunction X := f₀.repair with hf
  have hdivf : _root_.Jacobians.MeromorphicFunction.div X f = D := by
    rw [← hdiv]
    refine Finsupp.ext (fun y => ?_)
    rw [meromorphicFunction_div_apply, meromorphicFunction_div_apply]
    refine congrArg WithTop.untop₀ (meromorphicOrderAt_congr ?_)
    exact f₀.holoRepr_read_eventuallyEq y
  -- divisor coefficient bookkeeping (Kirov PeriodLatticeDiscrete:401-468).
  have hD_apply : ∀ y : X, D y = ∑ j, ((if x j = y then (1 : ℤ) else 0)
      - (if a j = y then 1 else 0)) := by
    intro y
    rw [hD, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have hxO : ∀ j, x j ∈ O j := fun j => (hx_mem j).1
  have hxa_ne : ∀ j k, j ≠ k → x j ≠ a k := by
    intro j k hjk h; exact (hOdisj j k hjk).ne_of_mem (hxO j) (haO k) h
  have hane : ∀ j k, j ≠ k → a j ≠ a k := fun j k hjk h => hjk (hainj h)
  have hD_a : ∀ j, x j ≠ a j → D (a j) = -1 := by
    intro j hxj
    rw [hD_apply, Finset.sum_eq_single j]
    · rw [if_neg hxj, if_pos rfl]; norm_num
    · intro k _ hkj
      rw [if_neg (fun h => hxa_ne k j hkj h), if_neg (fun h => hane k j hkj h)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  -- the residue (leading-coefficient) vector.
  set cvec : Fin (genus X) → ℂ := fun j =>
    if hj : x j = a j then 0
    else (meromorphicFunction_normalForm_of_div f (a j)
      (n := -1) (by rw [hdivf]; exact hD_a j hj) (by norm_num)).choose
        ((chartAt (H := ℂ) (a j)) (a j))
    with hcvec
  set poles : Finset X := Finset.univ.image a ∪ Finset.univ.image x with hpoles
  -- `D` vanishes off the poles.
  have hD_off : ∀ y : X, y ∉ poles → D y = 0 := by
    intro y hy
    rw [hD_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hyx : x j ≠ y := fun h => hy (by
      rw [hpoles]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩))
    have hya : a j ≠ y := fun h => hy (by
      rw [hpoles]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩))
    rw [if_neg hyx, if_neg hya]; ring
  -- `orderAtPoint f₀ y = D y` for every `y` (`div f₀ = D`).
  have horder : ∀ y : X, f₀.orderAtPoint y = D y := by
    intro y
    show (meromorphicOrderAt (f₀.toFun ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y)).untop₀ = D y
    rw [← meromorphicFunction_div_apply f₀ y]
    exact congrFun (congrArg _ hdiv) y
  -- analyticity of the repaired read wherever `D y ≥ 0` (`f.toFun = f₀.repair.toFun`).
  have hgood' : ∀ y : X, 0 ≤ D y →
      AnalyticAt ℂ (fun z => f.toFun ((chartAt (H := ℂ) y).symm z))
        ((chartAt (H := ℂ) y) y) := by
    intro y hDy
    exact f₀.repair_read_analyticAt (by rw [horder y]; exact hDy)
  have hgood : ∀ y : X, y ∉ poles →
      AnalyticAt ℂ (fun z => f.toFun ((chartAt (H := ℂ) y).symm z))
        ((chartAt (H := ℂ) y) y) :=
    fun y hy => hgood' y (le_of_eq (hD_off y hy).symm)
  -- THE RESIDUE THEOREM on each `(bridgeKD (b i))·f`.
  have hres : ∀ i : Fin (genus X),
      ∑ y ∈ poles, Jacobians.Dolbeault.formFnResidue
        (Jacobians.Bridge.bridgeKDFormEquiv (b i)) f.toFun y = 0 := by
    intro i
    exact Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_unconditional
      (Jacobians.Bridge.bridgeKDFormEquiv (b i)) f poles hgood
  -- the residue at `a j` is `cvec j · A i j`.
  have hres_a : ∀ (i j : Fin (genus X)),
      Jacobians.Dolbeault.formFnResidue
          (Jacobians.Bridge.bridgeKDFormEquiv (b i)) f.toFun (a j)
        = cvec j * jacobiEvalMatrix b a i j := by
    intro i j
    by_cases hxj : x j = a j
    · -- no pole: `D (a j) = 0`, analytic read, residue `0`.
      have hDaj : D (a j) = 0 := by
        rw [hD_apply, Finset.sum_eq_single j]
        · rw [if_pos hxj, if_pos rfl]; norm_num
        · intro k _ hkj
          rw [if_neg (fun h => hxa_ne k j hkj h), if_neg (fun h => hane k j hkj h)]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [show cvec j = 0 from by rw [hcvec]; exact dif_pos hxj, zero_mul]
      exact Jacobians.Dolbeault.formFnResidue_eq_zero_of_analyticAt _ _ _
        (hgood' (a j) (le_of_eq hDaj.symm))
    · -- simple pole: residue `H(w₀)·coeffAt-centre = cvec j · A i j`.
      have hDaj : D (a j) = -1 := hD_a j hxj
      -- name the K3 normal-form witness so it matches `cvec`.
      set spec := meromorphicFunction_normalForm_of_div f (a j) (n := -1)
        (by rw [hdivf]; exact hDaj) (by norm_num) with hspec
      set H : ℂ → ℂ := spec.choose with hHdef
      obtain ⟨hH_ana, hH_ne, hH_ev⟩ := spec.choose_spec
      rw [Jacobians.Dolbeault.formFnResidue]
      -- the integrand is `Φ·(w−w₀)⁻¹` with `Φ = coeffAt·H` analytic.
      have hint_germ : (fun w => Jacobians.Dolbeault.coeffAt
              (Jacobians.Bridge.bridgeKDFormEquiv (b i)) (a j) w
            * f.toFun ((chartAt ℂ (a j)).symm w))
          =ᶠ[nhdsWithin ((chartAt (H := ℂ) (a j)) (a j))
              {(chartAt (H := ℂ) (a j)) (a j)}ᶜ]
          fun w => (Jacobians.Dolbeault.coeffAt
              (Jacobians.Bridge.bridgeKDFormEquiv (b i)) (a j) w * H w)
            * (w - (chartAt (H := ℂ) (a j)) (a j))⁻¹ := by
        filter_upwards [hH_ev] with w hw
        rw [hw, zpow_neg_one]; ring
      have hΦ : AnalyticAt ℂ (fun w => Jacobians.Dolbeault.coeffAt
            (Jacobians.Bridge.bridgeKDFormEquiv (b i)) (a j) w * H w)
          ((chartAt (H := ℂ) (a j)) (a j)) :=
        (Jacobians.Dolbeault.coeffAt_analyticAt (Jacobians.Bridge.bridgeKDFormEquiv (b i))
          (a j) ((chartAt ℂ (a j)).map_source (mem_chart_source ℂ (a j)))).mul hH_ana
      rw [Jacobians.Dolbeault.resAt_congr hint_germ, resAt_analyticAt_mul_sub_inv hΦ]
      rw [Jacobians.Dolbeault.coeffAt_chartCenter]
      rw [show cvec j = H ((chartAt (H := ℂ) (a j)) (a j)) from by
        show (if hj : x j = a j then 0
          else (meromorphicFunction_normalForm_of_div f (a j) (n := -1)
            (by rw [hdivf]; exact hD_a j hj) (by norm_num)).choose
              ((chartAt (H := ℂ) (a j)) (a j))) = H ((chartAt (H := ℂ) (a j)) (a j))
        rw [dif_neg hxj]]
      rw [jacobiEvalMatrix_apply, formEvalSelf_apply]
      ring
  -- residues vanish at the `x j` (those not equal to some `a k`).
  have hres_x : ∀ (i : Fin (genus X)) (y : X), y ∈ poles →
      y ∉ Finset.univ.image a →
      Jacobians.Dolbeault.formFnResidue
        (Jacobians.Bridge.bridgeKDFormEquiv (b i)) f.toFun y = 0 := by
    intro i y hy hya
    have hDy : 0 ≤ D y := by
      rw [hD_apply]
      refine Finset.sum_nonneg fun j _ => ?_
      have hyaj : a j ≠ y :=
        fun h => hya (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩)
      rw [if_neg hyaj]
      by_cases h : x j = y <;> simp [h]
    exact Jacobians.Dolbeault.formFnResidue_eq_zero_of_analyticAt _ _ _
      (hgood' y hDy)
  -- assemble: `A.mulVec cvec = 0`.
  have hmul : ∀ i : Fin (genus X),
      ∑ j, jacobiEvalMatrix b a i j * cvec j = 0 := by
    intro i
    have h := hres i
    rw [hpoles, Finset.sum_union_eq_left
      (fun y hy hyn => hres_x i y
        (by rw [hpoles]; exact Finset.mem_union_right _ hy) hyn)] at h
    rw [Finset.sum_image (fun j _ k _ h => hainj h)] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hres_a i j]; ring
  -- `cvec ≠ 0`: at `j₀` (where `x j₀ ≠ a j₀`) the leading coefficient is nonzero.
  have hcvec0 : cvec ≠ 0 := by
    intro h
    have hjval : cvec j₀ = 0 := by rw [h]; rfl
    simp only [hcvec, dif_neg (hxa j₀ hj₀)] at hjval
    exact (meromorphicFunction_normalForm_of_div f (a j₀) (n := -1)
      (by rw [hdivf]; exact hD_a j₀ (hxa j₀ hj₀)) (by norm_num)).choose_spec.2.1 hjval
  -- contradiction with `det A ≠ 0`.
  refine hdet ?_
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨cvec, hcvec0, ?_⟩
  funext i
  rw [Matrix.mulVec, dotProduct]
  exact hmul i

/-! ## K6 — `DiscreteTopology (loopPeriodLattice x₀ b)` and the unconditional
packaging

Idea source: Kirov `906335f`, `Jacobians/PeriodLatticeBasis.lean:38-53`
(Apache 2.0). The isolated-zero window (K5) is open after pulling back along
`Subtype.val`, so the singleton `{0}` is open in the subtype — which is the
`discreteTopology_iff_isOpen_singleton_zero` criterion. With discreteness
PROVEN (not hypothesised), OUR axiom-free B-3 spanning
(`span_real_loopPeriodLattice_eq_top`) upgrades the lattice to a full
ℤ-lattice and the #208 image-route corollaries (`finrank = 2g`, ℤ-basis)
become UNCONDITIONAL. -/

/-- **K6 (E): TR-DISC, UNCONDITIONAL.** The loop-period lattice in `ℂ^g` is
discrete — no `AX_PeriodCycleBasis`, no `PeriodGeneratingLoops` hypothesis.
The whole Kirov dissection-free route (K1–K5) collapses to the isolated-zero
window, which makes `{0}` open in the subtype. -/
theorem discreteTopology_loopPeriodLattice (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (loopPeriodLattice x₀ b) := by
  obtain ⟨U, hU, hU0⟩ := loopPeriodLattice_isolated_zero x₀ b
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hU
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hset : ({0} : Set (loopPeriodLattice x₀ b))
      = (Subtype.val : loopPeriodLattice x₀ b → (Fin (genus X) → ℂ)) ⁻¹' V := by
    ext ⟨v, hv⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h0
      rw [show v = 0 from congrArg Subtype.val h0]
      exact hV0
    · intro hvV
      exact Subtype.ext (hU0 v hv (hVsub hvV))
  rw [hset]
  exact hVopen.preimage continuous_subtype_val

/-- **K6 (E): TR-DISC as a global instance.** Registering the
unconditional discreteness so the #208 image-route theorems
(`finrank_loopPeriodLattice`, `exists_loopPeriodLattice_basis`,
`isZLattice_loopPeriodLattice`), and the `IsZLattice` class itself — which
carries a `[DiscreteTopology L]` field — fire without a hypothesis. -/
instance instDiscreteTopology_loopPeriodLattice (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (loopPeriodLattice x₀ b) :=
  discreteTopology_loopPeriodLattice x₀ b

/-- **K6 (E): the loop-period lattice is a full ℤ-lattice, UNCONDITIONAL.**
Discreteness (K6, now a global instance) + the axiom-free B-3 spanning. -/
theorem isZLattice_loopPeriodLattice_unconditional (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (loopPeriodLattice x₀ b) :=
  isZLattice_loopPeriodLattice x₀ b

/-- **K6 (E): ℤ-rank `2g`, UNCONDITIONAL.** -/
theorem finrank_loopPeriodLattice_unconditional (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Module.finrank ℤ (loopPeriodLattice x₀ b) = 2 * genus X :=
  finrank_loopPeriodLattice x₀ b

/-- **K6 (E): a `Fin (2g)`-indexed ℤ-basis, UNCONDITIONAL.** -/
theorem exists_loopPeriodLattice_basis_unconditional (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ (loopPeriodLattice x₀ b)) :=
  exists_loopPeriodLattice_basis x₀ b

end Jacobians.RiemannSurface
