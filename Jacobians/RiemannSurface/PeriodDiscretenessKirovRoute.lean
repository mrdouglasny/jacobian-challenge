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
import KirovDolbeault.Dolbeault.FormCoeff
import KirovDolbeault.OfCurveAnalyticitySkeleton
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

end Jacobians.RiemannSurface
