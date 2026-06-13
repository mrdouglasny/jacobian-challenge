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

end Jacobians.RiemannSurface
