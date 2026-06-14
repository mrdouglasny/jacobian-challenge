/-
Submission for the lean-eval problem `jacobian_challenge_diffgeo`
(Kevin Buzzard's Jacobian challenge), from `mrdouglasny/jacobian-challenge`.

Every challenge declaration delegates to the proven development, which is
vendored under `Submission/` (module paths renamed to `Submission.*`;
declaration namespaces unchanged, so `_root_.genus` etc. still resolve). All 24
obligations are sorry-free; the Buzzard property theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/
import Submission.Jacobians.Challenge

open scoped ContDiff

namespace Submission

namespace JacobianChallenge

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

noncomputable def genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  _root_.genus X

theorem genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  _root_.genus_eq_zero_iff_homeo

noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u :=
  _root_.Jacobian X

namespace Jacobian

noncomputable instance instAddCommGroup : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (_root_.Jacobian X))

noncomputable instance instTopologicalSpace : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (_root_.Jacobian X))

instance instT2Space : T2Space (Jacobian X) :=
  inferInstanceAs (T2Space (_root_.Jacobian X))

instance instCompactSpace : CompactSpace (Jacobian X) :=
  inferInstanceAs (CompactSpace (_root_.Jacobian X))

noncomputable instance instChartedSpace : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  inferInstanceAs (ChartedSpace (Fin (_root_.genus X) → ℂ) (_root_.Jacobian X))

instance instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

instance instLieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

noncomputable def ofCurve (P : X) : X → Jacobian X := _root_.Jacobian.ofCurve P

theorem ofCurve_contMDiff (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) :=
  _root_.Jacobian.ofCurve_contMDiff P

theorem ofCurve_self (P : X) : ofCurve P P = 0 := _root_.Jacobian.ofCurve_self P

theorem ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  _root_.Jacobian.ofCurve_inj P h

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  _root_.Jacobian.pushforward f hf

theorem pushforward_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  _root_.Jacobian.pushforward_contMDiff f hf

theorem pushforward_id_apply (P : Jacobian X) :
    pushforward id contMDiff_id P = P :=
  _root_.Jacobian.pushforward_id_apply P

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

theorem pushforward_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  apply _root_.Jacobian.pushforward_comp_apply

noncomputable def pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  _root_.Jacobian.pullback f hf

theorem pullback_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  _root_.Jacobian.pullback_contMDiff f hf

theorem pullback_id_apply (P : Jacobian X) :
    pullback id contMDiff_id P = P :=
  _root_.Jacobian.pullback_id_apply P

theorem pullback_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  apply _root_.Jacobian.pullback_comp_apply

open Classical in
/-- The challenge's `degree` hole binds only `[TopologicalSpace _]` and
`[ChartedSpace ℂ _]` (its signature instances), so the shim takes exactly those
binders; the honest `ContMDiff.degree` additionally needs `T2`/`Compact`/
`Connected`/`IsManifold`, which we recover with a decidable guard (always true
on a Riemann surface). -/
noncomputable def degree {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ :=
  if h : T2Space X ∧ CompactSpace X ∧ ConnectedSpace X
        ∧ IsManifold (modelWithCornersSelf ℂ ℂ) ω X
        ∧ T2Space Y ∧ CompactSpace Y ∧ ConnectedSpace Y
        ∧ IsManifold (modelWithCornersSelf ℂ ℂ) ω Y then
    @_root_.ContMDiff.degree X _ h.1 h.2.1 h.2.2.1 _ h.2.2.2.1
      Y _ h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 _ h.2.2.2.2.2.2.2 f hf
  else 0

theorem pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (degree f hf) • P := by
  have hd : degree f hf = _root_.ContMDiff.degree f hf := by
    rw [degree, dif_pos ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance⟩]
  rw [hd]
  apply _root_.Jacobian.pushforward_pullback

end Jacobian

end JacobianChallenge

end Submission
